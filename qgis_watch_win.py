#!/usr/bin/env python3
"""
qgis-watch: a live terminal view of what QGIS is streaming and downloading.
Runs on macOS and Windows (Linux works too).

Panels
  1 Throughput    network rate in and out, with history
  2 Processes     QGIS, qgis_process, GDAL/OGR tools, curl/wget/aws, and anything QGIS spawned
  3 Connections   every open socket, labeled by service (LANDFIRE, AWS S3, Earth Search, ...)
  4 Open files    rasters, GeoPackages and other geodata QGIS has open, with write rates
  5 Downloads     recent geodata in your Downloads folder (and any --watch folders)
  6 Events        connections opening and closing, processes starting and exiting,
                  downloads finishing

Requirements
  macOS    The built-in python3 (3.9 or newer). Uses ps, lsof and nettop, which ship
           with macOS. Nothing to install and no sudo needed.
  Windows  Python 3.9 or newer from python.org, plus two packages:
               py -m pip install psutil windows-curses
           No admin rights needed. Windows does not keep network counts per app, so
           the throughput graph shows the whole machine's network traffic, and the
           process table shows each process's combined disk and network I/O.
  Linux    python3 with psutil (python3 -m pip install psutil).

Usage (on Windows type py instead of python3)
  python3 qgis_watch.py                          watch live
  python3 qgis_watch.py --demo                   preview the interface with simulated activity
  python3 qgis_watch.py --once                   print one plain-text snapshot and exit
  python3 qgis_watch.py --host my-bucket.s3.us-west-2.amazonaws.com=Fireplans --watch ~/fireplans
  python3 qgis_watch.py --log ~/qgis-watch.log   also append events to a log file

Keys
  1-6 zoom into a panel, 0 or Esc to see them all again
  up/down and PgUp/PgDn scroll a zoomed panel
  p pause    + and - change the refresh rate    n show raw IPs instead of hostnames
  c clear events    q quit
"""
from __future__ import annotations

import argparse
import collections
import glob
import ipaddress
import locale
import os
import plistlib
import queue
import random
import re
import shutil
import socket
import subprocess
import sys
import threading
import time

try:
    import curses
except ImportError:  # Windows needs the windows-curses package for the full-screen view
    curses = None

try:
    import psutil
except ImportError:  # required on Windows and Linux, optional on macOS
    psutil = None

VERSION = "1.1.0"
HOME = os.path.expanduser("~")
IS_WIN = sys.platform == "win32"
IS_MAC = sys.platform == "darwin"

# Hostnames resolved up front so their IP addresses can be labeled even when
# reverse DNS only returns a CDN name. Add your own with --host.
KNOWN_HOSTS = {
    "lfps.usgs.gov": "LANDFIRE",
    "www.landfire.gov": "LANDFIRE",
    "earth-search.aws.element84.com": "Earth Search STAC",
    "sentinel-cogs.s3.us-west-2.amazonaws.com": "Sentinel-2 COGs",
    "usgs-landsat.s3.us-west-2.amazonaws.com": "Landsat COGs",
    "planetarycomputer.microsoft.com": "Planetary Computer",
    "landsateuwest.blob.core.windows.net": "Planetary Computer",
    "sentinel2l2a01.blob.core.windows.net": "Planetary Computer",
    "tile.openstreetmap.org": "OSM tiles",
    "plugins.qgis.org": "QGIS plugins",
    "feed.qgis.org": "QGIS news feed",
    "version.qgis.org": "QGIS version check",
}

# Reverse DNS name patterns, checked in order when an IP is not a known host.
HOST_RULES = [
    (r"lfps\.usgs\.gov$|landfire", "LANDFIRE"),
    (r"element84|earth-search", "Earth Search STAC"),
    (r"(^|[.-])s3([.-][a-z0-9-]+)*\.amazonaws\.com$", "AWS S3"),
    (r"amazonaws\.com$", "AWS"),
    (r"cloudfront\.net$", "CloudFront CDN"),
    (r"planetarycomputer|blob\.core\.windows\.net$", "Planetary Computer"),
    (r"usgs\.gov$", "USGS"),
    (r"openstreetmap\.org$", "OSM tiles"),
    (r"qgis\.org$", "QGIS.org"),
    (r"arcgis(online)?\.com$|esri\.com$", "Esri ArcGIS"),
    (r"1e100\.net$|google", "Google"),
    (r"akamai", "Akamai CDN"),
    (r"fastly", "Fastly CDN"),
    (r"github", "GitHub"),
]

GEO_EXT = {
    ".tif", ".tiff", ".vrt", ".gpkg", ".geojson", ".shp", ".zip", ".nc", ".jp2", ".img",
    ".hdf", ".h5", ".mbtiles", ".las", ".laz", ".kml", ".kmz", ".qgz", ".qgs", ".ovr",
    ".fgb", ".parquet", ".asc", ".dem",
}
OPEN_FILE_EXT = GEO_EXT | {".xml", ".sqlite", ".json", ".csv", ".gpkg-wal"}
PARTIAL_EXT = {".part", ".crdownload", ".download", ".partial"}
DOWNLOAD_TOOLS = {"curl", "wget", "aws", "aria2c", "rclone", "s5cmd", "gsutil", "azcopy"}
APP_RE = re.compile(r"^.*?\.app/Contents/MacOS/(QGIS|qgis)(\s|$)")
APP_PROC_RE = re.compile(r"^.*?\.app/Contents/MacOS/(bin/)?qgis_process", re.I)
# Executable names: qgis-bin.exe and qgis-ltr-bin.exe on Windows, qgis on Linux.
QGIS_NAME_RE = re.compile(r"^qgis(-ltr|-qt6|-dev|-nightly)?(-bin)?(-g7)?$")
QGIS_PROC_NAME_RE = re.compile(r"^qgis_process(-qgis[\w-]*)?$")

SECTIONS = ["Throughput", "Processes", "Connections", "Open files", "Downloads", "Events"]
WEIGHTS = [0, 2, 4, 2, 2, 3]

BARS = " ▁▂▃▄▅▆▇█"
ELLIPSIS = "…"
ARROW_IN, ARROW_OUT = "↓", "↑"


# ---------------------------------------------------------------- formatting

def human_bytes(n):
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1024 or unit == "TB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024.0
    return f"{n:.1f} TB"


def human_rate(n):
    if not n:
        return "-"
    return human_bytes(n) + "/s"


def ago(seconds):
    s = max(0, int(seconds))
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m{s % 60:02d}s" if s < 600 else f"{s // 60}m"
    if s < 86400:
        return f"{s // 3600}h{(s % 3600) // 60:02d}m"
    return f"{s // 86400}d{(s % 86400) // 3600}h"


def squeeze(text, width):
    """Shorten text to width by cutting out the middle."""
    if width <= 0:
        return ""
    if len(text) <= width:
        return text
    if width < 6:
        return text[:width]
    keep = width - 1
    return text[: keep // 2] + ELLIPSIS + text[-(keep - keep // 2):]


def tilde(path):
    if IS_WIN:
        return "~" + path[len(HOME):] if path.lower().startswith(HOME.lower()) else path
    return "~" + path[len(HOME):] if path.startswith(HOME) else path


def split_exe(args):
    """Split a command line into the program path and the rest."""
    text = args.strip()
    if text.startswith('"'):
        exe, _, rest = text[1:].partition('"')
        return exe, rest
    exe, sep, rest = text.partition(" ")
    return exe, sep + rest


def short_cmd(args):
    m = re.match(r"^(.*?\.app)/Contents/MacOS/(\S+)(.*)$", args)
    if m:
        return os.path.basename(m.group(1)) + " " + m.group(2) + m.group(3)
    exe, rest = split_exe(args)
    if "\\" in exe:
        # C:\Program Files\QGIS 3.40.4\bin\qgis-bin.exe -> QGIS 3.40.4 qgis-bin.exe
        parts = [p for p in re.split(r"[\\/]", exe) if p]
        for part in parts[:-1]:
            if part.lower().startswith(("qgis", "osgeo4w")):
                return f"{part} {parts[-1]}{rest}"
        if exe.lower().startswith(HOME.lower()):
            return tilde(exe) + rest
        return parts[-1] + rest if len(parts) > 1 else exe + rest
    return tilde(args)


def spark(values, width):
    vals = list(values)[-width:] if width > 0 else []
    if not vals:
        return ""
    top = max(vals) or 1.0
    steps = len(BARS) - 1
    out = []
    for v in vals:
        out.append(BARS[0] if v <= 0 else BARS[max(1, min(steps, int(round(v / top * steps))))])
    return "".join(out)


def run(cmd, timeout=10):
    try:
        res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                             text=True, timeout=timeout)
        return res.stdout
    except (OSError, subprocess.TimeoutExpired):
        return None


def is_local(ip):
    try:
        addr = ipaddress.ip_address(ip.split("%")[0])
    except ValueError:
        return False
    return addr.is_private or addr.is_loopback or addr.is_link_local


def split_hostport(text):
    text = text.strip()
    if text.startswith("["):
        host, _, port = text[1:].partition("]:")
    else:
        host, _, port = text.rpartition(":")
    return host, port


def etime(seconds):
    s = int(seconds)
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    if d:
        return f"{d}-{h:02d}:{m:02d}:{s:02d}"
    if h:
        return f"{h:02d}:{m:02d}:{s:02d}"
    return f"{m:02d}:{s:02d}"


# ---------------------------------------------------------------- shared state

class State:
    """Everything the screen shows. Collectors write, the UI reads a snapshot."""

    def __init__(self, interval, log_path=None):
        self.lock = threading.Lock()
        self.interval = interval
        self.paused = False
        self.procs = []
        self.conns = []
        self.files = []
        self.downloads = []
        self.proc_rates = {}
        self.rate_in = 0.0
        self.rate_out = 0.0
        self.hist_in = collections.deque(maxlen=300)
        self.hist_out = collections.deque(maxlen=300)
        self.total_in = 0
        self.total_out = 0
        self.rate_source = "starting"
        self.cache = None
        self.events = collections.deque(maxlen=1000)
        self.notes = {}
        self.app_version = ""
        self.proc_io = "net"   # "net" on macOS (per-app network), "io" with psutil (disk + network)
        self.io_read = 0.0
        self.io_write = 0.0
        self.watch_pids = set()
        self._seen_procs = None
        self._seen_conns = None
        self._first_seen = {}
        self._log = None
        if log_path:
            try:
                self._log = open(os.path.expanduser(log_path), "a", buffering=1)
                self._log.write(f"--- qgis-watch {VERSION} started {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            except OSError as exc:
                self.notes["log"] = f"log file: {exc.strerror}"

    def _event(self, kind, text):
        now = time.time()
        self.events.appendleft((now, kind, text))
        if self._log:
            try:
                self._log.write(f"{time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(now))}  {kind:<6} {text}\n")
            except OSError:
                pass

    def event(self, kind, text):
        with self.lock:
            self._event(kind, text)

    def note(self, key, text):
        with self.lock:
            if text:
                self.notes[key] = text
            else:
                self.notes.pop(key, None)

    def commit_procs(self, procs, version=""):
        with self.lock:
            new = {p["pid"]: p for p in procs}
            old = self._seen_procs
            if old is None:
                if procs:
                    self._event("info", f"watching {len(procs)} QGIS-related process(es)")
                else:
                    self._event("info", "QGIS is not running yet, waiting for it to start")
            else:
                for pid in sorted(new.keys() - old.keys()):
                    p = new[pid]
                    self._event("start", f"{p['kind']} started   pid {pid}  {short_cmd(p['args'])}")
                for pid in sorted(old.keys() - new.keys()):
                    p = old[pid]
                    self._event("exit", f"{p['kind']} exited    pid {pid}  {short_cmd(p['args'])}")
            self._seen_procs = new
            self.procs = procs
            self.watch_pids = set(new)
            self.app_version = version

    def commit_conns(self, conns):
        now = time.time()
        with self.lock:
            new = {c["key"]: c for c in conns}
            old = self._seen_conns
            for key in new:
                self._first_seen.setdefault(key, now)
            if old is None:
                if conns:
                    self._event("info", f"{len(conns)} connection(s) already open")
            else:
                for key in new.keys() - old.keys():
                    c = new[key]
                    self._event("open", f"open    {c['service'] or '-':<18} {c['host']}:{c['port']}  pid {c['pid']}")
                for key in old.keys() - new.keys():
                    c = old[key]
                    age = now - self._first_seen.get(key, now)
                    self._event("close", f"closed  {c['service'] or '-':<18} {c['host']}:{c['port']}  after {ago(age)}")
            for key in list(self._first_seen):
                if key not in new:
                    del self._first_seen[key]
            for c in conns:
                c["age"] = now - self._first_seen.get(c["key"], now)
            self._seen_conns = new
            self.conns = conns

    def commit_files(self, files):
        with self.lock:
            self.files = files

    def commit_downloads(self, downloads):
        with self.lock:
            self.downloads = downloads

    def commit_rates(self, rate_in, rate_out, add_in, add_out, per_pid, source):
        with self.lock:
            self.rate_in, self.rate_out = rate_in, rate_out
            self.hist_in.append(rate_in)
            self.hist_out.append(rate_out)
            self.total_in += add_in
            self.total_out += add_out
            self.proc_rates = per_pid
            self.rate_source = source

    def commit_cache(self, cache):
        with self.lock:
            self.cache = cache

    def commit_io(self, read, write):
        with self.lock:
            self.io_read, self.io_write = read, write

    def clear_events(self):
        with self.lock:
            self.events.clear()

    def snapshot(self):
        with self.lock:
            return {
                "procs": list(self.procs), "conns": list(self.conns), "files": list(self.files),
                "downloads": list(self.downloads), "proc_rates": dict(self.proc_rates),
                "rate_in": self.rate_in, "rate_out": self.rate_out,
                "hist_in": list(self.hist_in), "hist_out": list(self.hist_out),
                "total_in": self.total_in, "total_out": self.total_out,
                "rate_source": self.rate_source, "cache": self.cache,
                "events": list(self.events), "notes": dict(self.notes),
                "paused": self.paused, "interval": self.interval,
                "app_version": self.app_version, "proc_io": self.proc_io,
                "io_read": self.io_read, "io_write": self.io_write,
            }


# ---------------------------------------------------------------- name lookups

class Labeler:
    """Turns remote IPs into a hostname and a service label."""

    def __init__(self, extra_hosts, use_dns=True):
        self.use_dns = use_dns
        self.hosts = dict(KNOWN_HOSTS)
        for item in extra_hosts:
            host, _, label = item.partition("=")
            self.hosts[host.strip()] = label.strip() or self._rule_label(host.strip()) or "custom"
        self.ip_map = {}
        self.rdns = {}
        self.pending = set()
        self.q = queue.Queue()
        for _ in range(4):
            threading.Thread(target=self._rdns_worker, daemon=True).start()

    @staticmethod
    def _rule_label(name):
        for pattern, label in HOST_RULES:
            if re.search(pattern, name, re.I):
                return label
        return ""

    def refresh_known(self):
        found = {}
        for host, label in self.hosts.items():
            try:
                for info in socket.getaddrinfo(host, 443, proto=socket.IPPROTO_TCP):
                    found[info[4][0]] = (host, label)
            except OSError:
                continue
        self.ip_map = found

    def _rdns_worker(self):
        while True:
            ip = self.q.get()
            try:
                name = socket.gethostbyaddr(ip)[0]
            except (OSError, UnicodeError):
                name = ""
            self.rdns[ip] = name
            self.pending.discard(ip)

    def label(self, ip, port):
        if ip in self.ip_map:
            return self.ip_map[ip]
        if is_local(ip):
            return ip, "local network"
        name = None
        if self.use_dns:
            name = self.rdns.get(ip)
            if name is None and ip not in self.pending:
                self.pending.add(ip)
                self.q.put(ip)
        if name:
            return name, self._rule_label(name)
        return ip, ""


# ---------------------------------------------------------------- system probes

def exe_name(text):
    base = re.split(r"[\\/]", text.strip().strip('"'))[-1].lower()
    return base[:-4] if base.endswith(".exe") else base


def classify(args, name=None):
    base = exe_name(name) if name else exe_name(split_exe(args)[0])
    if APP_PROC_RE.match(args) or QGIS_PROC_NAME_RE.match(base):
        return "qgis_proc"
    if APP_RE.match(args) or QGIS_NAME_RE.match(base):
        return "QGIS"
    if base.startswith(("gdal", "ogr")):
        return "GDAL"
    if base in DOWNLOAD_TOOLS:
        return "download"
    return None


def scan_processes(exclude):
    # -ww keeps ps from trimming long command lines to the terminal width.
    out = run(["ps", "-axww", "-o", "pid=,ppid=,pcpu=,rss=,etime=,args="])
    if not out:
        return []
    rows, children = {}, collections.defaultdict(list)
    for line in out.splitlines():
        parts = line.split(None, 5)
        if len(parts) < 6:
            continue
        try:
            pid, ppid, cpu, rss = int(parts[0]), int(parts[1]), float(parts[2]), int(parts[3])
        except ValueError:
            continue
        rows[pid] = {"pid": pid, "ppid": ppid, "cpu": cpu, "rss": rss * 1024,
                     "etime": parts[4], "args": parts[5]}
        children[ppid].append(pid)
    picked = {}
    for pid, row in rows.items():
        if pid in exclude:
            continue
        kind = classify(row["args"])
        if kind:
            row["kind"] = kind
            picked[pid] = row
    stack = [pid for pid, r in picked.items() if r["kind"] in ("QGIS", "qgis_proc")]
    visited = set(stack)
    while stack:
        for child in children.get(stack.pop(), []):
            if child in visited or child in exclude:
                continue
            visited.add(child)
            if child not in picked:
                rows[child]["kind"] = "child"
                picked[child] = rows[child]
            stack.append(child)
    order = {"QGIS": 0, "qgis_proc": 1, "GDAL": 2, "download": 3, "child": 4}
    return sorted(picked.values(), key=lambda r: (order.get(r["kind"], 9), -r["cpu"]))


def read_lsof(pids):
    """One lsof call for every open file and socket of the watched processes."""
    if not pids or not shutil.which("lsof"):
        return []
    out = run(["lsof", "-nP", "-w", "-p", ",".join(str(p) for p in pids), "-F", "pftanPT"], timeout=15)
    if not out:
        return []
    entries, pid, cur = [], None, None
    for line in out.splitlines():
        if not line:
            continue
        tag, val = line[0], line[1:]
        if tag == "p":
            if cur:
                entries.append(cur)
            pid, cur = int(val), None
        elif tag == "f":
            if cur:
                entries.append(cur)
            cur = {"pid": pid, "fd": val}
        elif cur is None:
            continue
        elif tag == "t":
            cur["type"] = val
        elif tag == "a":
            cur["mode"] = val
        elif tag == "P":
            cur["proto"] = val
        elif tag == "n":
            cur["name"] = val
        elif tag == "T" and val.startswith("ST="):
            cur["state"] = val[3:]
    if cur:
        entries.append(cur)
    return entries


def read_nettop():
    """Cumulative bytes in/out per process, keyed by pid."""
    out = run(["nettop", "-P", "-L", "1", "-n", "-x", "-J", "bytes_in,bytes_out"], timeout=15)
    if out is None:
        return None
    totals = {}
    for line in out.splitlines():
        cells = [c.strip() for c in line.split(",")]
        for i, cell in enumerate(cells):
            if re.match(r"^\d{1,2}:\d{2}:\d{2}", cell):
                continue
            m = re.match(r"^(.+)\.(\d+)$", cell)
            if not m:
                continue
            nums = [int(x) for x in cells[i + 1:] if x.isdigit()]
            if len(nums) >= 2:
                totals[int(m.group(2))] = (nums[0], nums[1])
            break
    return totals


def win_file_version(path):
    """Read the version stamped into a Windows .exe, such as qgis-bin.exe."""
    try:
        import ctypes
        from ctypes import wintypes
        lib = ctypes.WinDLL("version")
        size = lib.GetFileVersionInfoSizeW(path, None)
        if not size:
            return ""
        buf = ctypes.create_string_buffer(size)
        if not lib.GetFileVersionInfoW(path, 0, size, buf):
            return ""
        ptr, length = ctypes.c_void_p(), wintypes.UINT()
        if not lib.VerQueryValueW(buf, "\\", ctypes.byref(ptr), ctypes.byref(length)):
            return ""

        class Fixed(ctypes.Structure):
            _fields_ = [(n, wintypes.DWORD) for n in (
                "sig", "struc", "ms", "ls", "pms", "pls", "mask", "flags", "os", "kind", "sub", "dms", "dls")]

        info = ctypes.cast(ptr, ctypes.POINTER(Fixed)).contents
        major, minor, patch = info.ms >> 16, info.ms & 0xFFFF, info.ls >> 16
        return f"{major}.{minor}.{patch}" if (major or minor) else ""
    except Exception:
        return ""


def app_version(args, exe="", cache={}):
    key = exe or args
    if key in cache:
        return cache[key]
    version = ""
    m = re.match(r"^(.*?\.app)/Contents/MacOS/", args)
    if m:
        try:
            with open(os.path.join(m.group(1), "Contents", "Info.plist"), "rb") as fh:
                info = plistlib.load(fh)
            version = str(info.get("CFBundleShortVersionString") or info.get("CFBundleVersion") or "")
        except Exception:
            version = ""
    else:
        m = re.search(r"QGIS[ _-]?(\d+\.\d+(?:\.\d+)?)", exe or args, re.I)
        if m:
            version = m.group(1)
        elif IS_WIN and exe:
            version = win_file_version(exe)
    cache[key] = version
    return version


def walk_limited(root, depth, limit=5000):
    count, stack = 0, [(root, 0)]
    while stack:
        folder, level = stack.pop()
        try:
            it = os.scandir(folder)
        except OSError:
            continue
        with it:
            for entry in it:
                count += 1
                if count > limit:
                    return
                try:
                    if entry.is_dir(follow_symlinks=False):
                        if level < depth and not entry.name.startswith("."):
                            stack.append((entry.path, level + 1))
                    elif entry.is_file(follow_symlinks=False):
                        yield entry.path, entry.stat(follow_symlinks=False)
                except OSError:
                    continue


def file_ext(path):
    name = re.split(r"[\\/]", path)[-1].lower()
    return os.path.splitext(name)[1]


def is_app_resource(path):
    """Files that ship inside QGIS itself, which are not worth listing."""
    p = path.replace("\\", "/").lower()
    return any(part in p for part in (
        "/contents/resources/", "/contents/frameworks/", "/apps/qgis", "/apps/gdal",
        "/share/proj", "/share/gdal", "/share/qgis"))


def safe(fn, *args, **kwargs):
    try:
        return fn(*args, **kwargs)
    except Exception:
        return None


def fmt_addr(addr):
    ip, port = addr[0], addr[1]
    return f"[{ip}]:{port}" if ":" in ip else f"{ip}:{port}"


# ---------------------------------------------------------------- live collector

class LiveCollector:
    def __init__(self, state, args):
        self.state = state
        self.args = args
        self.stop = threading.Event()
        self.labeler = Labeler(args.host or [], use_dns=not args.no_dns)
        self.exclude = {os.getpid()}
        self.file_track = {}
        self.dl_track = {}
        self.dl_seeded = False
        self.cache_prev = None
        self.disk_rate = 0.0
        self.nettop_ok = bool(shutil.which("nettop"))
        dirs = [os.path.join(HOME, "Downloads")] + [os.path.expanduser(d) for d in (args.watch or [])]
        self.watch_dirs = [d for d in dirs if os.path.isdir(d)]
        missing = [d for d in dirs if not os.path.isdir(d)]
        if missing:
            state.note("watch", "not found: " + ", ".join(tilde(d) for d in missing))
        if not shutil.which("lsof"):
            state.note("lsof", "lsof not found, no connections or files")

    def start(self):
        threading.Thread(target=self._fast_loop, daemon=True).start()
        threading.Thread(target=self._slow_loop, daemon=True).start()
        threading.Thread(target=self._dns_loop, daemon=True).start()
        if self.nettop_ok:
            threading.Thread(target=self._nettop_loop, daemon=True).start()
        else:
            self.state.note("nettop", "nettop not found, rates estimated from disk")

    # Processes, sockets and open files, every refresh.
    def _fast_loop(self):
        while not self.stop.is_set():
            started = time.time()
            if not self.state.paused:
                try:
                    self.cycle()
                    self.state.note("error", None)
                except Exception as exc:  # keep the screen alive whatever happens
                    self.state.note("error", f"collector: {exc}")
            self.stop.wait(max(0.2, self.state.interval - (time.time() - started)))

    def gather(self):
        """Processes, sockets and open files of everything QGIS-related (macOS tools)."""
        procs = scan_processes(self.exclude)
        sockets, files = [], []
        for e in read_lsof([p["pid"] for p in procs]):
            kind, name = e.get("type", ""), e.get("name", "")
            if kind in ("IPv4", "IPv6") and "->" in name:
                local, remote = name.split("->", 1)
                sockets.append({"pid": e["pid"], "proto": e.get("proto", "?"), "local": local,
                                "remote": remote, "state": e.get("state", "")})
            elif kind == "REG":
                files.append({"pid": e["pid"], "path": name, "mode": e.get("mode", "")})
        return procs, sockets, files

    def cycle(self):
        now = time.time()
        procs, sockets, raw_files = self.gather()
        version = ""
        for p in procs:
            if p["kind"] == "QGIS":
                version = app_version(p["args"], p.get("exe", ""))
                break
        self.state.commit_procs(procs, version)
        conns = []
        for sock in sockets:
            ip, port = split_hostport(sock["remote"])
            host, service = self.labeler.label(ip, port)
            if self.args.show_ips:
                host = ip
            conns.append({
                "key": (sock["pid"], sock["proto"], sock["local"], sock["remote"]),
                "pid": sock["pid"], "proto": sock["proto"], "ip": ip, "port": port,
                "host": host, "service": service, "state": sock["state"],
            })
        files, seen_paths = [], set()
        for f in raw_files:
            name = f["path"]
            if file_ext(name) not in OPEN_FILE_EXT or name in seen_paths or is_app_resource(name):
                continue
            seen_paths.add(name)
            try:
                size = os.stat(name).st_size
            except OSError:
                continue
            prev = self.file_track.get(name)
            rate = 0.0
            if prev and now > prev[1] and size > prev[0]:
                rate = (size - prev[0]) / (now - prev[1])
            self.file_track[name] = (size, now)
            mode = f["mode"]
            status = "writing" if rate > 0 else ("reading" if mode == "r" else "open")
            files.append({"pid": f["pid"], "mode": mode, "size": size, "rate": rate,
                          "status": status, "path": name})
        for path in list(self.file_track):
            if path not in seen_paths:
                del self.file_track[path]
        conns.sort(key=lambda c: (c["service"] == "", c["service"], c["pid"], c["host"]))
        files.sort(key=lambda f: (-f["rate"], f["path"]))
        self.state.commit_conns(conns)
        self.state.commit_files(files)
        self.disk_rate = sum(f["rate"] for f in files)
        self.after_cycle(procs, files, now)

    def after_cycle(self, procs, files, now):
        if not self.nettop_ok:
            est = self.disk_rate + (self.state.cache or {}).get("rate", 0.0)
            est += sum(d["rate"] for d in self.state.downloads)
            self.state.commit_rates(est, 0.0, est * self.state.interval, 0, {}, "disk estimate")

    # Downloads folders and the QGIS network cache, every couple of seconds.
    def _slow_loop(self):
        last_cache = 0.0
        while not self.stop.is_set():
            if not self.state.paused:
                try:
                    self.scan_downloads()
                    if time.time() - last_cache > 5:
                        self.scan_cache()
                        last_cache = time.time()
                except Exception as exc:
                    self.state.note("error2", f"scanner: {exc}")
            self.stop.wait(2.0)

    def scan_downloads(self):
        now = time.time()
        cutoff = now - self.args.recent * 60
        rows, seen = [], set()
        for root in self.watch_dirs:
            for path, st in walk_limited(root, depth=2):
                ext = file_ext(path)
                if ext not in GEO_EXT and ext not in PARTIAL_EXT:
                    continue
                if st.st_mtime < cutoff:
                    continue
                seen.add(path)
                track = self.dl_track.get(path)
                rate = 0.0
                if track is None:
                    track = {"size": st.st_size, "t": now, "grow": 0.0, "announced": False}
                    self.dl_track[path] = track
                    if self.dl_seeded:
                        self.state.event("new", f"new file  {tilde(path)}")
                        track["grow"] = now
                elif st.st_size != track["size"]:
                    if st.st_size > track["size"] and now > track["t"]:
                        rate = (st.st_size - track["size"]) / (now - track["t"])
                    track.update(size=st.st_size, t=now, grow=now, announced=False)
                growing = now - track["grow"] < 5
                if ext in PARTIAL_EXT:
                    status = "partial"
                elif growing:
                    status = "growing"
                else:
                    status = "done"
                    if track["grow"] and not track["announced"]:
                        track["announced"] = True
                        self.state.event("done", f"finished  {tilde(path)}  {human_bytes(st.st_size)}")
                rows.append({"path": path, "size": st.st_size, "rate": rate,
                             "status": status, "mtime": st.st_mtime})
        for path in list(self.dl_track):
            if path not in seen:
                del self.dl_track[path]
        self.dl_seeded = True
        rows.sort(key=lambda r: ({"growing": 0, "partial": 1}.get(r["status"], 2), -r["mtime"]))
        self.state.commit_downloads(rows)

    def cache_dirs(self):
        if self.args.cache_dir:
            return [os.path.expanduser(self.args.cache_dir)]
        pattern = os.path.join(HOME, "Library", "Application Support", "QGIS", "QGIS*", "profiles", "*", "cache")
        found = glob.glob(pattern)
        found += glob.glob(os.path.join(HOME, "Library", "Caches", "QGIS*"))
        found += glob.glob(os.path.join(HOME, ".local", "share", "QGIS", "QGIS*", "profiles", "*", "cache"))
        for env in ("APPDATA", "LOCALAPPDATA"):
            base = os.environ.get(env)
            if base:
                found += glob.glob(os.path.join(base, "QGIS", "QGIS*", "profiles", "*", "cache"))
        return [d for d in found if os.path.isdir(d)]

    def scan_cache(self):
        dirs = self.cache_dirs()
        if not dirs:
            self.state.commit_cache(None)
            return
        total = count = 0
        for d in dirs:
            for path, _, names in os.walk(d):
                for name in names:
                    try:
                        total += os.lstat(os.path.join(path, name)).st_size
                        count += 1
                    except OSError:
                        pass
        now = time.time()
        rate = 0.0
        if self.cache_prev and now > self.cache_prev[1] and total > self.cache_prev[0]:
            rate = (total - self.cache_prev[0]) / (now - self.cache_prev[1])
        self.cache_prev = (total, now)
        self.state.commit_cache({"size": total, "files": count, "rate": rate, "dirs": dirs})

    def _dns_loop(self):
        while not self.stop.is_set():
            self.labeler.refresh_known()
            self.stop.wait(300)

    def _nettop_loop(self):
        prev, empty_runs = {}, 0
        while not self.stop.is_set():
            started = time.time()
            if not self.state.paused:
                totals = read_nettop()
                now = time.time()
                if not totals:
                    empty_runs += 1
                    if empty_runs >= 3:
                        self.state.note("nettop", "nettop returned nothing, rates unavailable")
                else:
                    empty_runs = 0
                    self.state.note("nettop", None)
                    pids = self.state.watch_pids
                    per_pid, add_in, add_out, rin, rout = {}, 0, 0, 0.0, 0.0
                    for pid in pids:
                        if pid not in totals:
                            continue
                        b_in, b_out = totals[pid]
                        if pid in prev:
                            p_in, p_out, p_t = prev[pid]
                            dt = max(0.001, now - p_t)
                            d_in, d_out = max(0, b_in - p_in), max(0, b_out - p_out)
                            add_in += d_in
                            add_out += d_out
                            per_pid[pid] = (d_in / dt, d_out / dt)
                            rin += d_in / dt
                            rout += d_out / dt
                        prev[pid] = (b_in, b_out, now)
                    for pid in list(prev):
                        if pid not in pids:
                            del prev[pid]
                    self.state.commit_rates(rin, rout, add_in, add_out, per_pid, "nettop")
            self.stop.wait(max(0.2, self.state.interval - (time.time() - started)))


# ---------------------------------------------------------------- psutil collector

class PsutilCollector(LiveCollector):
    """Windows and Linux: processes, sockets, open files and I/O through psutil."""

    ORDER = {"QGIS": 0, "qgis_proc": 1, "GDAL": 2, "download": 3, "child": 4}

    def __init__(self, state, args):
        super().__init__(state, args)
        state.note("lsof", None)
        state.proc_io = "io"
        self.nettop_ok = False
        self.handles = {}
        self.io_prev = {}
        self.net_prev = None
        self.per_process_sockets = False

    def start(self):
        for target in (self._fast_loop, self._slow_loop, self._dns_loop):
            threading.Thread(target=target, daemon=True).start()

    def handle(self, pid):
        proc = self.handles.get(pid)
        if proc is not None and safe(proc.is_running):
            return proc
        try:
            proc = psutil.Process(pid)
            proc.cpu_percent(None)  # the first reading only primes the counter
        except psutil.Error:
            return None
        self.handles[pid] = proc
        return proc

    def gather(self):
        now = time.time()
        names, children = {}, collections.defaultdict(list)
        for p in psutil.process_iter(["pid", "ppid", "name"]):
            info = p.info
            names[info["pid"]] = info.get("name") or ""
            children[info.get("ppid")].append(info["pid"])
        picked = {}
        for pid, name in names.items():
            if pid not in self.exclude and name:
                kind = classify("", name)
                if kind:
                    picked[pid] = kind
        stack = [pid for pid, kind in picked.items() if kind in ("QGIS", "qgis_proc")]
        visited = set(stack)
        while stack:
            for child in children.get(stack.pop(), []):
                if child in visited or child in self.exclude:
                    continue
                visited.add(child)
                picked.setdefault(child, "child")
                stack.append(child)

        procs = []
        for pid, kind in picked.items():
            proc = self.handle(pid)
            if proc is None:
                continue
            try:
                with proc.oneshot():
                    cpu = proc.cpu_percent(None)
                    rss = proc.memory_info().rss
                    created = proc.create_time()
                    exe = safe(proc.exe) or ""
                    cmd = safe(proc.cmdline) or []
                    io = safe(proc.io_counters) if hasattr(proc, "io_counters") else None
            except psutil.Error:
                continue
            if cmd:
                args = subprocess.list2cmdline(cmd) if IS_WIN else " ".join(cmd)
            else:
                args = exe or names.get(pid, "")
            procs.append({"pid": pid, "cpu": cpu, "rss": rss, "etime": etime(now - created),
                          "args": args, "exe": exe, "kind": kind, "io": io})
        for pid in list(self.handles):
            if pid not in picked:
                del self.handles[pid]
        procs.sort(key=lambda r: (self.ORDER.get(r["kind"], 9), -r["cpu"]))

        pids = {p["pid"] for p in procs}
        sockets = self.read_sockets(pids)
        files = []
        for p in procs:
            proc = self.handles.get(p["pid"])
            for f in (safe(proc.open_files) or []) if proc else []:
                files.append({"pid": p["pid"], "path": f.path, "mode": getattr(f, "mode", "") or ""})
        return procs, sockets, files

    def read_sockets(self, pids):
        if not pids:
            return []
        pairs = []
        if not self.per_process_sockets:
            try:
                pairs = [(c.pid, c) for c in psutil.net_connections(kind="inet") if c.pid in pids]
            except psutil.AccessDenied:  # macOS needs root for the system-wide list
                self.per_process_sockets = True
        if self.per_process_sockets:
            for pid in pids:
                proc = self.handles.get(pid)
                fn = getattr(proc, "net_connections", None) or getattr(proc, "connections", None)
                for c in (safe(fn, kind="inet") or []) if fn else []:
                    pairs.append((pid, c))
        out = []
        for pid, c in pairs:
            if not c.raddr:
                continue
            state = "" if c.status in ("NONE", "") else c.status
            out.append({"pid": pid, "proto": "TCP" if c.type == socket.SOCK_STREAM else "UDP",
                        "local": fmt_addr(c.laddr), "remote": fmt_addr(c.raddr), "state": state})
        return out

    def after_cycle(self, procs, files, now):
        per_pid, total_read, total_write = {}, 0.0, 0.0
        for p in procs:
            io = p.get("io")
            if io is None:
                continue
            if IS_WIN:
                # Windows counts file, network and device I/O together in these.
                r, w = io.read_bytes, io.write_bytes
            else:
                r = getattr(io, "read_chars", io.read_bytes)
                w = getattr(io, "write_chars", io.write_bytes)
            prev = self.io_prev.get(p["pid"])
            self.io_prev[p["pid"]] = (r, w, now)
            if prev and now > prev[2]:
                dt = now - prev[2]
                rr, ww = max(0, r - prev[0]) / dt, max(0, w - prev[1]) / dt
                per_pid[p["pid"]] = (rr, ww)
                total_read += rr
                total_write += ww
        live = {p["pid"] for p in procs}
        for pid in list(self.io_prev):
            if pid not in live:
                del self.io_prev[pid]

        net = safe(psutil.net_io_counters)
        rate_in = rate_out = 0.0
        add_in = add_out = 0
        if net and self.net_prev:
            dt = max(0.001, now - self.net_prev[2])
            add_in = max(0, net.bytes_recv - self.net_prev[0])
            add_out = max(0, net.bytes_sent - self.net_prev[1])
            rate_in, rate_out = add_in / dt, add_out / dt
        if net:
            self.net_prev = (net.bytes_recv, net.bytes_sent, now)
        self.state.commit_rates(rate_in, rate_out, add_in, add_out, per_pid, "whole-machine network (psutil)")
        self.state.commit_io(total_read, total_write)


# ---------------------------------------------------------------- demo collector

def demo_path(path):
    """Demo paths shaped like the platform the demo is running on."""
    if IS_WIN:
        path = path.replace("/Users/hp/Library/Application Support/QGIS", "/Users/hp/AppData/Roaming/QGIS")
    path = HOME + path[len("/Users/hp"):] if path.startswith("/Users/hp") else path
    return path.replace("/", "\\") if IS_WIN else path


if IS_WIN:
    DEMO_QGIS = '"C:\\Program Files\\QGIS 3.40.4\\bin\\qgis-bin.exe"'
    DEMO_GDAL = '"C:\\Program Files\\QGIS 3.40.4\\bin\\gdalwarp.exe"'
    DEMO_CURL = "C:\\Windows\\System32\\curl.exe"
else:
    DEMO_QGIS = "/Applications/QGIS.app/Contents/MacOS/QGIS"
    DEMO_GDAL = "/Applications/QGIS.app/Contents/MacOS/bin/gdalwarp"
    DEMO_CURL = "curl"


class DemoCollector:
    """Simulated QGIS session so the interface can be tried without QGIS running."""

    SERVICES = [
        ("LANDFIRE", "lfps.usgs.gov", "3.33.152.147", 6),
        ("AWS S3", "firepal-plans.s3.us-west-2.amazonaws.com", "52.218.236.81", 2),
        ("Earth Search STAC", "earth-search.aws.element84.com", "18.155.68.12", 2),
        ("Sentinel-2 COGs", "sentinel-cogs.s3.us-west-2.amazonaws.com", "52.92.148.17", 4),
        ("Planetary Computer", "sentinel2l2a01.blob.core.windows.net", "20.150.103.68", 2),
        ("OSM tiles", "tile.openstreetmap.org", "151.101.2.217", 3),
        ("QGIS plugins", "plugins.qgis.org", "37.120.165.157", 1),
        ("", "ec2-54-190-12-8.us-west-2.compute.amazonaws.com", "54.190.12.8", 1),
    ]

    def __init__(self, state, args):
        self.state = state
        self.args = args
        self.stop = threading.Event()
        self.t0 = time.time() - 1834
        self.conns = {}
        self.port = 51000
        self.rin = 400_000.0
        self.burst = 0
        if IS_WIN:
            state.proc_io = "io"
        self.files = {
            "/Users/hp/Library/Application Support/QGIS/QGIS3/profiles/default/FirePal/tactics_7f3a.gpkg": [1_843_200, "u", 0],
            "/Users/hp/Library/Application Support/QGIS/QGIS3/profiles/default/FirePal/tactics_7f3a.gpkg-wal": [65_536, "u", 0],
            "/Users/hp/FirePal_QGIS/cache/Landfire_LF2024_FBFM40.xml": [1_204, "r", 0],
            "/Users/hp/SatStream/clips/S2B_10SEG_20261021_NDVI_clip.tif": [0, "w", 9_000_000],
        }
        self.files = {demo_path(k): v for k, v in self.files.items()}
        self.dl = [
            {"path": "/Users/hp/Downloads/LF2024_FBFM40_CONUS.zip", "size": 0, "target": 48_000_000, "grow": 0, "done": False},
            {"path": "/Users/hp/Downloads/S2A_MSIL2A_20261019_T10SEG.tif.part", "size": 0, "target": 180_000_000, "grow": 0, "done": False},
            {"path": "/Users/hp/Downloads/usgs_3dep_dem_n38w122.tif", "size": 22_413_000, "target": 22_413_000, "grow": 0, "done": True},
        ]
        for d in self.dl:
            d["path"] = demo_path(d["path"])
        self.cache_size = 212_000_000
        self.children = {}
        self.first = True

    def start(self):
        threading.Thread(target=self._loop, daemon=True).start()

    def _loop(self):
        while not self.stop.is_set():
            if not self.state.paused:
                self.tick()
            self.stop.wait(self.state.interval)

    def tick(self):
        now = time.time()
        dt = self.state.interval
        # throughput: a random walk with occasional tile-streaming bursts
        if self.burst <= 0 and random.random() < 0.12:
            self.burst = random.randint(3, 9)
        target = random.uniform(2.5e6, 7e6) if self.burst > 0 else random.uniform(5e4, 6e5)
        self.burst -= 1
        self.rin = max(0.0, self.rin * 0.55 + target * 0.45)
        rout = random.uniform(2e3, 2.5e4) + (random.uniform(3e5, 9e5) if random.random() < 0.08 else 0)

        procs = [{"pid": 5512, "ppid": 1, "cpu": random.uniform(14, 48) + (60 if self.burst > 0 else 0),
                  "rss": 1_420_000_000 + random.randint(0, 90_000_000), "etime": etime(now - self.t0),
                  "args": DEMO_QGIS, "kind": "QGIS"}]
        if random.random() < 0.05 and "gdalwarp" not in self.children:
            self.children["gdalwarp"] = (5900 + random.randint(0, 90), now, random.randint(6, 14))
        if random.random() < 0.04 and "curl" not in self.children:
            self.children["curl"] = (6100 + random.randint(0, 90), now, random.randint(5, 12))
        for name, (pid, born, life) in list(self.children.items()):
            if now - born > life:
                del self.children[name]
                continue
            if name == "gdalwarp":
                args = DEMO_GDAL + " -cutline aoi.gpkg -crop_to_cutline /vsicurl/https://sentinel-cogs.s3.us-west-2.amazonaws.com/.../B08.tif clip.tif"
                procs.append({"pid": pid, "ppid": 5512, "cpu": random.uniform(70, 99), "rss": 210_000_000,
                              "etime": etime(now - born), "args": args, "kind": "GDAL"})
            else:
                args = DEMO_CURL + " -L -O https://lfps.usgs.gov/arcgis/rest/directories/arcgisoutput/LF2024_FBFM40.zip"
                procs.append({"pid": pid, "ppid": 812, "cpu": random.uniform(1, 6), "rss": 9_000_000,
                              "etime": etime(now - born), "args": args, "kind": "download"})
        version = "3.40.4"
        self.state.commit_procs(procs, version)

        # connections: weighted churn per service
        for svc in self.SERVICES:
            label, host, ip, weight = svc
            live = [k for k, c in self.conns.items() if c["host"] == host]
            if len(live) < weight and random.random() < (0.35 if self.burst > 0 else 0.12):
                self.port += 1
                key = (5512, "TCP", f"192.168.1.23:{self.port}", f"{ip}:443")
                self.conns[key] = {"key": key, "pid": 5512, "proto": "TCP", "ip": ip, "port": "443",
                                   "host": ip if self.args.show_ips else host, "service": label, "state": "ESTABLISHED"}
            elif live and random.random() < 0.08:
                del self.conns[random.choice(live)]
        for c in self.conns.values():
            c["host"] = c["ip"] if self.args.show_ips else next(s[1] for s in self.SERVICES if s[2] == c["ip"])
        conns = sorted(self.conns.values(), key=lambda c: (c["service"] == "", c["service"], c["host"]))
        self.state.commit_conns(conns)

        # open files, one clip being written while a burst is on
        files = []
        for path, info in self.files.items():
            rate = 0.0
            if info[2] and info[0] < info[2] and self.burst > 0:
                rate = random.uniform(4e5, 1.6e6)
                info[0] = min(info[2], info[0] + int(rate * dt))
            elif path.endswith("-wal") and random.random() < 0.1:
                rate = random.uniform(4e3, 4e4)
                info[0] += int(rate * dt)
            status = "writing" if rate else ("reading" if info[1] == "r" else "open")
            files.append({"pid": 5512, "mode": info[1], "size": info[0], "rate": rate,
                          "status": status, "path": path})
        files.sort(key=lambda f: (-f["rate"], f["path"]))
        self.state.commit_files(files)

        # downloads folder
        rows = []
        for d in self.dl:
            rate = 0.0
            if not d["done"]:
                rate = random.uniform(1.5e6, 4.5e6)
                d["size"] = min(d["target"], d["size"] + int(rate * dt))
                d["grow"] = now
                if d["size"] >= d["target"]:
                    d["done"] = True
                    final = d["path"][:-5] if d["path"].endswith(".part") else d["path"]
                    d["path"] = final
                    self.state.event("done", f"finished  {tilde(final)}  {human_bytes(d['size'])}")
            ext = file_ext(d["path"])
            status = "partial" if ext in PARTIAL_EXT else ("growing" if now - d["grow"] < 5 and d["grow"] else "done")
            rows.append({"path": d["path"], "size": d["size"], "rate": rate, "status": status,
                         "mtime": d["grow"] or now - 600})
        rows.sort(key=lambda r: ({"growing": 0, "partial": 1}.get(r["status"], 2), -r["mtime"]))
        self.state.commit_downloads(rows)

        grow = random.uniform(2e5, 1.5e6) if self.burst > 0 else 0.0
        self.cache_size += int(grow * dt)
        self.state.commit_cache({"size": self.cache_size, "files": 4_812, "rate": grow,
                                 "dirs": [demo_path("/Users/hp/Library/Application Support/QGIS/QGIS3/profiles/default/cache")]})
        if IS_WIN:
            self.state.commit_io(self.rin * 1.1, self.rin * 0.4)
        add_in = int(self.rin * dt)
        per_pid = {5512: (self.rin * 0.9, rout)}
        for p in procs[1:]:
            per_pid[p["pid"]] = (self.rin * 0.1, 0.0)
        self.state.commit_rates(self.rin, rout, add_in, int(rout * dt), per_pid, "demo")


# ---------------------------------------------------------------- panel builders

class Palette:
    def __init__(self):
        self.plain = 0
        self.bold = 0
        self.dim = 0
        self.green = self.cyan = self.yellow = self.magenta = self.red = self.blue = 0
        self.head = 0

    def init_curses(self):
        self.bold = curses.A_BOLD
        self.dim = curses.A_DIM
        self.head = curses.A_REVERSE
        if curses.has_colors():
            curses.start_color()
            try:
                curses.use_default_colors()
                bg = -1
            except curses.error:
                bg = curses.COLOR_BLACK
            for i, fg in enumerate([curses.COLOR_GREEN, curses.COLOR_CYAN, curses.COLOR_YELLOW,
                                    curses.COLOR_MAGENTA, curses.COLOR_RED, curses.COLOR_BLUE], start=1):
                curses.init_pair(i, fg, bg)
            curses.init_pair(7, curses.COLOR_BLACK, curses.COLOR_CYAN)
            self.green, self.cyan, self.yellow = (curses.color_pair(1), curses.color_pair(2),
                                                  curses.color_pair(3))
            self.magenta, self.red, self.blue = (curses.color_pair(4), curses.color_pair(5),
                                                 curses.color_pair(6))
            self.head = curses.color_pair(7) | curses.A_BOLD


P = Palette()


def build_throughput(s, width):
    label_w = 18
    bar_w = max(10, width - label_w - 2)
    rows = [
        [(f" {ARROW_IN} in  {human_rate(s['rate_in']) if s['rate_in'] else '0 B/s':>11}  ", P.bold),
         (spark(s["hist_in"], bar_w), P.green)],
        [(f" {ARROW_OUT} out {human_rate(s['rate_out']) if s['rate_out'] else '0 B/s':>11}  ", P.bold),
         (spark(s["hist_out"], bar_w), P.cyan)],
    ]
    machine = s["proc_io"] == "io"
    scope = " (whole machine)" if machine else ""
    info = [(f" session {ARROW_IN} {human_bytes(s['total_in'])}  {ARROW_OUT} {human_bytes(s['total_out'])}{scope}", P.plain)]
    if machine:
        info.append((f"    QGIS disk+network I/O  read {human_rate(s['io_read'])}  write {human_rate(s['io_write'])}", P.plain))
    rows.append(info)
    cache = s["cache"]
    if cache:
        grow = f", +{human_rate(cache['rate'])}" if cache["rate"] else ""
        info2 = [(f" QGIS network cache {human_bytes(cache['size'])} in {cache['files']:,} files{grow}", P.plain)]
    else:
        info2 = [(" QGIS network cache not found", P.dim)]
    info2.append((f"    source: {s['rate_source']}", P.dim))
    rows.append(info2)
    return "Throughput", None, rows


def build_processes(s, width):
    if s["proc_io"] == "io":
        col_in, col_out = "I/O READ", "I/O WRITE"
    else:
        col_in, col_out = ARROW_IN + " NET", ARROW_OUT + " NET"
    header = f"{'PID':>6}  {'KIND':<9} {'CPU%':>6} {'MEMORY':>9} {'ELAPSED':>11} {col_in:>11} {col_out:>11}  COMMAND"
    rows = []
    kind_color = {"QGIS": P.green | P.bold, "qgis_proc": P.green, "GDAL": P.yellow,
                  "download": P.cyan, "child": P.blue}
    for p in s["procs"]:
        r_in, r_out = s["proc_rates"].get(p["pid"], (0.0, 0.0))
        left = f"{p['pid']:>6}  "
        mid = f" {p['cpu']:>6.1f} {human_bytes(p['rss']):>9} {p['etime']:>11} "
        used = len(left) + 9 + len(mid) + 24
        rows.append([
            (left, P.plain), (f"{p['kind']:<9}", kind_color.get(p["kind"], P.plain)), (mid, P.plain),
            (f"{human_rate(r_in):>11}", P.green), (" ", P.plain), (f"{human_rate(r_out):>11}", P.cyan),
            ("  " + squeeze(short_cmd(p["args"]), max(10, width - used - 2)), P.plain),
        ])
    if not rows:
        rows.append([("  QGIS is not running. This screen will pick it up as soon as it starts.", P.dim)])
    return "Processes", header, rows


def build_connections(s, width):
    header = f"{'PID':>6}  {'SERVICE':<20} {'STATE':<12} {'AGE':>7} {'PORT':>5} {'PROTO':<5}  REMOTE"
    rows = []
    for c in s["conns"]:
        left = f"{c['pid']:>6}  "
        svc = f"{squeeze(c['service'] or '-', 20):<20}"
        state = c["state"] or ("-" if c["proto"] == "UDP" else "")
        rest = f" {state[:12]:<12} {ago(c.get('age', 0)):>7} {c['port']:>5} {c['proto']:<5}  "
        used = len(left) + 20 + len(rest)
        state_attr = P.plain if state in ("ESTABLISHED", "-") else P.yellow
        rows.append([
            (left, P.plain), (svc, P.magenta if c["service"] else P.dim),
            (rest, state_attr), (squeeze(c["host"], max(10, width - used - 1)), P.plain),
        ])
    return "Connections", header, rows


def build_files(s, width):
    header = f"{'PID':>6}  {'MODE':<4} {'STATUS':<8} {'SIZE':>9} {'RATE':>11}  PATH"
    rows = []
    for f in s["files"]:
        left = f"{f['pid']:>6}  {f['mode']:<4} "
        status_attr = P.green | P.bold if f["status"] == "writing" else P.plain
        mid = f" {human_bytes(f['size']):>9} {human_rate(f['rate']):>11}  "
        used = len(left) + 8 + len(mid)
        rows.append([
            (left, P.plain), (f"{f['status']:<8}", status_attr), (mid, P.plain),
            (squeeze(tilde(f["path"]), max(10, width - used - 1)), P.plain),
        ])
    return "Open files", header, rows


def build_downloads(s, width):
    header = f"{'STATUS':<8} {'SIZE':>9} {'RATE':>11} {'MODIFIED':>9}  PATH"
    rows = []
    now = time.time()
    attrs = {"growing": P.green | P.bold, "partial": P.yellow, "done": P.dim}
    for d in s["downloads"]:
        mid = f" {human_bytes(d['size']):>9} {human_rate(d['rate']):>11} {ago(now - d['mtime']) + ' ago':>9}  "
        used = 8 + len(mid)
        rows.append([
            (f"{d['status']:<8}", attrs.get(d["status"], P.plain)), (mid, P.plain),
            (squeeze(tilde(d["path"]), max(10, width - used - 1)), P.plain),
        ])
    return "Downloads", header, rows


def build_events(s, width):
    attrs = {"open": P.green, "close": P.dim, "start": P.cyan, "exit": P.red,
             "done": P.yellow | P.bold, "new": P.yellow, "info": P.plain}
    rows = []
    for t, kind, text in s["events"]:
        stamp = time.strftime("%H:%M:%S", time.localtime(t))
        rows.append([(f" {stamp}  ", P.dim), (squeeze(text, max(10, width - 12)), attrs.get(kind, P.plain))])
    return "Events", None, rows


BUILDERS = [build_throughput, build_processes, build_connections, build_files, build_downloads, build_events]


def allocate(built, avail):
    """Split the available rows between panels by need and weight."""
    full, mins = [], []
    for i, (_, header, rows) in enumerate(built):
        chrome = 1 + (1 if header else 0)
        full.append(chrome + max(1, len(rows)))
        mins.append(chrome + 1 if i else chrome + len(rows))
    alloc = [0] * len(built)
    spare = avail
    for i in range(len(built)):
        take = min(mins[i], spare)
        alloc[i] = take
        spare -= take
    while spare > 0:
        progressed = False
        for i, weight in enumerate(WEIGHTS):
            for _ in range(weight):
                if spare and alloc[i] < full[i]:
                    alloc[i] += 1
                    spare -= 1
                    progressed = True
        if not progressed:
            break
    if spare > 0:
        alloc[-1] += spare
    return alloc


# ---------------------------------------------------------------- curses UI

class View:
    def __init__(self):
        self.zoom = None
        self.scroll = 0
        self.last_alloc = None


def put(scr, y, x, text, attr=0):
    h, w = scr.getmaxyx()
    if y < 0 or y >= h or x >= w - 1:
        return x
    text = text[: max(0, w - 1 - x)]
    try:
        scr.addstr(y, x, text, attr)
    except curses.error:
        pass
    return x + len(text)


def put_row(scr, y, segments):
    x = 0
    for text, attr in segments:
        x = put(scr, y, x, text, attr)


def header_text(s):
    qgis = [p for p in s["procs"] if p["kind"] == "QGIS"]
    if qgis:
        ver = f" {s['app_version']}" if s["app_version"] else ""
        others = len(s["procs"]) - len(qgis)
        extra = f", {others} related" if others else ""
        status = f"QGIS{ver} running, pid {qgis[0]['pid']}{extra}, {len(s['conns'])} connections"
    elif s["procs"]:
        status = f"{len(s['procs'])} GIS tool process(es), QGIS not open"
    else:
        status = "waiting for QGIS to start"
    return status


def draw(scr, state, view):
    h, w = scr.getmaxyx()
    scr.erase()
    if h < 10 or w < 50:
        put(scr, 0, 0, "Window too small for qgis-watch, make it bigger.", P.bold)
        scr.refresh()
        return
    s = state.snapshot()
    left = f" QGIS WATCH  {header_text(s)}"
    right = f"{'PAUSED  ' if s['paused'] else ''}every {s['interval']:.1f}s  {time.strftime('%H:%M:%S')} "
    bar = left + " " * max(1, w - len(left) - len(right)) + right
    put(scr, 0, 0, bar[: w - 1] + " ", P.head)

    built = [b(s, w) for b in BUILDERS]
    avail = h - 2
    if view.zoom is not None:
        alloc = [0] * len(built)
        alloc[view.zoom] = avail
    else:
        alloc = allocate(built, avail)
    if alloc != view.last_alloc:
        # Panels changed size, so repaint the whole screen instead of patching it.
        scr.clearok(True)
        view.last_alloc = alloc

    y = 1
    for i, (title, header, rows) in enumerate(built):
        n = alloc[i]
        if n <= 0:
            continue
        top = y
        try:
            scr.hline(y, 0, curses.ACS_HLINE, w)
        except curses.error:
            pass
        count = f" ({len(rows)})" if i in (1, 2, 3, 4) else ""
        x = put(scr, y, 1, f" {i + 1} {title}{count} ", P.yellow | P.bold)
        y += 1
        n -= 1
        if header and n > 0:
            put(scr, y, 0, header, P.dim | P.bold)
            y += 1
            n -= 1
        start = 0
        if view.zoom == i:
            view.scroll = max(0, min(view.scroll, max(0, len(rows) - n)))
            start = view.scroll
        shown = rows[start:start + n]
        for row in shown:
            put_row(scr, y, row)
            y += 1
        hidden = len(rows) - start - len(shown)
        if hidden > 0 or start > 0:
            more = []
            if start:
                more.append(f"{start} above")
            if hidden > 0:
                more.append(f"{hidden} more")
            hint = ", ".join(more) + ("" if view.zoom == i else f", press {i + 1} to zoom")
            put(scr, top, x + 1, f" {hint} ", P.dim)
        y = top + alloc[i]

    keys = " q quit  p pause  1-6 zoom  0 all  arrows scroll  +/- rate  n IPs  c clear"
    notes = "  ".join(s["notes"].values())
    footer = keys
    if notes:
        footer = keys + "   " + notes
    put(scr, h - 1, 0, footer[: w - 1], P.dim if not notes else P.red)
    if notes:
        put(scr, h - 1, 0, keys[: w - 1], P.dim)
    scr.refresh()


def run_ui(scr, state, args):
    try:
        curses.curs_set(0)
    except curses.error:
        pass
    P.init_curses()
    scr.timeout(250)
    scr.keypad(True)
    view = View()
    while True:
        draw(scr, state, view)
        ch = scr.getch()
        if ch == curses.KEY_RESIZE:
            if IS_WIN and hasattr(curses, "resize_term"):
                try:
                    curses.resize_term(0, 0)  # PDCurses needs this to pick up the new size
                except curses.error:
                    pass
            continue
        if ch == -1:
            continue
        if ch in (ord("q"), ord("Q")):
            return
        if ch in (ord("p"), ord("P"), ord(" ")):
            state.paused = not state.paused
        elif ord("1") <= ch <= ord("6"):
            idx = ch - ord("1")
            view.zoom = None if view.zoom == idx else idx
            view.scroll = 0
        elif ch in (ord("0"), 27):
            view.zoom, view.scroll = None, 0
        elif ch == curses.KEY_DOWN:
            view.scroll += 1
        elif ch == curses.KEY_UP:
            view.scroll = max(0, view.scroll - 1)
        elif ch == curses.KEY_NPAGE:
            view.scroll += max(1, scr.getmaxyx()[0] - 5)
        elif ch == curses.KEY_PPAGE:
            view.scroll = max(0, view.scroll - max(1, scr.getmaxyx()[0] - 5))
        elif ch in (ord("+"), ord("=")):
            state.interval = max(0.5, state.interval - 0.5)
        elif ch in (ord("-"), ord("_")):
            state.interval = min(10.0, state.interval + 0.5)
        elif ch in (ord("n"), ord("N")):
            args.show_ips = not args.show_ips
        elif ch in (ord("c"), ord("C")):
            state.clear_events()


def print_once(state, width):
    s = state.snapshot()
    print(f"QGIS WATCH  {header_text(s)}  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    for i, b in enumerate(BUILDERS):
        title, header, rows = b(s, width)
        print()
        print(f"== {i + 1} {title} " + "=" * max(0, width - len(title) - 7))
        if header:
            print(header)
        for row in rows[:40]:
            print("".join(t for t, _ in row)[:width])
        if len(rows) > 40:
            print(f"  ... {len(rows) - 40} more")
    for note in s["notes"].values():
        print(f"note: {note}")


def main():
    global BARS, ELLIPSIS, ARROW_IN, ARROW_OUT
    parser = argparse.ArgumentParser(
        prog="qgis-watch",
        description="Live terminal view of what QGIS is streaming and downloading on macOS.")
    parser.add_argument("--demo", action="store_true", help="simulate activity to preview the interface")
    parser.add_argument("--once", action="store_true", help="print one plain-text snapshot and exit")
    parser.add_argument("-i", "--interval", type=float, default=1.0, help="refresh seconds (default 1)")
    parser.add_argument("--watch", action="append", metavar="DIR",
                        help="extra folder to watch for downloads (repeatable; ~/Downloads is always watched)")
    parser.add_argument("--host", action="append", metavar="HOST[=LABEL]",
                        help="extra hostname to label, e.g. my-bucket.s3.us-west-2.amazonaws.com=Fireplans")
    parser.add_argument("--recent", type=float, default=30, metavar="MIN",
                        help="show downloads modified in the last MIN minutes (default 30)")
    parser.add_argument("--cache-dir", metavar="DIR", help="QGIS network cache folder, if not the default")
    parser.add_argument("--log", metavar="FILE", help="append events to FILE")
    parser.add_argument("--no-dns", action="store_true", help="skip reverse DNS lookups")
    parser.add_argument("--ascii", action="store_true", help="plain ASCII graphics for limited terminals")
    parser.add_argument("--unicode", action="store_true", help="force Unicode graphics (for example in an older Windows console)")
    parser.add_argument("--psutil", action="store_true", help="on macOS, collect with psutil instead of ps/lsof/nettop")
    parser.add_argument("--version", action="version", version=f"qgis-watch {VERSION}")
    args = parser.parse_args()
    args.show_ips = False
    args.interval = max(0.5, min(10.0, args.interval))

    try:
        locale.setlocale(locale.LC_ALL, "")
    except locale.Error:
        pass
    if IS_WIN:
        # Windows Terminal and VS Code draw the graph and line characters; the old console may not.
        fancy = bool(os.environ.get("WT_SESSION") or os.environ.get("TERM_PROGRAM"))
    else:
        fancy = "UTF-8" in (locale.getpreferredencoding(False) or "").upper()
    if args.ascii or not (fancy or args.unicode):
        BARS, ELLIPSIS, ARROW_IN, ARROW_OUT = " .:-=+*#@", "~", "v", "^"
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass

    if curses is None and not args.once:
        if IS_WIN:
            print("qgis-watch needs one more package for its screen on Windows. Install it with:\n"
                  "    py -m pip install windows-curses", file=sys.stderr)
        else:
            print("This Python was built without curses, so only --once works.", file=sys.stderr)
        sys.exit(1)
    use_psutil = not args.demo and (not IS_MAC or args.psutil)
    if use_psutil and psutil is None:
        pip = "py -m pip" if IS_WIN else "python3 -m pip"
        print(f"qgis-watch needs the psutil package on this system. Install it with:\n"
              f"    {pip} install psutil{' windows-curses' if IS_WIN else ''}", file=sys.stderr)
        sys.exit(1)

    state = State(args.interval, args.log)
    if args.demo:
        collector = DemoCollector(state, args)
    elif use_psutil:
        collector = PsutilCollector(state, args)
    else:
        collector = LiveCollector(state, args)
    collector.start()

    if args.once:
        time.sleep(2.5 if not args.demo else 0.1)
        if args.demo:
            for _ in range(4):
                collector.tick()
        try:
            print_once(state, shutil.get_terminal_size((120, 40)).columns)
        except BrokenPipeError:
            pass
        return

    try:
        curses.wrapper(run_ui, state, args)
    except KeyboardInterrupt:
        pass
    finally:
        collector.stop.set()


if __name__ == "__main__":
    main()
