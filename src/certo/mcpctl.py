"""Which certo MCP servers are running, and which are running OLD code.

An MCP server is started by its client over stdio and lives as long as the
client keeps it. After `pip install` it goes on answering with the code it
loaded: a user mixed results from two versions without noticing. certo cannot
restart a server -- only the client can start one -- but it can say which are
stale, and stop them so the client starts fresh ones:

  * every MCP answer carries `certo_version`, and `stale: true` with a note
    when the server's code is older than the installed package;
  * `certo mcp status` lists the servers, when each started, and which
    started before the current install;
  * `certo mcp restart` shows what it would stop; `--yes` stops the stale
    ones (`--all`, every one). The client then reconnects: `/mcp` in Claude
    Code, a restart in Claude Desktop.

Stopping a server ends that client's session with it, which is why listing is
the default and stopping takes a flag.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

DIST = "certo-math"
_SERVER = re.compile(r"certo[._\-]mcp(_server)?\b")


def _dist():
    try:
        from importlib import metadata
        return metadata.distribution(DIST)
    except Exception:  # noqa: BLE001 -- not installed, or unreadable
        return None


def installed_version():
    d = _dist()
    return None if d is None else d.version


def running_installed_copy() -> bool:
    """Is THIS process's certo the installed one -- not a checkout on the
    path? Only then can "installed differs from loaded" mean stale."""
    import certo

    d = _dist()
    if d is None:
        return False
    try:
        return Path(d.locate_file("certo/__init__.py")).resolve() == \
            Path(certo.__file__).resolve()
    except (OSError, TypeError, ValueError):
        return False


def stale():
    """`(installed, loaded)` when this process runs code older than the
    installed package, else None."""
    from . import __version__

    if not running_installed_copy():
        return None
    inst = installed_version()
    if inst and inst != __version__:
        return inst, __version__
    return None


def install_time():
    """When the installed package was written, as an epoch, or None."""
    d = _dist()
    if d is None:
        return None
    for f in d.files or []:
        if f.name == "METADATA":
            try:
                return Path(d.locate_file(f)).stat().st_mtime
            except OSError:
                return None
    return None


def servers():
    """`[{pid, started, cmd}]` for every process that looks like a certo MCP
    server. `started` is an epoch, or None when the platform would not say."""
    me = os.getpid()
    rows = []
    if os.name == "nt":
        ps = ("Get-CimInstance Win32_Process | Where-Object { $_.CommandLine "
              "-match 'certo[._-]mcp' } | Select-Object ProcessId, "
              "@{n='Start';e={$_.CreationDate.ToUniversalTime().ToString('o')}}, "
              "CommandLine | ConvertTo-Json -Compress")
        try:
            out = subprocess.run(["powershell", "-NoProfile", "-Command", ps],
                                 capture_output=True, text=True, timeout=60,
                                 encoding="utf-8", errors="replace").stdout
            data = json.loads(out) if out.strip() else []
        except (OSError, subprocess.SubprocessError, ValueError):
            data = []
        for d in [data] if isinstance(data, dict) else data:
            try:
                started = datetime.fromisoformat(
                    d["Start"].replace("Z", "+00:00")).timestamp()
            except (KeyError, TypeError, ValueError, AttributeError):
                started = None
            rows.append({"pid": int(d["ProcessId"]), "started": started,
                         "cmd": d.get("CommandLine") or ""})
    else:
        try:
            out = subprocess.run(["ps", "-eo", "pid=,lstart=,args="],
                                 capture_output=True, text=True, timeout=30).stdout
        except (OSError, subprocess.SubprocessError):
            out = ""
        for line in out.splitlines():
            parts = line.split(None, 6)
            if len(parts) < 7:
                continue
            try:
                started = time.mktime(time.strptime(" ".join(parts[1:6]),
                                                    "%a %b %d %H:%M:%S %Y"))
            except ValueError:
                started = None
            rows.append({"pid": int(parts[0]), "started": started,
                         "cmd": parts[6]})
    return [r for r in rows if r["pid"] != me and _SERVER.search(r["cmd"])
            and " mcp status" not in r["cmd"] and " mcp restart" not in r["cmd"]]


def status() -> dict:
    """The installed version, when it was installed, and every server with
    whether it started before that."""
    when = install_time()
    rows = []
    for r in servers():
        r = dict(r)
        r["stale"] = bool(when and r["started"] and r["started"] < when)
        r["started_iso"] = (datetime.fromtimestamp(r["started"], timezone.utc)
                            .isoformat(timespec="seconds")
                            if r["started"] else None)
        rows.append(r)
    return {"installed": installed_version(),
            "installed_at": (datetime.fromtimestamp(when, timezone.utc)
                             .isoformat(timespec="seconds") if when else None),
            "servers": rows}


def stop(pids) -> list:
    """Stop these processes; returns `[(pid, ok, detail)]`."""
    out = []
    for pid in pids:
        try:
            if os.name == "nt":
                r = subprocess.run(["taskkill", "/PID", str(pid), "/T", "/F"],
                                   capture_output=True, text=True, timeout=30,
                                   encoding="utf-8", errors="replace")
                out.append((pid, r.returncode == 0,
                            (r.stdout or r.stderr).strip()[:120]))
            else:
                import signal

                os.kill(pid, signal.SIGTERM)
                out.append((pid, True, "SIGTERM"))
        except (OSError, subprocess.SubprocessError) as e:
            out.append((pid, False, str(e)[:120]))
    return out


if __name__ == "__main__":                                   # pragma: no cover
    json.dump(status(), sys.stdout, indent=2)
