"""What this install can and cannot do, and what each gap costs.

Installing every extra pulls in a fair chain of dependencies, and most people
need none of it. So the answer to "what do I actually have?" should not be
read off an import error in the middle of a run.

Every row says the same three things: whether the capability is there, what it
is for, and **what happens without it**. A missing optional tool is almost
never fatal here -- there is a slower or narrower fallback -- and a checklist
of red crosses that does not say so reads as a broken install.
"""
from __future__ import annotations

import importlib
import os
import shutil
import time
import subprocess
import sys
from pathlib import Path

from .i18n import t


def _module(name):
    try:
        importlib.import_module(name)
        return True, ""
    except ImportError:
        return False, ""


def _binary(name, args=("--version",), must_run=False):
    """On PATH, and -- when `must_run` -- actually able to answer.

    `lake` on a machine with no toolchain is on PATH and reports an error, so
    "the binary exists" is the wrong question for anything we intend to run.
    """
    path = shutil.which(name)
    if not path:
        return False, ""
    try:
        out = subprocess.run([path, *args], capture_output=True, text=True,
                             timeout=20, encoding="utf-8",
                             errors="replace")
    except (OSError, subprocess.SubprocessError):
        return not must_run, path
    first = (out.stdout or out.stderr or "").strip().splitlines()
    detail = first[0][:70] if first else path
    if must_run and out.returncode != 0:
        return False, detail
    return True, detail


def _z3_version():
    try:
        import z3
        return True, z3.get_version_string()
    except ImportError:
        return False, ""


def _flint():
    ok, _ = _module("flint")
    if not ok:
        return False, ""
    import flint
    return True, "Arb via python-flint " + getattr(flint, "__version__", "?")


def _geng():
    # nauty's geng exits non-zero on --version, so ask it for nothing instead.
    return _binary("geng", ("-h",))


def _lean():
    """`lake`, and whether it can answer from HERE.

    Outside a Lean project `lake --version` fails with "no default toolchain":
    the toolchain is chosen by the project's `lean-toolchain` file, so a
    perfectly good installation reports an error when asked from certo's own
    directory. Reporting that as "absent" sent a user to say certo was wrong
    about their machine, and they were right -- Lean was installed, with
    Mathlib built, and certo could not see it.

    So the two cases are separated. Missing is missing; present-but-unpinned
    is present, and says what to do.
    """
    ok, detail = _binary("lake", ("--version",), must_run=True)
    if not ok and "default toolchain" in detail:
        return False, t("doctor.lean.no_default")
    return ok, detail


def _startup():
    """How much of a certo invocation is the interpreter starting up?

    A user reported `certo --help` staying alive indefinitely. It was not
    certo: `site` runs every `.pth` in site-packages before a single line of
    certo executes, and one of them here loads a certificate-store shim that
    reaches for the system trust store. On a corporate network that can block.
    certo contributes under a tenth of a second and can do nothing about the
    rest -- but it can say where the time went, and a `certo --help` that
    hangs is otherwise indistinguishable from a certo that hangs.

    The check is the symptom, bounded: if the plain interpreter does not come
    back within the timeout, that IS the report.
    """
    import sys

    def timed(args, limit):
        start = time.perf_counter()
        try:
            subprocess.run([sys.executable, *args, "-c", "pass"],
                           capture_output=True, timeout=limit)
        except subprocess.TimeoutExpired:
            return None
        except (OSError, subprocess.SubprocessError):
            return -1.0
        return time.perf_counter() - start

    bare = timed(["-S"], 20)
    full = timed([], 20)
    if full is None:
        return False, t("doctor.detail.startup_hang", seconds=20,
                        names=", ".join(_startup_hooks()[:3]) or "-")
    if bare is None or bare < 0 or full < 0:
        return True, t("doctor.detail.startup_unknown")

    overhead = full - bare
    if overhead < 0.5:
        return True, t("doctor.detail.startup_ok",
                       total="{:.2f}".format(full))
    return False, t("doctor.detail.startup_slow",
                    total="{:.2f}".format(full),
                    overhead="{:.2f}".format(overhead),
                    names=", ".join(_startup_hooks()[:3]) or "-")


def _startup_hooks() -> list:
    """The `.pth` files that RUN code rather than just adding a path.

    A path entry costs nothing. A line beginning `import` executes at every
    interpreter start, which is where the time -- and any hang -- lives.
    """
    import glob
    import os
    import site

    out = []
    try:
        roots = list(site.getsitepackages())
    except Exception:  # noqa: BLE001
        return out
    for d in roots:
        for f in glob.glob(os.path.join(d, "*.pth")) + \
                glob.glob(os.path.join(d, "Lib", "site-packages", "*.pth")):
            try:
                text = open(f, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            if any(ln.startswith("import ") for ln in text.splitlines()):
                out.append(os.path.basename(f))
    return sorted(set(out))


def _site_roots():
    """Every site-packages directory, resolved and deduplicated.

    `site.getsitepackages()` returns overlapping roots on Windows -- the
    prefix and its `Lib/site-packages` -- so the same leftover is found twice
    and reported as two. Resolving and deduplicating here is what makes a
    count mean what it says.
    """
    import site

    seen, out = set(), []
    try:
        roots = list(site.getsitepackages())
    except Exception:  # noqa: BLE001  -- a venv without the helper
        roots = []
    for d in roots:
        for base in (Path(d), Path(d) / "Lib" / "site-packages"):
            try:
                real = base.resolve()
            except OSError:
                continue
            if real.is_dir() and real not in seen:
                seen.add(real)
                out.append(real)
    return out


def _script_dirs():
    """Where the launchers live, ASKED rather than derived.

    The first version of this took site-packages and went up one: from
    `<prefix>/Lib/site-packages` that lands on `<prefix>/Lib/Scripts`, which
    does not exist -- the launchers are at `<prefix>/Scripts`, one level
    further up, and on POSIX the layout differs again. So the `.deleteme`
    marker was never found on a real install.

    The test did not catch it because the test built the fixture the same
    wrong way. `sysconfig` knows the answer and every platform's version of
    it; deriving it was inventing one.
    """
    import sysconfig

    out = []
    for scheme in (None, "nt_user" if os.name == "nt" else "posix_user"):
        try:
            path = (sysconfig.get_path("scripts") if scheme is None
                    else sysconfig.get_path("scripts", scheme))
            real = Path(path).resolve()
        except (KeyError, OSError):
            continue
        if real.is_dir() and real not in out:
            out.append(real)
    return out


def leftovers() -> list:
    """The `~`-prefixed directories pip abandons when an install is stopped.

    pip renames what it is replacing to `~`-something, copies the new files,
    then deletes the rename. Interrupted between the second and third step --
    which on Windows is what a held-open `.exe` does -- it leaves the rename
    behind, and the package is then present twice under two names, one of them
    unimportable.

    Only entries DIRECTLY inside a site-packages root, whose name begins with
    `~`, and which resolve back inside that root. Anything else is somebody
    else's file.
    """
    out, seen = [], set()
    # Two markers, because pip leaves two. `~`-something is the rename it did
    # not finish; `something.deleteme` is a launcher it could not replace,
    # left beside an orphaned `.exe` whose package is gone. A user found
    # exactly that pair and could not run `certo doctor` to diagnose it,
    # because the thing to diagnose was the missing package -- so the second
    # marker is looked for here, for the runs where certo does still start.
    for given in _script_dirs():
        # RESOLVED HERE, like the roots below and for the same reason: a
        # comparison between a resolved child and an unresolved parent is
        # false whenever Windows hands back a short name. This is the third
        # place that has bitten, so neither side trusts its caller.
        try:
            scripts = Path(given).resolve()
        except OSError:
            continue
        for entry in sorted(scripts.glob("*.deleteme")):
            try:
                real = entry.resolve()
            except OSError:
                continue
            if real.parent == scripts and real not in seen:
                seen.add(real)
                out.append(real)
    for given in _site_roots():
        # RESOLVED HERE rather than trusted from the caller. Windows hands out
        # 8.3 short names -- `C:\Users\JTRAVE~1\...` for `C:\Users\jtraverso`
        # -- and junctions, so `entry.resolve().parent` and the root as given
        # are the same directory under two spellings. Comparing them
        # unresolved made every entry look like it pointed out of the tree,
        # and the repair found nothing at all.
        try:
            root = Path(given).resolve()
        except OSError:
            continue
        for entry in sorted(root.glob("~*")):
            try:
                real = entry.resolve()
            except OSError:
                continue
            if real.parent != root:
                continue            # a link pointing out of the tree
            if real not in seen:
                seen.add(real)
                out.append(real)
    return out


def held_open() -> list:
    """certo's own scripts that something is holding, by name.

    A running executable is opened by Windows with read sharing only, so
    asking for write access is refused -- without touching the file. That
    refusal IS the diagnosis: it is the thing that makes the next
    `pip install -e .` stop halfway, and removing the leftovers without
    stopping the holder just produces new ones.
    """
    out = []
    for root in _site_roots():
        for exe in sorted((root.parent / "Scripts").glob("certo*")):
            if exe.is_dir():
                continue
            try:
                with open(exe, "r+b"):
                    pass
            except PermissionError:
                out.append(exe.name)
            except OSError:
                continue
    return sorted(set(out))


def repair(apply: bool = False) -> dict:
    """What an interrupted install left behind, and -- with `apply` -- its end.

    PREVIEW IS THE DEFAULT, and not out of caution for its own sake: the thing
    being removed is in site-packages, where a wrong guess breaks an
    environment rather than a file. So the list comes back first, and removing
    it is a second decision.

    certo does not reinstall. That is pip's job, running pip from inside the
    tool would hide which of the two failed, and the reason the install broke
    is usually still running -- `held_open` names it.
    """
    import shutil

    found = leftovers()
    report = {"leftovers": [str(p) for p in found],
              "held_open": held_open(), "applied": bool(apply),
              "removed": [], "failed": []}
    if not apply:
        return report

    for path in found:
        try:
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()
            report["removed"].append(str(path))
        except OSError as exc:
            report["failed"].append({"path": str(path),
                                     "why": "{}: {}".format(
                                         type(exc).__name__, exc)})
    return report


def _partial_install():
    """Did a pip install stop halfway and leave the package in pieces?

    On Windows pip cannot replace a file another process holds open, and
    `certo-mcp.exe` is held open for as long as the MCP server runs. So
    `pip install -e .` from inside an editor with the server attached aborts
    part-way, renames the old distribution to `~`-something, and leaves
    nothing installed under the real name -- which is how `pip show certo`
    came to report a version three releases old while the tool reported the
    current one.

    The leftover is pip's own marker and it is the only reliable trace, so
    that is what is looked for.
    """
    found = leftovers()
    if not found:
        return True, t("doctor.detail.install_clean")
    return False, t("doctor.detail.install_partial",
                    n=len(found),
                    names=", ".join(sorted(p.name for p in found)[:3]))


#: The name on PyPI. The import package is `certo`; this is what a
#: metadata lookup has to ask for, and it is checked against
#: `pyproject.toml` by a test so a rename cannot mute the check.
DISTRIBUTION = "certo-math"


def _metadata_copies() -> list:
    """Every copy of the distribution's metadata, and what each one IS.

    There are three kinds and they were being collapsed into one answer:

      INSTALLED   a `.dist-info` under a site-packages root
      SOURCE      an `egg-info` in a checkout, which `python -m build` leaves
                  behind and `PYTHONPATH=src` puts first on `sys.path`
      LEFTOVER    a `~`-prefixed directory pip abandoned mid-install -- and
                  `importlib.metadata` reads it as a real distribution, so a
                  half-finished upgrade answers with the OLD version forever

    A machine with all three is not exotic: it is a checkout, an install, and
    one interrupted `pip install`. Reporting the first one found made `doctor`
    warn about a source tree while `pip show` correctly said 0.12.0 -- true,
    useless, and indistinguishable from the case that matters.

    Returns `[(version, kind, path)]`, newest metadata first is not attempted:
    the caller decides which kind it cares about.
    """
    try:
        from importlib.metadata import distributions
    except ImportError:
        return []

    roots = _site_roots()
    wanted = {DISTRIBUTION.lower(), "certo"}
    out = []
    for dist in distributions():
        try:
            name = (dist.metadata["Name"] or "").lower().replace("_", "-")
        except Exception:  # noqa: BLE001  -- a broken METADATA file
            continue
        if name not in wanted:
            continue
        try:
            where = Path(str(dist.locate_file(""))).resolve()
            version = dist.version
        except (OSError, AttributeError):
            continue
        holder = getattr(dist, "_path", None)
        if holder is not None and Path(str(holder)).name.startswith("~"):
            kind = "leftover"
        elif any(where == r or r in where.parents for r in roots):
            kind = "installed"
        else:
            kind = "source"
        out.append((version, kind, where))
    return out


def _metadata_source():
    """The version `pip show` would report, and whether it is an install.

    Kept for the one question its callers ask -- `cli.installed_version` needs
    a version only when there genuinely is an install. An INSTALLED copy wins
    over a source tree, because that is what `pip show` reports and what a bug
    report will name.
    """
    copies = _metadata_copies()
    for version, kind, where in copies:
        if kind == "installed":
            return version, True, where
    for version, kind, where in copies:
        if kind == "source":
            return version, False, where
    return None, False, None


def _installed_metadata():
    """Does `pip show certo-math` agree with the code that is running?

    They are declared once now, so they cannot be WRITTEN apart -- but an
    editable install goes stale on its own the moment the version moves, and
    a user found ours reporting 0.6.0 while the tool reported 0.9.0. A
    disagreement here is not a broken install; it is a stale one, and saying
    which is the whole value of the check.

    Four answers, and the first version of this gave the first three as one.
    """
    from . import __version__

    copies = _metadata_copies()
    installed = [v for v, kind, _w in copies if kind == "installed"]
    source = [(v, w) for v, kind, w in copies if kind == "source"]
    leftover = sorted({v for v, kind, _w in copies if kind == "leftover"})

    if not copies:
        return True, t("doctor.detail.metadata_absent",
                       why="PackageNotFoundError")

    # A leftover answers `importlib.metadata` like an install, so it is named
    # here rather than silently counted as one. `--repair` removes it.
    suffix = ("" if not leftover else
              " " + t("doctor.detail.metadata_leftover",
                      versions=", ".join(leftover)))

    if installed:
        if __version__ in installed:
            return not leftover, t("doctor.detail.metadata_ok",
                                   version=__version__) + suffix
        return False, t("doctor.detail.metadata_stale",
                        installed=", ".join(sorted(set(installed))),
                        running=__version__) + suffix

    if source:
        version, where = source[0]
        return False, t("doctor.detail.metadata_source_tree",
                        version=version, path=str(where)) + suffix

    # Only leftovers answered: there is no install, and the version anything
    # reads out of the metadata is the one pip failed to replace.
    return False, t("doctor.detail.metadata_only_leftover",
                    versions=", ".join(leftover))


CHECKS = [
    ("startup", False, _startup),
    ("install", False, _partial_install),
    ("metadata", False, _installed_metadata),
    # (key, required, probe)
    ("python", True, lambda: (sys.version_info >= (3, 11),
                              sys.version.split()[0])),
    ("z3", True, _z3_version),
    ("pulp", True, lambda: _module("pulp")),
    ("mcp", False, lambda: _module("mcp")),
    ("flint", False, _flint),
    ("mpmath", False, lambda: _module("mpmath")),
    ("numpy", False, lambda: _module("numpy")),
    ("clarabel", False, lambda: _module("clarabel")),
    ("nauty", False, _geng),
    ("cadical", False, lambda: _binary("cadical")),
    ("kissat", False, lambda: _binary("kissat")),
    ("drat_trim", False, lambda: _binary("drat-trim", ())),
    ("lean", False, _lean),
]


def report() -> dict:
    """Run every probe. Returns rows plus a count of what is missing."""
    rows, missing_required = [], 0
    for key, required, probe in CHECKS:
        try:
            ok, detail = probe()
        except Exception as e:  # noqa: BLE001
            ok, detail = False, "{}: {}".format(type(e).__name__, e)
        if required and not ok:
            missing_required += 1
        rows.append({
            "key": key,
            "ok": bool(ok),
            "required": required,
            "detail": detail,
            "what": t("doctor.what." + key),
            "without": "" if ok else t("doctor.without." + key),
        })

    caps = {r["key"]: r["ok"] for r in rows}
    from . import coverage

    return {
        "rows": rows,
        # Not a capability, so not a row: nothing is missing when it is empty.
        # It is here because `doctor` is where somebody looks to find out what
        # certo is doing on their machine, and writing a file is one of those
        # things.
        "coverage": dict(coverage.summary(), enabled=coverage.enabled()),
        "missing_required": missing_required,
        "numerics": caps["flint"] or caps["mpmath"],
        "sat_external": caps["cadical"] or caps["kissat"],
        "ok": missing_required == 0,
    }


# ---------------------------------------------------------------------------
# MCP registration
# ---------------------------------------------------------------------------


def mcp_status(workspace=None) -> dict:
    """Is the server registered, and does it actually start?

    Registered and working are different questions, and the second is the one
    people mean. Importing the server module in a subprocess answers it
    without needing a client.
    """
    ws = Path(workspace or os.environ.get("CERTO_WORKSPACE", Path.cwd()))
    cfg = Path.cwd() / ".mcp.json"
    out = {
        "workspace": str(ws.resolve()),
        "config_present": cfg.exists(),
        "config_path": str(cfg),
        # Informational only since the registration stopped using it: the
        # server starts through the interpreter, so a missing shim is no
        # longer a reason it would fail.
        "command_on_path": bool(shutil.which("certo-mcp")),
        "starts_via": "module",
    }
    sdk, _ = _module("mcp")
    out["sdk"] = sdk
    if not sdk:
        out["starts"] = False
        out["detail"] = t("doctor.mcp.no_sdk")
        return out

    # Import rather than run: starting the server for real would block on
    # stdio waiting for a client. What this answers is whether the module the
    # registration names can be loaded by the interpreter that would load it.
    probe = subprocess.run(
        [sys.executable, "-c", "import certo.mcp_server as m; print(m.__name__)"],
        capture_output=True, text=True, timeout=60,
        encoding="utf-8", errors="replace")
    out["starts"] = probe.returncode == 0
    out["detail"] = ((probe.stderr or "").strip().splitlines() or [""])[-1][:200] \
        if probe.returncode else ""
    return out


def mcp_entry(python=None) -> dict:
    """How to start the MCP server, as `.mcp.json` wants it.

    THE INTERPRETER, NOT THE SHIM, and the reason is a bug this cost three
    times on one machine. `certo-mcp` is a launcher pip generates; on Windows
    the running process holds that `.exe` open for its whole lifetime, so an
    upgrade fails with

        WinError 32: the process cannot access the file because it is being
        used by another process

    pip has already removed the old package by then, which leaves the install
    broken -- `import certo` stops working -- and a `~certo` directory behind.
    `doctor --repair` cleans that up afterwards; nothing was stopping it
    happening again.

    Starting the server as `<interpreter> -m certo.mcp_server` moves the lock
    onto `python.exe`, which pip never replaces, and leaves the shim free. The
    server is the same server: `certo.mcp_server` has had a `__main__` all
    along and the console script only ever called its `main`.

    PORTABLE BY DEFAULT, and that is a correction rather than a preference.
    The first version wrote `sys.executable`, which pins the environment and
    is the more accurate thing to say -- until you notice that `.mcp.json` is
    a file people COMMIT. An absolute path carries one machine's user name
    into a shared config and starts nothing on anyone else's. Pass an
    interpreter to `python` when pinning is what you want and the file is
    yours; the default names `python`, which is portable and fixes the lock
    just as well, because whatever it resolves to is not the shim.
    """
    return {
        "mcpServers": {
            "certo": {
                "command": python or "python",
                "args": ["-m", "certo.mcp_server"],
                "env": {"CERTO_WORKSPACE": "."},
            }
        }
    }


#: Kept as a name because it was one, and read through the function so the
#: interpreter is the one running now rather than the one that imported this.
MCP_ENTRY = mcp_entry()


def register_mcp(path=None) -> dict:
    """Write `.mcp.json`, merging rather than replacing.

    Replacing would drop every other server the project has registered, which
    is a rude thing for a diagnostic command to do.
    """
    import json

    p = Path(path or (Path.cwd() / ".mcp.json"))
    existing = {}
    if p.exists():
        try:
            existing = json.loads(p.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            return {"written": False, "path": str(p),
                    "detail": t("doctor.mcp.bad_json", path=str(p))}

    entry = mcp_entry()["mcpServers"]["certo"]
    servers = dict(existing.get("mcpServers") or {})
    already = servers.get("certo") == entry
    # An entry written by an older certo names the `certo-mcp` shim, which is
    # the thing that cannot be replaced while the server runs. Rewriting it is
    # the point of running this again, so `already` is False for those and the
    # merge replaces certo's own entry while leaving every other server alone.
    servers["certo"] = entry
    existing["mcpServers"] = servers
    p.write_text(json.dumps(existing, indent=2) + "\n", encoding="utf-8")
    return {"written": True, "path": str(p), "already": already,
            "servers": sorted(servers)}
