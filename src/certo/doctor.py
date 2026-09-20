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


def _metadata_source():
    """The distribution's metadata, and WHERE it was read from.

    `importlib.metadata` searches `sys.path`, and a source tree carries
    `src/<name>.egg-info` the moment anybody runs `python -m build`. With
    `PYTHONPATH=src` that egg-info is found first and answers as though it
    were an install -- so this check, which exists to catch an install that
    has gone stale, reported `[ok] matching the code` on a machine where the
    package was ABSENT and `pip show` returned nothing. The state it was
    written to detect is the state it hid.

    So the question is not only "what version does the metadata say" but
    "is that metadata an INSTALL". Anything outside a site-packages root is
    not one.

    Returns `(version, installed, path)`; `version` is None when nothing was
    found at all.
    """
    try:
        from importlib.metadata import PackageNotFoundError, distribution
    except ImportError:
        # No metadata machinery at all: nothing to disagree with, which is
        # the quiet branch and not a failure. The import was outside the
        # guard for one commit and an interpreter without it crashed here.
        return None, False, None

    dist = None
    for name in (DISTRIBUTION, "certo"):
        # Installs made before the distribution was renamed still carry the
        # old name. Without this the check would find nothing, take the quiet
        # branch, and stop working -- a guard that goes silent is worse than
        # one that was never written.
        try:
            dist = distribution(name)
            break
        except PackageNotFoundError:
            continue
        except Exception:  # noqa: BLE001  -- a broken .dist-info
            continue
    if dist is None:
        return None, False, None

    try:
        where = Path(str(dist.locate_file(""))).resolve()
    except (OSError, AttributeError):
        return dist.version, True, None

    roots = _site_roots()
    installed = any(where == r or r in where.parents for r in roots)
    return dist.version, installed, where


def _installed_metadata():
    """Does `pip show certo-math` agree with the code that is running?

    They are declared once now, so they cannot be WRITTEN apart -- but an
    editable install goes stale on its own the moment the version moves, and
    a user found ours reporting 0.6.0 while the tool reported 0.9.0. A
    disagreement here is not a broken install; it is a stale one, and saying
    which is the whole value of the check.

    And a version that came from a source tree is not an install at all,
    which is a third answer this used to give as the first.
    """
    from . import __version__

    version, installed, where = _metadata_source()
    if version is None:
        return True, t("doctor.detail.metadata_absent",
                       why="PackageNotFoundError")
    if not installed:
        return False, t("doctor.detail.metadata_source_tree",
                        version=version, path=str(where or "?"))
    if version == __version__:
        return True, t("doctor.detail.metadata_ok", version=version)
    return False, t("doctor.detail.metadata_stale", installed=version,
                    running=__version__)


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
    return {
        "rows": rows,
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
        "command_on_path": bool(shutil.which("certo-mcp")),
    }
    sdk, _ = _module("mcp")
    out["sdk"] = sdk
    if not sdk:
        out["starts"] = False
        out["detail"] = t("doctor.mcp.no_sdk")
        return out

    probe = subprocess.run(
        [sys.executable, "-c", "import certo.mcp_server as m; print(m.__name__)"],
        capture_output=True, text=True, timeout=60,
        encoding="utf-8", errors="replace")
    out["starts"] = probe.returncode == 0
    out["detail"] = ((probe.stderr or "").strip().splitlines() or [""])[-1][:200] \
        if probe.returncode else ""
    return out


MCP_ENTRY = {
    "mcpServers": {
        "certo": {"command": "certo-mcp", "env": {"CERTO_WORKSPACE": "."}}
    }
}


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

    servers = dict(existing.get("mcpServers") or {})
    already = servers.get("certo") == MCP_ENTRY["mcpServers"]["certo"]
    servers["certo"] = MCP_ENTRY["mcpServers"]["certo"]
    existing["mcpServers"] = servers
    p.write_text(json.dumps(existing, indent=2) + "\n", encoding="utf-8")
    return {"written": True, "path": str(p), "already": already,
            "servers": sorted(servers)}
