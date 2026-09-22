"""What certo was asked and could NOT settle.

THE POINT. Every `out_of_theory`, `timeout`, `unknown_solver` and
`resource_exhausted` is a recorded instance of a question somebody brought and
this tool could not answer -- a route its caller had to abandon, or pursue
without help. Counted over time and grouped by command, those are the honest
answer to "which mathematics should certo cover next", which is otherwise
decided by whoever writes the backlog from memory.

Nothing recorded this until 0.13. The ledger looked like the place, and is
not: the ledger is opt-in, it ties a CLAIM to a re-verifiable artefact, and a
question certo could not settle produces no artefact to tie. Two different
jobs. Reading the ledger for coverage found two lines, both conclusive.

WHAT IS RECORDED, and the rule that bounds it: numbers about SIZE, never names
or values from the problem. A command, a status, an engine, which surface
asked, the version, and whatever scalars in `meta` are on the allowlist below
-- n, a count, a degree. Not `detail`, which interpolates the caller's own
names into its message; not a title, not a path, not a spec. The line
"`sweep` could not finish at n=11" is the whole of what a coverage map needs
and is already visible to anyone who watched the command run.

AND IT IS ON BY DEFAULT, which is the part that had to be argued rather than
assumed. Recording only on request is what the ledger does, and after a year
of releases the ledger holds two lines: a switch nobody remembers to flip
measures nothing. But a tool whose entire argument is that it does not say
more than it knows does not get to start writing files quietly either. So:

  * it writes ONE file, in the user's own data directory, never the working
    directory, because certo is run from wherever the mathematics lives;
  * `CERTO_NO_COVERAGE=1` turns it off completely, everywhere;
  * `CERTO_COVERAGE_FILE` puts it somewhere else;
  * it is bounded, and when it fills it STOPS rather than rotating -- losing
    the oldest evidence silently is the failure this module exists to fix;
  * `certo doctor` reports it, so it is discoverable without reading this;
  * and a failure to record never fails the command. A coverage log that can
    break a run is worse than no coverage log.
"""
from __future__ import annotations

import json
import os
from datetime import datetime, timezone
from pathlib import Path

#: Scalars worth keeping, by name. An allowlist rather than "every number in
#: `meta`", because `meta` also carries ANSWERS -- an optimum, a bound -- and
#: those are the caller's mathematics, not the size of their question.
SHAPE_KEYS = (
    "n", "count", "enumerated", "items", "size", "k", "degree", "depth",
    "variables", "vars", "rows", "columns", "nodes", "clauses", "atoms",
    "generators", "dimension", "cases", "iterations", "terms",
)

MAX_LINES = 5_000
MAX_BYTES = 1_024 * 1_024

ENV_OFF = "CERTO_NO_COVERAGE"
ENV_FILE = "CERTO_COVERAGE_FILE"


def enabled() -> bool:
    return os.environ.get(ENV_OFF, "").strip() not in ("1", "true", "yes", "on")


def data_dir() -> Path:
    """The user's data directory, not the working directory."""
    override = os.environ.get(ENV_FILE)
    if override:
        return Path(override).expanduser().parent
    if os.name == "nt":
        base = os.environ.get("LOCALAPPDATA") or (Path.home() / "AppData" / "Local")
    else:
        base = os.environ.get("XDG_DATA_HOME") or (Path.home() / ".local" / "share")
    return Path(base) / "certo"


def default_path() -> Path:
    override = os.environ.get(ENV_FILE)
    if override:
        return Path(override).expanduser()
    return data_dir() / "coverage.jsonl"


def shape_of(meta) -> dict:
    """The size of what was asked, and nothing else about it."""
    out = {}
    for key in SHAPE_KEYS:
        v = (meta or {}).get(key)
        if isinstance(v, bool):
            continue
        if isinstance(v, int) or (isinstance(v, float) and v == v):
            out[key] = v
    return out


def entry(res, source: str) -> dict:
    return {
        "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "command": res.command,
        "status": res.status.value,
        "engine": res.engine,
        "source": source,
        "shape": shape_of(getattr(res, "meta", None)),
        "certo": _version(),
    }


def _version() -> str:
    from . import __version__
    return __version__


def full(path: Path) -> bool:
    """Bounded, and the bound is a stop rather than a rotation."""
    try:
        st = path.stat()
    except OSError:
        return False
    if st.st_size >= MAX_BYTES:
        return True
    with path.open("r", encoding="utf-8") as fh:
        return sum(1 for _ in fh) >= MAX_LINES


def record(res, source: str, path=None) -> bool:
    """Record a non-conclusive result. True when a line was written.

    Conclusive results are not recorded: this is a map of what certo could not
    do, and a log of its successes would bury it.
    """
    try:
        if res is None or res.status.conclusive or not enabled():
            return False
        p = Path(path) if path else default_path()
        if p.exists() and full(p):
            return False
        p.parent.mkdir(parents=True, exist_ok=True)
        line = json.dumps(entry(res, source), ensure_ascii=False)
        with p.open("a", encoding="utf-8") as fh:
            fh.write(line + "\n")
        return True
    except Exception:  # noqa: BLE001
        # Never fail a command because a log could not be written.
        return False


def summary(path=None) -> dict:
    """What has accumulated. The reader the map will be built on.

    Deliberately small: counts by command and by status, and the span of time
    they cover. Ranking a coverage gap needs judgement about what the counts
    MEAN -- a `timeout` is a depth problem and an `out_of_theory` is a breadth
    one -- and that judgement is not made here.
    """
    p = Path(path) if path else default_path()
    out = {"path": str(p), "exists": p.exists(), "lines": 0,
           "by_command": {}, "by_status": {}, "first": None, "last": None,
           "full": False}
    if not p.exists():
        return out
    try:
        with p.open("r", encoding="utf-8") as fh:
            for raw in fh:
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    e = json.loads(raw)
                except ValueError:
                    continue
                out["lines"] += 1
                cmd, st, ts = e.get("command"), e.get("status"), e.get("ts")
                out["by_command"][cmd] = out["by_command"].get(cmd, 0) + 1
                out["by_status"][st] = out["by_status"].get(st, 0) + 1
                if ts:
                    out["first"] = ts if out["first"] is None else min(out["first"], ts)
                    out["last"] = ts if out["last"] is None else max(out["last"], ts)
    except OSError:
        return out
    out["full"] = full(p)
    return out
