"""Many specs, one process: `certo batch COMMAND DIR`.

A user certified 179 lemma pieces as 179 processes, and paid the interpreter,
z3 and the imports 179 times for twenty milliseconds of work each. This runs
every spec in a directory through `api.run` -- the in-process entry point, so
each certificate is self-checked exactly as one run at a time would be -- and
writes one certificate per spec, named after it.

`jobs=N` spreads the specs over N worker processes, each paying the start-up
once. Results come back in the directory's order either way, so two runs of
one batch print the same table.

Nothing is aggregated into a claim. A batch is many separate runs, each with
its own verdict and certificate; joining boxes into one statement is
`atlas`, and checking that a set was certified exactly once is
`status --manifest`.
"""
from __future__ import annotations

import time
from pathlib import Path


def specs_in(directory, pattern="*.py") -> list:
    """The spec files of a directory, in a fixed order."""
    root = Path(directory)
    return sorted(str(p) for p in root.glob(pattern) if p.is_file())


def run_one(job) -> dict:
    """One spec, run and written. Never raises: an error is a row."""
    command, path, out_dir, timeout_ms, gz = job
    from . import api, store
    from .limits import Limits
    from .spec import load_spec

    t0 = time.perf_counter()
    row = {"spec": path}
    try:
        spec = load_spec(path)
        res = api.run(command, spec, limits=Limits(timeout_ms=timeout_ms),
                      spec_path=path)
    except Exception as e:  # noqa: BLE001 -- one bad spec is one bad row
        row.update(status="error", verdict=None,
                   error="{}: {}".format(type(e).__name__, e),
                   ms=round((time.perf_counter() - t0) * 1000, 1))
        return row
    row.update(status=res.status.value, verdict=res.verdict.value,
               detail=(res.detail or "")[:300],
               ms=round((time.perf_counter() - t0) * 1000, 1))
    if res.certificate is not None:
        dest = Path(out_dir) / (Path(path).stem + (".json.gz" if gz else ".json"))
        store.write_certificate(res.certificate, str(dest))
        row["certificate"] = str(dest)
        row["kind"] = res.certificate.kind
    return row


def run(command, files, out_dir, jobs=1, timeout_ms=60_000, gz=False,
        on_row=None) -> list:
    """Every file through `command`; rows in the files' order."""
    Path(out_dir).mkdir(parents=True, exist_ok=True)
    work = [(command, f, str(out_dir), timeout_ms, gz) for f in files]
    rows = []
    if jobs <= 1 or len(work) <= 1:
        for job in work:
            rows.append(run_one(job))
            if on_row:
                on_row(rows[-1])
        return rows
    from concurrent.futures import ProcessPoolExecutor
    from concurrent.futures.process import BrokenProcessPool

    # A worker that dies at start-up -- a `site` hook does that to a share of
    # interpreter starts on some machines -- breaks the whole pool. What it
    # left undone is run here, in this process, rather than lost or reported
    # as an error of the spec's.
    done = {}
    try:
        with ProcessPoolExecutor(max_workers=jobs) as ex:
            futures = [ex.submit(run_one, job) for job in work]
            for i, fut in enumerate(futures):
                try:
                    done[i] = fut.result()
                except BrokenProcessPool:
                    break
    except BrokenProcessPool:
        pass
    for i, job in enumerate(work):
        row = done.get(i) or run_one(job)
        rows.append(row)
        if on_row:
            on_row(row)
    return rows


def summary(rows) -> dict:
    out = {"specs": len(rows), "errors": 0}
    for r in rows:
        if r["status"] == "error":
            out["errors"] += 1
        else:
            out[r["verdict"]] = out.get(r["verdict"], 0) + 1
    return out
