"""Run what CI runs, here, before a tag: a CLEAN checkout, CI's order, no out/.

Every failed release so far passed here and failed on a clean runner: a test
that read `out/` (which only the examples make), doctor tests that read this
machine, a file nobody had `git add`ed. They passed because THIS checkout has
all of that lying around. So this builds a fresh worktree of exactly what
would be tagged -- HEAD, plus uncommitted changes to tracked files, and
nothing untracked, which is how a forgotten `git add` shows up -- and runs
the suites in CI's order inside it:

    smoke mcp i18n extras adversarial determinism   (as `publish.yml` does)
    run_examples                                    (its own job in CI)
    run_lean, with --lean                           (every exporter, Mathlib)

    $ python tests/prerelease.py            # the suites and the examples
    $ python tests/prerelease.py --lean     # and every exporter against Mathlib

Exit 0 only when every step passed. It is not a substitute for CI -- one
machine, one Python, one OS -- but it removes the failures that were never
about the platform at all.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SUITES = ("smoke", "mcp", "i18n", "extras", "adversarial", "determinism")


def _git(*args, cwd=ROOT) -> str:
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                          text=True, check=True).stdout.strip()


def _snapshot() -> str:
    """HEAD, or HEAD plus the uncommitted changes to tracked files."""
    stash = _git("stash", "create")
    return stash or _git("rev-parse", "HEAD")


def _run(label, cmd, cwd, env) -> bool:
    t0 = time.perf_counter()
    p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    tail = [l for l in (p.stdout + p.stderr).splitlines()
            if "[XX]" in l or "passed" in l or "examples ran" in l
            or "exports compile" in l or "NOT RUN" in l]
    # "NOT RUN" exits 0 in run_lean -- a missing toolchain is not a failing
    # export -- but a pre-release check that was asked for Lean and got none
    # has not passed.
    ok = p.returncode == 0 and not any("NOT RUN" in l for l in tail)
    print("[{}] {:<14} {:>6.0f}s  {}".format("ok" if ok else "XX", label,
                                             time.perf_counter() - t0,
                                             tail[-1] if tail else ""), flush=True)
    if not ok:
        for line in [l for l in tail if "[XX]" in l][:12]:
            print("       " + line)
        if not any("[XX]" in l for l in tail):
            # Failed with no summary line: it crashed or was killed. Its last
            # words are the only clue, and they used to be thrown away.
            last = (p.stdout + p.stderr).strip().splitlines()[-15:]
            print("       exit code {}; last output:".format(p.returncode))
            for line in last:
                print("       | " + line[:200])
    return ok


def main(argv) -> int:
    lean = "--lean" in argv
    untracked = _git("ls-files", "--others", "--exclude-standard")
    if untracked:
        print("untracked, and so NOT in the checkout being tested (git add?):")
        for line in untracked.splitlines()[:20]:
            print("  " + line)
    sha = _snapshot()
    tmp = Path(tempfile.mkdtemp(prefix="certo_prerelease_"))
    wt = tmp / "wt"
    _git("worktree", "add", "--detach", str(wt), sha)
    env = dict(os.environ, PYTHONPATH=str(wt / "src"),
               CERTO_COVERAGE_FILE=str(tmp / "coverage.jsonl"))
    # The worktree has no Mathlib built beside it; the project next to THIS
    # checkout does, and `run_lean` would otherwise not find it and not run.
    if lean and "CERTO_LEAN_PROJECT" not in env:
        for cand in (ROOT / ".github" / "lean", ROOT.parent / "certo-leantest"):
            if (cand / ".lake" / "packages" / "mathlib" / ".lake" / "build").exists():
                env["CERTO_LEAN_PROJECT"] = str(cand)
                break
    print("checkout {} at {}".format(sha[:12], wt), flush=True)
    results = []
    try:
        for t in SUITES:
            results.append(_run(t, [sys.executable, "tests/test_{}.py".format(t)],
                                wt, env))
        results.append(_run("examples", [sys.executable, "tests/run_examples.py"],
                            wt, env))
        if lean:
            results.append(_run("lean", [sys.executable, "tests/run_lean.py"],
                                wt, env))
    finally:
        _git("worktree", "remove", "--force", str(wt))
    print("\n{} of {} steps passed".format(sum(results), len(results)))
    return 0 if all(results) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
