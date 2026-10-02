"""Compile every Lean file certo can emit, against a real Mathlib.

"It should compile" is the claim most likely to be wrong and the one nobody
should have to take on trust from a program that writes text. Worse, the
failure that actually costs a user time is not a file that fails to compile --
it is one that compiles and says nothing, which is why `hollow_count` exists.
This runs the other half: the file has to elaborate.

KEPT OUT OF THE FAST SUITE, AND NOT A RELEASE GATE. Importing Mathlib costs
minutes per file, depends on a toolchain version, and fails in ways that say
nothing about whether certo's mathematics is right. certo's job is the step
BEFORE the proof assistant; wiring its release cycle to one would be adopting
the cost of a different tool without taking on its work.

This is for the person ADDING an exporter, run once, by hand -- and the rule
it enforces is in `leanexport`: emit only a small self-contained artefact whose
content is the certificate's data, and refuse rather than guess.

    $ python tests/run_lean.py                     # finds a project, or says so
    $ CERTO_LEAN_PROJECT=/path/to/proj python tests/run_lean.py

WITHOUT A PROJECT IT SAYS SO AND EXITS 0. A missing toolchain is not a
failing export, and reporting it as one would train everybody to ignore the
result -- but it is not a pass either, and the output says which of the two
happened every time.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "examples"))

#: Places a Lean project with Mathlib built tends to be, in order. The
#: environment variable wins: a machine with several is the normal case.
CANDIDATES = (
    ROOT / ".github" / "lean",
    ROOT.parent / "certo-leantest",
)


def project() -> Path | None:
    named = os.environ.get("CERTO_LEAN_PROJECT")
    roots = ([Path(named)] if named else []) + list(CANDIDATES)
    for p in roots:
        if (p / "lakefile.toml").exists() or (p / "lakefile.lean").exists():
            built = p / ".lake" / "packages" / "mathlib" / ".lake" / "build"
            if built.exists():
                return p
    return None


#: (example, the command whose engine produces a certificate an exporter
#: knows). Routing is by SPEC TYPE, the same way `ask` does it: hardcoding an
#: engine per example is how this first ran `core` over a `MultiSpec`.
#: certo emits Lean for a LINEAR Farkas certificate and nothing else, so this
#: is short by design rather than by omission. A spec whose certificate has no
#: exporter is skipped, not failed.
SPECS = (
    "farkas_linear.py",
    "affine_semigroup.py",
)


def _cases(limits):
    """One certificate per exporter that has one, from the real examples."""
    from certo import leanexport
    from certo.routing import prepared, runner_for
    from certo.spec import load_spec

    out = []
    for name in SPECS:
        spec = load_spec(str(ROOT / "examples" / name))
        _command, run = runner_for(spec)
        if run is None:
            continue
        cert = run(prepared(spec), limits).certificate
        if cert is not None and cert.kind in leanexport.EXPORTERS:
            out.append((name, cert))
    return out


def main() -> int:
    from certo import Limits, leanexport

    where = project()
    if where is None:
        print("no Lean project with Mathlib built was found.")
        print("  set CERTO_LEAN_PROJECT to one, or run `lake exe cache get`")
        print("  in a project that requires mathlib.")
        print("\nNOT RUN -- which is not the same as passing.")
        return 0

    print("project: {}".format(where))
    limits = Limits(timeout_ms=300_000)
    tmp = Path(tempfile.mkdtemp(prefix="certo_lean_"))
    failures = 0
    cases = _cases(limits)

    for name, cert in cases:
        data = cert.to_dict()
        data["digest"] = cert.digest()
        text = leanexport.EXPORTERS[cert.kind](data)
        path = tmp / "{}.lean".format(name.capitalize())
        path.write_text(text, encoding="utf-8")

        hollow = leanexport.hollow_count(text)
        report = leanexport.check(path, project=str(where))
        if not report.get("ran"):
            print("[??] {:<20} {} did not run: {}".format(
                name, cert.kind, report.get("reason")))
            failures += 1
            continue
        if report.get("ok"):
            print("[ok] {:<20} {:<22} {} line(s), {} hollow, {} sorry".format(
                name, cert.kind, len(text.splitlines()), hollow,
                text.count("sorry") - 1))
        else:
            failures += 1
            print("[XX] {:<20} {}".format(name, cert.kind))
            for line in (report.get("output") or "").splitlines()[:8]:
                print("       " + line)

    print("\n{}/{} exports compile".format(len(cases) - failures, len(cases)))
    _ = json
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
