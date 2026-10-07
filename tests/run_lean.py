"""Compile every Lean file certo can emit, against a real Mathlib.

"It should compile" is the claim most likely to be wrong and the one nobody
should have to take on trust from a program that writes text. Worse, the
failure that actually costs a user time is not a file that fails to compile --
it is one that compiles and says nothing, which is why `hollow_count` exists.
This runs the other half: the file has to elaborate.

KEPT OUT OF THE FAST SUITE. Importing Mathlib costs minutes per file, depends
on a toolchain version, and fails in ways that say nothing about whether
certo's mathematics is right. So it runs where a toolchain is: in CI's `lean`
job, and before a tag with `python tests/prerelease.py --lean`. Every exporter
must have a case here (a missing one fails), and a file that compiles with
warnings counts as failing -- two exporters had never been compiled at all.

The rule it enforces is in `leanexport`: emit only a small self-contained
artefact whose content is the certificate's data, and refuse rather than guess.

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


#: The examples whose certificates have an exporter. Routing is by SPEC TYPE,
#: the way `ask` does it.
SPECS = (
    "farkas_linear.py",
    "affine_semigroup.py",
)


def _generated(limits):
    """Cases the examples do not reach, each the shape that broke or could:
    a Farkas combination of 170 rows (Lean's default recursion depth stopped
    one of 169), an exact LP bound, an infeasible LP read as hypotheses
    whose contradiction is the statement `False`, ideal identities over a field
    and over every commutative ring and an inconsistent system, the Smith form of an integer matrix, a
    unimodular cone in dimension 4 (all four semigroup stages) and a
    semigroup with a generator in the cone of the others (stage 3 leaves it
    out)."""
    import z3

    from certo import IdealSpec, LPSpec, MatrixSpec, SemigroupSpec, Spec
    from certo.engines import algebra, farkas, lp

    out = []
    n = 170
    xs = z3.Reals(" ".join("x%d" % i for i in range(n)))
    s = Spec().assume("h0", xs[0] >= 1)
    for i in range(n - 1):
        s.assume("h%d" % (i + 1), xs[i + 1] >= xs[i] + 1)
    s.claim(xs[n - 1] >= n)
    out.append(("farkas_170_rows", farkas.farkas(s, limits).certificate))

    m = LPSpec(sense="max")
    m.variable("a", 0, None)
    m.variable("b", 0, None)
    m.objective({"a": 1, "b": 1})
    m.constraint({"a": 1}, "<=", 2, name="cap_a")
    m.constraint({"a": 1, "b": 1}, "<=", 3, name="both")
    out.append(("lp_dual_bound", lp.opt(m, limits).certificate))
    m.constraint({"a": 1, "b": 1}, ">=", 4, name="too_much")
    out.append(("farkas_infeasible_lp", farkas.farkas(m, limits).certificate))

    x, y, z = z3.Reals("x y z")
    out.append(("ideal_member_rational", algebra.ideal(IdealSpec(
        variables=["x", "y"], equations=[x * y - 1, x - z3.Q(1, 3) * y],
        claim=y * y - 3), limits).certificate))
    out.append(("ideal_member_integral", algebra.ideal(IdealSpec(
        variables=["x", "y", "z"], equations=[x * y - z, y - 2],
        claim=2 * x - z), limits).certificate))
    out.append(("ideal_inconsistent", algebra.ideal(IdealSpec(
        variables=["x", "y"], equations=[x * y - 1, x], claim=None),
        limits).certificate))
    out.append(("smith_3x3", algebra.integer_matrix(MatrixSpec(
        matrix=[[2, 4, 4], [-6, 6, 12], [10, -4, -16]], question="smith"),
        limits).certificate))

    out.append(("semigroup_unimodular_4d", algebra.affine_semigroup(SemigroupSpec(
        generators={"e0": (1, 0, 0, 0), "e1": (1, 1, 0, 0), "e2": (1, 1, 1, 0),
                    "e3": (1, 1, 1, 1)}, points={"p": (4, 3, 2, 1)}),
        limits).certificate))
    out.append(("semigroup_partial", algebra.affine_semigroup(SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        points={"q": (2, 1)}), limits).certificate))
    return out


def _cases(limits):
    """One certificate per exporter, from the examples and generated."""
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
    out += [(n, c) for n, c in _generated(limits)
            if c is not None and c.kind in leanexport.EXPORTERS]
    covered = {c.kind for _n, c in out}
    missing = sorted(set(leanexport.EXPORTERS) - covered)
    if missing:
        raise SystemExit("no case for exporter(s): " + ", ".join(missing))
    return out


def main() -> int:
    from certo import Limits, leanexport

    where = project()
    if where is None:
        print("no Lean project with Mathlib built was found.")
        print("  set CERTO_LEAN_PROJECT to one, or run `lake exe cache get`")
        print("  in a project that requires mathlib.")
        print("\nNOT RUN -- which is not the same as passing.")
        # Where Lean is the point of the job, its absence is a failure.
        return 1 if os.environ.get("CERTO_LEAN_REQUIRED") else 0

    print("project: {}".format(where))
    limits = Limits(timeout_ms=300_000)
    tmp = Path(tempfile.mkdtemp(prefix="certo_lean_"))
    failures = 0
    cases = _cases(limits)

    # And each exporter's output once more as `export --theorem NAME` writes
    # it: a theorem with a dotted name, or a renamed namespace, has to
    # elaborate too -- the rename is text, and text is what this checks.
    seen, named = set(), []
    for name, cert in cases:
        if cert.kind not in seen:
            seen.add(cert.kind)
            named.append(("named_" + name, cert, "CertoNamed.case_" + cert.kind))
    jobs = [(n, c, None) for n, c in cases] + named

    for name, cert, theorem in jobs:
        data = cert.to_dict()
        data["digest"] = cert.digest()
        text = leanexport.EXPORTERS[cert.kind](data)
        if theorem:
            text = leanexport.named(text, theorem)
        path = tmp / "{}.lean".format(
            name.replace(".py", "").replace(".", "_").capitalize())
        path.write_text(text, encoding="utf-8")

        hollow = leanexport.hollow_count(text)
        report = leanexport.check(path, project=str(where))
        if not report.get("ran"):
            print("[??] {:<20} {} did not run: {}".format(
                name, cert.kind, report.get("reason")))
            failures += 1
            continue
        warned = [l for l in (report.get("output") or "").splitlines()
                  if "warning" in l]
        if report.get("ok") and not warned:
            print("[ok] {:<24} {:<18} {} line(s), {} hollow, {} sorry".format(
                name, cert.kind, len(text.splitlines()), hollow,
                sum(1 for l in text.splitlines() if "sorry" in l.split("--")[0]
                    and not l.lstrip().startswith(("/-", "-/")))))
        elif report.get("ok"):
            # It compiles, and Lean has something to say: a release should
            # not ship Lean that warns, so this counts.
            failures += 1
            print("[!!] {:<24} {} compiles WITH warnings".format(name, cert.kind))
            for line in warned[:8]:
                print("       " + line)
        else:
            failures += 1
            print("[XX] {:<20} {}".format(name, cert.kind))
            for line in (report.get("output") or "").splitlines()[:8]:
                print("       " + line)

    print("\n{}/{} exports compile".format(len(jobs) - failures, len(jobs)))
    _ = json
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
