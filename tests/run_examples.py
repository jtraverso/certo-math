"""Run every example, and verify the certificate it produces.

The examples are the documentation. Documentation that no longer runs is worse
than none: a spec that stopped working still reads convincingly.

Each entry says which command the example is for, because that is the one
thing a spec file does not carry -- `spec()` returns an object, and the
command follows from its type, but the flags do not. Anything not listed here
is reported at the end rather than silently skipped, so a new example cannot
join the repository without joining this file.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EX = ROOT / "examples"
OUT = ROOT / "out"

# (example, command, extra flags[, expected exit code]). A command that makes
# no certificate -- `lint` -- is listed in NO_CERT below and checked on its
# exit code alone, which for a linter IS the result.
CASES = [
    ("lint_vacuous_regime.py", "lint", [], 1),
    ("regime_nonempty.py", "check", ["--hypotheses-only"]),
    ("refute_density.py", "prove", []),
    ("calibrate_density.py", "sweep", []),
    ("amgm.py", "prove", []),
    ("pigeonhole.py", "cases", []),
    ("core_matrix.py", "core", []),
    ("hypothesis_audit.py", "audit", []),
    ("symmetry_reduction.py", "reduce", []),
    ("parametric_symmetry.py", "reduce", ["--parametric"]),
    ("integer_matrix.py", "matrix", []),
    ("interchange_matrix.py", "matrix", []),
    ("toric_cone.py", "cone", []),
    ("linear_system.py", "solve", []),
    ("equitable_quotient.py", "quotient", []),
    ("farkas_linear.py", "farkas", []),
    ("farkas_nonlinear.py", "farkas", ["--nonlinear"]),
    ("farkas_named_square.py", "farkas", ["--nonlinear"]),
    ("bounds_constant.py", "bounds", []),
    ("order_decay.py", "order", []),
    ("ideal_inconsistent.py", "ideal", []),
    ("eliminate_parameter.py", "eliminate", []),
    ("parametric_bound.py", "parametric", []),
    ("parametric_cover.py", "parametric", []),
    ("parametric_orbits.py", "parametric", []),
    ("ratio_window.py", "ratio", []),
    ("first_moment.py", "moment", []),
    ("first_entry.py", "entry", []),
    ("peak_residues.py", "peak", []),
    ("packing_with_loads.py", "opt", []),
    ("clique_partition.py", "cover", []),
    ("no_decomposition.py", "exists", []),
    ("family_max.py", "family", []),
    ("cover_optimize.py", "cover", []),
    ("sos_quartic.py", "sos", []),
    ("number_mersenne.py", "number", []),
    ("induct_sum.py", "induct", []),
    ("lp_mixed_packing.py", "opt", []),
    ("mixed_design.py", "mixed", []),
    ("walkthrough.py", "opt", ["--gap"]),
    ("walkthrough_ideal.py", "ideal", []),
    ("walkthrough_proof.py", "compose", []),
    ("packing_mixed.py", "opt", ["--by-type"]),
    ("synth_constant.py", "synth", []),
    ("synth_prove_identity.py", "synth", ["--prove-candidate"]),
    ("ramsey.py", "cases", []),
    ("propositional.py", "cases", []),
    ("ramsey_k5.py", "cases", []),
    ("mus_ramsey.py", "shrink", []),
    ("sweep_simplicial.py", "sweep", []),
    ("sweep_certified_lp.py", "sweep", []),
    ("sweep_orbits.py", "sweep", []),
    ("setfamily_sweep.py", "sweep", ["--witnesses"]),
    ("orbits_witnessed.py", "sweep", []),
    ("shrink_nonchordal.py", "shrink", []),
    ("bisect_constant.py", "bisect", []),
    ("bisect_ramsey.py", "bisect", []),
    ("compose_proof.py", "compose", []),

    # 0.10: the six the feedback asked for
    ("variable_range.py", "range", ["--var", "a"]),
    ("dependency_cycle.py", "cycle", []),
    ("order_relations.py", "order", []),
    ("overdetermined.py", "eliminate", []),
    ("counting_bound.py", "prove", []),
    ("lean_binding.py", "bind", []),

    # The recipe in docs/CASES.md. A recipe nobody runs is a recipe that rots,
    # and this one exists because a team could not find the encoding.
    ("smallest_deletion.py", "bisect", []),

    # A nested range: sweep_range over sweep over lp_dual. It exists because
    # what a nested artefact carries -- and what it loses -- is invisible on a
    # flat one, and that is where two defects lived.
    ("sweep_range_nested.py", "sweep", ["--n-range", "3..4"]),
]

#: Commands that report rather than certify. `status` is not here because it
#: takes a directory rather than a spec; it runs once at the end, over
#: everything the other examples just produced.
NO_CERT = {"lint"}

# compose_proof.py reads two certificates that are output, not source, so they
# have to exist before it runs. This is the `make examples` the backlog wants,
# in the one place that already knows the order.
PREREQS = {
    # The walkthrough's proof reads the two certificates the earlier steps
    # produce, which is the point of it -- so they have to exist first.
    "walkthrough_proof.py": [
        ("opt", "walkthrough.py", ["--gap", "--cert", "out/gap.json"]),
        ("mixed", "walkthrough.py",
         ["--prove-optimal", "--max-nodes", "30000",
          "--cert", "out/optimal.json"]),
    ],
    "compose_proof.py": [
        ("cases", "ramsey.py", ["--cert", "out/r33_k6.json"]),
        ("cases", "ramsey_k5.py", ["--cert", "out/r33_k5.json"]),
    ],
    # `bind` reads the certificate it is tying to a declaration, so that
    # certificate has to exist -- and carry the provenance the binding reads
    # the hypothesis out of.
    "lean_binding.py": [
        ("prove", "counting_bound.py", ["--cert", "out/counting_bound.json"]),
    ],
}


#: The suite tests the tree it lives in, not whatever happens to be
#: installed. Without this a half-finished `pip install` -- which on Windows
#: is what happens whenever the MCP server holds `certo-mcp.exe` open -- makes
#: every example fail for a reason that has nothing to do with the examples.
ENV = dict(os.environ, PYTHONPATH=str(ROOT / "src"))


def run(args, label, expect=None):
    p = subprocess.run([sys.executable, "-m", "certo.cli", *args],
                       cwd=ROOT, capture_output=True, text=True, env=ENV,
                       encoding="utf-8", errors="replace", timeout=900)
    if expect is not None:
        # An example that exists to be REJECTED has to be rejected: a linter
        # whose failing case starts passing is the failure that hides itself.
        if p.returncode != expect:
            print("[XX] {} exited {}, expected {}\n{}".format(
                label, p.returncode, expect, (p.stdout + p.stderr)[-800:]))
            return False
        return True
    # Exit 2 is "inconclusive", which several examples are ON PURPOSE -- a
    # sweep that refutes, a bisect that brackets. Only 1 and 3 are failures.
    if p.returncode in (1, 3):
        print("[XX] {}\n{}".format(label, (p.stdout + p.stderr)[-800:]))
        return False
    return True


def _tracked_examples():
    """The example files git actually carries, or None outside a checkout."""
    try:
        p = subprocess.run(["git", "ls-files", "examples/*.py"], cwd=ROOT,
                           capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    if p.returncode:
        return None
    return {line.split("/")[-1] for line in p.stdout.split() if line}


def _declared_against_emitted(produced):
    """`KIND_OF` and `TIER`, against what the commands actually emitted.

    Both are DECLARED, because an engine emits different kinds on different
    paths and a boolean cannot say the true thing about `prove`: a `model` on
    a refutation re-checks by substitution, an `unsat_core` on a proof only
    when the core is linear.

    Declared and unchecked is how the old `SOLVER_FREE` set came to be wrong
    for six commands -- `opt` among them, whose `lp_dual` is the most
    re-checked certificate here. Every error ran the same way: it UNDERSTATED
    what is solver-free, which sends a reader to archive a weaker artefact
    than the one they already hold. A user comparing tools reported
    `opt`/`ratio`/`farkas` as solver-free and was right while the table said
    otherwise.

    This is the one place that runs every command for real, so it is where the
    declaration meets the emission.
    """
    from certo import routing

    out = []
    for cmd, seen in sorted(produced.items()):
        kinds = {k for k, _sf in seen if k}
        want_kind = routing.KIND_OF.get(cmd)
        allowed = ({want_kind} if isinstance(want_kind, str)
                   else set(want_kind or ()))
        if allowed and kinds and not (kinds <= allowed):
            out.append((cmd, "KIND_OF", "/".join(sorted(allowed)),
                        ", ".join(sorted(kinds - allowed))))

        tier = routing.TIER.get(cmd)
        if tier in (None, routing.DEPENDS):
            continue
        flags = {bool(sf) for _k, sf in seen}
        want = tier == routing.YES
        if flags and flags != {want}:
            out.append((cmd, "TIER", tier,
                        "solver_free=" + ",".join(sorted(map(str, flags)))))
    return out


def main() -> int:
    OUT.mkdir(exist_ok=True)
    listed = {case[0] for case in CASES}
    # Files the repository does not carry (a contributor's local work) would
    # show up here as "not covered" every run, which is noise about something
    # this file cannot cover anyway.
    tracked = _tracked_examples()
    present = {p.name for p in EX.glob("*.py")
               if tracked is None or p.name in tracked}
    missing = sorted(present - listed)

    failures = 0
    #: command -> the (kind, solver_free) of every certificate it emitted,
    #: so the declarations can be met with what actually came out.
    produced: dict = {}
    for case in CASES:
        name, command, flags = case[0], case[1], case[2]
        expect = case[3] if len(case) > 3 else None
        if name not in present:
            print("[XX] {} is listed here but not in examples/".format(name))
            failures += 1
            continue
        for pre_cmd, pre_name, pre_flags in PREREQS.get(name, []):
            run([pre_cmd, "examples/" + pre_name, *pre_flags],
                "prereq {}".format(pre_name))

        label = "{} {}".format(command, name)
        if command in NO_CERT:
            if run([command, "examples/" + name, *flags], label, expect):
                print("[ok] {:<10} {}".format(command, name))
            else:
                failures += 1
            continue

        cert = OUT / (name[:-3] + ".json")
        ok = run([command, "examples/" + name, *flags, "--cert", str(cert)],
                 label, expect)
        if not ok:
            failures += 1
            continue
        if cert.exists():
            payload = json.loads(cert.read_text(encoding="utf-8"))
            produced.setdefault(command, []).append(
                (payload.get("kind"), payload.get("solver_free")))
        if cert.exists() and not run(["verify", str(cert)],
                                     "verify {}".format(cert.name)):
            failures += 1
        else:
            print("[ok] {:<10} {}".format(command, name))

    # Last, over everything the run just produced: `status` has to be able to
    # read the whole output directory. It is the one command whose input is
    # the other commands, so this is the only place it can be exercised for
    # real rather than against a directory built to suit it.
    if not run(["status", str(OUT)], "status out/"):
        failures += 1
    else:
        print("[ok] {:<10} {}".format("status", "out/"))

    if missing:
        # Not a failure, but it must not be silent: an example nobody runs is
        # an example nobody notices breaking.
        print("\nNOT COVERED by this file: " + ", ".join(missing))

    wrong = _declared_against_emitted(produced)
    for cmd, what, said, got in wrong:
        print("[XX] {} declares {}={} and emitted {}".format(
            cmd, what, said, got))
    failures += len(wrong)

    print("\n{}/{} examples ran and verified".format(
        len(CASES) + 1 - failures, len(CASES) + 1))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
