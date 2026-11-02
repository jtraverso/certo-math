"""synth: a model, and a program that knows the REAL problem.

The formulas say: find a gain `g` in 0..10 with g * x >= x for every load x in
0..5 -- any g >= 1 will do. The real system has a margin the model leaves out:
a gain under 3 fails on the bench. That knowledge lives in a program, not in
a formula, so it is the DOMAIN VERIFIER: called on every candidate the model
accepts, it answers valid, or invalid with a counterexample and a reason.

A rejected candidate is excluded and the search goes on; the trace keeps each
call's input hash, result hash and the verifier's version. The answer is
g = 3, and `verify` says plainly that the bench was not re-run.

    certo synth examples/synth_domain_verifier.py --cert out/synth_domain.json
    certo verify out/synth_domain.json
"""
import z3

from certo import SynthSpec

g, x = z3.Ints("g x")


def bench(candidate):
    """The real problem: a gain below 3 does not hold the load."""
    if candidate["g"] < 3:
        return {"valid": False, "reason": "the margin fails on the bench"}
    return True


bench.version = "bench-2026.11"


def spec():
    return SynthSpec(
        title="a gain the model accepts AND the bench does",
        impl_vars=[g], input_vars=[x],
        impl_constraints=z3.And(g >= 0, g <= 10),
        behavior=z3.And(x >= 0, x <= 5),
        correctness=g * x >= x,
        domain_verifier=bench,
    )
