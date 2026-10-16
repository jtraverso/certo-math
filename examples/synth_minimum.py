"""synth --minimize: the BEST threshold, not just one that works.

    find the least integer a in [0, 20] such that for every x in [0, 3]:
        access:   a >= x + 2
        payment:  a >= 2 x

CEGIS finds a candidate, then asks for a better one under `a < value`, until
no candidate exists. The certificate (`synth_optimum`) carries both halves:
the candidate that attains 6, and the refuted search for anything below it --
both verified, tied to the same contract. Each counterexample in the trace
says which obligation it breaks. Optimal within this template and its bounded
domain, which is what the scope says.

    certo synth examples/synth_minimum.py
    certo verify out/synth_minimum.json
"""
import z3

from certo import SynthSpec


def spec():
    a, x = z3.Ints("a x")
    return SynthSpec(
        title="the least threshold paying access and payment",
        impl_vars=[a],
        input_vars=[x],
        impl_constraints=z3.And(a >= 0, a <= 20),
        behavior=z3.And(x >= 0, x <= 3),
        correctness={"access": a >= x + 2, "payment": a >= 2 * x},
        minimize=a,
    )
