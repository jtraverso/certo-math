"""synth with a template: find a FUNCTION, then prove it for every n.

The least linear bound f(n) = c0 + c1 n, with integer coefficients in [0, 9],
such that f(n) >= 2 n + 1 for n in [0, 10] -- and then, fixed, for every real
n >= 0. The template's coefficients are the implementation variables; the
result names the function found (`meta["functions"]`), the optimum is
certified (`synth_optimum`), and `--prove-candidate` proves it unbounded:

    certo synth examples/synth_template.py --prove-candidate
    certo verify out/synth_template.json
"""
import z3

from certo import Spec, SynthSpec
from certo import templates


def spec():
    n = z3.Int("n")
    nr = z3.Real("nr")
    f = templates.polynomial("f", [n], degree=1, lo=0, hi=9)
    return SynthSpec(
        title="the least linear f with f(n) >= 2n + 1",
        impl_vars=[], input_vars=[n], templates=[f],
        behavior=z3.And(n >= 0, n <= 10),
        correctness=f.expr >= 2 * n + 1,
        minimize=z3.Sum(f.vars),
        universal=lambda v: Spec(title="for every real n >= 0").assume(
            "domain", nr >= 0).claim(v["f_c0"] + v["f_c1"] * nr >= 2 * nr + 1),
    )
