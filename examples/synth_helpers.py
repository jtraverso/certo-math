"""synth (CEGIS) with HELPERS: a capacity k such that every load can be split.

Shape of the problem:

    THERE EXISTS k  FOR ALL loads (x, y, b)  THERE EXIST shares (h1, h2) :
        h1 + h2 = x + y*b,  0 <= h1, h2 <= k

The helpers are the adaptive part -- a different split for every load -- and
the order of the quantifiers is what makes it a synthesis rather than a
check. Since 0.40 the counterexample search asks no quantified query: it
looks for a load no KNOWN split saves, then for a split that saves it, and
the splits it finds are written into the certificate (`helper_witnesses`).
`verify` checks that every load is saved by one of them, with one
quantifier-free query.

    certo synth examples/synth_helpers.py --trace
"""
import z3

from certo import SynthSpec


def spec():
    k = z3.Int("k")                     # what we are looking for
    x, y, b = z3.Ints("x y b")          # every load
    h1, h2 = z3.Ints("h1 h2")           # a split, chosen per load

    return SynthSpec(
        title="a capacity that splits every load in two",
        impl_vars=[k],
        input_vars=[x, y, b],
        helper_vars=[h1, h2],
        impl_constraints=z3.And(k >= 0, k <= 9),
        behavior=z3.And(x >= 5, x <= 8, y >= 5, y <= 8, b >= 0, b <= 1),
        correctness=z3.And(h1 >= 0, h2 >= 0, h1 <= k, h2 <= k,
                           h1 + h2 == x + y * b),
    )
