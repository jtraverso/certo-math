"""sweep over a RANGE of sizes, where each size's predicate certifies.

Three levels, which is the shape that shows what a nested artefact does and
does not carry:

    sweep_range          one entry per n
      └─ sweep           one verdict per graph on n vertices
           └─ lp_dual    the exact dual for the graph that decided it

The predicate asks whether the fractional K3-packing of a graph is an INTEGER,
and returns the exact dual either way -- so the sweep is `certified` rather
than `reproducible`, and the range's entries are certificates all the way
down rather than a record that something once ran.

    certo sweep examples/sweep_range_nested.py --range 3:5 --cert out/nested.json
    certo verify out/nested.json

WHAT THIS EXISTS TO PIN. A user auditing a nested range wrote their own
checker because the top-level report did not say what the inner certificates
established, and saw a warning about the predicate not being re-run on
artefacts that carry their own proofs. Both are about what survives one level
of nesting, and neither is visible on a flat sweep -- so the example is the
nested one.
"""
from fractions import Fraction
from itertools import combinations

from certo import LPSpec, Outcome, SweepSpec
from certo.engines import lp

LO, HI = 3, 5


def packing_lp(g):
    """The graph's fractional K3-packing, edges as the shared resource."""
    spec = LPSpec(sense="max", title="K3 packing on n={}".format(g.n))
    triangles = [s for s in combinations(range(g.n), 3)
                 if all(g.has_edge(a, b) for a, b in combinations(s, 2))]
    if not triangles:
        return None, []
    for s in triangles:
        spec.variable("K3_" + "_".join(map(str, s)))
    spec.objective({"K3_" + "_".join(map(str, s)): 1 for s in triangles})
    for a, b in combinations(range(g.n), 2):
        using = ["K3_" + "_".join(map(str, s)) for s in triangles
                 if a in s and b in s]
        if using:
            spec.constraint({n: 1 for n in using}, "<=", 1,
                            name="e{}_{}".format(a, b))
    return spec, triangles


def integral_packing(g):
    """Is the fractional optimum an integer? The dual says what it is."""
    spec, triangles = packing_lp(g)
    if not triangles:
        # No triangle: the optimum is zero, which is an integer, and there is
        # nothing to certify. Said rather than dressed as a certified pass.
        return Outcome(True, detail="no triangle on n={}".format(g.n))
    res = lp.opt(spec)
    if res.certificate is None or not res.meta.get("exact"):
        return Outcome(None, detail="the LP did not certify exactly")
    value = Fraction(res.meta["objective"])
    return Outcome(value.denominator == 1, cert=res.certificate,
                   detail="optimum {}".format(value), value=value)


def spec():
    return SweepSpec(
        n=LO,
        predicate=integral_packing,
        title="is the fractional K3-packing integral, for every graph on n?",
    )
