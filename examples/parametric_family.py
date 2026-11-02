"""parametric: a program FEASIBLE on a whole interval, by a family of bases.

    x + y  = 1
    x      >= t - 1/2          x, y >= 0,   t in [0, 1]

No single formula serves the interval. For t <= 1/2 the basis {y, r2} gives
x = 0, y = 1 (the row r2 slack); for t >= 1/2 the basis {x, y} gives
x = t - 1/2, y = 3/2 - t. They meet at the FRONTIER t = 1/2, where x = 0 in
both.

Each piece names its basis; certo solves the tight rows exactly (Cramer, with
Bareiss' fraction-free elimination), checks A(t) N(t) = D(t) d(t) as a
polynomial identity, and every sign -- the denominator, N >= 0, each slack --
by Bernstein coefficients on the piece's region. The two pieces carry
`1/2 - t >= 0` and `t - 1/2 >= 0`: a frontier and its opposite, so together
they cover the interval, and `verify` walks that cover.

    certo parametric examples/parametric_family.py --cert out/pfamily.json
    certo verify out/pfamily.json
"""
from fractions import Fraction

from certo import ParametricSpec
from certo.polynomials import Poly

RING = ("t",)
t = Poly.var(RING, "t")
K = lambda c: Poly.const(RING, c)  # noqa: E731
HALF = K(Fraction(1, 2))


def spec():
    return ParametricSpec(
        title="feasible for every t in [0, 1], two bases",
        parameters={"t": 0},
        box={"t": (0, 1)},
        objective={"x": K(1)},
        constraints=[
            ("e1", {"x": K(1), "y": K(1)}, "==", K(1)),
            ("r2", {"x": K(1)}, ">=", t - HALF),
        ],
        pieces=[
            {"basis": ["y", "r2"], "region": [("below", HALF - t)]},
            {"basis": ["x", "y"], "region": [("above", t - HALF)]},
        ],
        # and the optimum of max x is at least t - 1/2 on every piece
        claim=t - HALF,
    )
