"""nonneg for `construction_charts.json`: a bound in NEW coordinates.

The obligation is `2 x - 1 >= 0` for x in [1/2, 1]. In the coordinate
u = (1 - x) / x, i.e. x = 1 / (1 + u), the box is u in [0, 1], and
`(1 + u) (2 / (1 + u) - 1) = 1 - u`. This proves that; the construction's
`substitution` contract checks the pull-back, that 1 + u > 0, that the
inverse undoes the map, and that [1/2, 1] lands inside [0, 1].

    certo nonneg examples/chart_pullback.py --cert out/chart_pullback.json
"""
from certo import NonnegSpec
from certo.polynomials import Poly

u = Poly.var(("u",), "u")


def spec():
    return NonnegSpec(poly=1 - u, box={"u": (0, 1)}, title="1 - u on [0, 1]")
