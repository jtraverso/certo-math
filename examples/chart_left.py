"""nonneg for `construction_charts.json`: the LEFT chart's bound.

    1 - x y - x / 2 >= 0   on [0, 1]^2, where x <= 3/5

The chart's selector `3/5 - x >= 0` is the certificate's region, so the
certificate assumes exactly what the chart selects -- the construction checks
that, and that the chart's leaves lie inside this box.

    certo nonneg examples/chart_left.py --cert out/chart_left.json
"""
from fractions import Fraction

from certo import NonnegSpec
from certo.polynomials import Poly

R = ("x", "y")
x, y = Poly.var(R, "x"), Poly.var(R, "y")


def spec():
    return NonnegSpec(poly=1 - x * y - x / 2,
                      box={"x": (0, 1), "y": (0, 1)},
                      region=[("left", Fraction(3, 5) - x)],
                      title="the left chart")
