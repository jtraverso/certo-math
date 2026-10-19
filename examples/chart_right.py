"""nonneg for `construction_charts.json`: the RIGHT chart's bound.

    x - x y / 2 - 1/5 >= 0   on [0, 1]^2, where x >= 2/5

    certo nonneg examples/chart_right.py --cert out/chart_right.json
"""
from fractions import Fraction

from certo import NonnegSpec
from certo.polynomials import Poly

R = ("x", "y")
x, y = Poly.var(R, "x"), Poly.var(R, "y")


def spec():
    return NonnegSpec(poly=x - x * y / 2 - Fraction(1, 5),
                      box={"x": (0, 1), "y": (0, 1)},
                      region=[("right", x - Fraction(2, 5))],
                      title="the right chart")
