"""A bound proved box by box, and the one sentence that joins them.

`max x` subject to `(p - q + 2) x <= 1`, for parameters in the unit square:
the dual 1 bounds the optimum by 1 wherever `p - q + 1 >= 0`, which is all of
the square. The claim is proved here on three of its four quadrants -- the
fourth, top-left, is left out on purpose -- and the domain is the square CUT
by the region `p - q >= 1/4`, which the missing quadrant lies wholly outside:

    $ certo atlas examples/parametric_atlas.py
    PROVED  [unsat]
      on the whole domain the optimum is <= 1: 3 piece(s), covering checked
      over 7 cells (1 shown outside the region)
      certificate: parametric_atlas (no solver needed)

WHAT IS CHECKED. Every piece verifies; all three are about the same program
and prove the same claim; and the covering is recomputed: the square is split
at the pieces' edges, and the one cell no piece covers is shown outside the
region by the Bernstein coefficients of `p - q - 1/4`, all negative there.
Drop the region and the same three pieces are NOT enough -- `atlas` names the
top-left quadrant as the uncovered cell, with its coordinates.

The pieces here are ParametricSpecs, run and embedded. Certificates written
by `certo parametric --cert` can be listed by path instead, and are then
referenced by digest rather than copied.
"""
from fractions import Fraction

from certo import AtlasSpec, ParametricSpec
from certo.polynomials import Poly

R = ("p", "q")
p, q = Poly.var(R, "p"), Poly.var(R, "q")
ONE = Poly.const(R, 1)
HALF = Fraction(1, 2)


def piece(box):
    return ParametricSpec(
        parameters={"p": 0, "q": 0}, objective={"x": ONE},
        constraints=[("c", {"x": p - q + ONE.scaled(2)}, "<=", ONE)],
        dual={"c": Fraction(1)}, box=box, claim=ONE,
        title="one quadrant")


def spec():
    return AtlasSpec(
        domain={"p": (0, 1), "q": (0, 1)},
        region=[("cut", p - q - ONE.scaled(Fraction(1, 4)))],
        claim=ONE,
        pieces=[piece({"p": (0, HALF), "q": (0, HALF)}),
                piece({"p": (HALF, 1), "q": (0, HALF)}),
                piece({"p": (HALF, 1), "q": (HALF, 1)})],
        title="three quadrants and a region")
