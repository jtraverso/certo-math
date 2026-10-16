"""covering: alternative obligations on a box, under physical conditions.

    for every (theta, zeta) in [0, 1] x [0, 1/7]
    with  theta (16 + theta) / 64 - zeta >= 0       (the physical domain)
    at least one of  F = theta - 2 zeta + 1/100 > 0
                     U = 1/7 - zeta - theta/8 >= 0

certo halves the box until on each leaf one obligation keeps its sign, or the
condition is negative there (the leaf is outside the physical domain), and
certifies that the leaves tile the box -- boundaries included. Every leaf and
its reason are in the certificate, recomputed by `verify` with no solver.

    certo covering examples/covering_physical.py
    certo verify out/covering_physical.json
"""
from fractions import Fraction

import z3

from certo import CoveringSpec


def spec():
    theta, zeta = z3.Reals("theta zeta")
    return CoveringSpec(
        title="F or U on the physical part of the box",
        domain={"theta": (0, 1), "zeta": (0, Fraction(1, 7))},
        conditions=[("physical", theta * (16 + theta) / 64 - zeta)],
        obligations=[("F", theta - 2 * zeta + Fraction(1, 100)),
                     ("U", ">=", Fraction(1, 7) - zeta - theta / 8)],
    )
