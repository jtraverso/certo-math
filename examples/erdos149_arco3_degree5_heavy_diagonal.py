"""Erdos149 session 594: exact univariate diagonal, degree <=5.

Analytical consequence, CONDITIONAL on S593 directed blocking lemma:
For an arc-3 candidate with heavier root x in [73/100, 3/4], y in
[1/2,x], a,b>=0, a+b<1/6, and old degree <=5 of the heavier root,
the scalar obstruction cannot hold. See docs/ERDOS149_CEGIS_RESEARCH.md.

    certo prove examples/erdos149_arco3_degree5_heavy_diagonal.py
"""
import z3
from certo import Spec

def spec():
    x = z3.Real("x")
    n = -3460*x**4 + 7884*x**3 - 5829*x**2 + 1710*x - 225
    s = Spec(title="Erdos149 arc-3 heavy-root degree-5 diagonal positivity")
    s.assume("x_ge_73_100", x >= z3.RealVal("73/100"))
    s.assume("x_le_3_4", x <= z3.RealVal("3/4"))
    s.claim(n > 0)
    s.role("consumer")
    s.pending("arc3", "Conditional on S593 directed-blocker inequality, not global theorem")
    return s
