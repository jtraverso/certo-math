"""Erdos149 session 594: exact univariate algebraic diagonal for d=4 heavy-root gate.

Certifies a polynomial used in the human analytical proof that the S593
scalar necessary obstruction cannot hold when 7/10<=x=max(root masses)<=3/4
and the heavier root has <=4 old neighbors.
The step from this polynomial to the graph statement uses the S593 directed
recoloring lemma, NOT certified by this file.

  certo prove examples/erdos149_arco3_degree4_heavy_diagonal.py
"""
import z3
from certo import Spec

def spec():
    x = z3.Real("x")
    n = -2896*x**4 + 6840*x**3 - 5349*x**2 + 1710*x - 225
    s = Spec(title="Erdos149 arc-3 heavy-root degree-4 diagonal positivity")
    s.assume("x_ge_7_10", x >= z3.RealVal("7/10"))
    s.assume("x_le_3_4", x <= z3.RealVal("3/4"))
    s.claim(n > 0)
    s.role("consumer")
    s.pending("arc3", "Conditional on S593 directed-blocker inequality, not universal proof")
    return s
