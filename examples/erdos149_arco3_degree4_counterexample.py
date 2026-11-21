"""Erdos #149: precise *refutation of a scalar criterion*, NOT the conjecture.

The degree-4 scalar test of session 593 fails at a valid rational residual
(x=y=13/20, a=b=1/200, p=q=199/200, D=1741/40000).
This is NOT a graph with Q_F>K, nor a counterexample to the arc-3 lemma.

Run:
  certo prove examples/erdos149_arco3_degree4_counterexample.py
"""
import z3
from certo import Spec
K = z3.RealVal("5/4")
A = z3.RealVal("1/200")

def gap_numerator(d, x):
    L = K - x
    dx = d * x
    return ((1 - x) * (1 - A) - z3.RealVal("1/4")) * dx * L - (1 - x) * L * L + x * A * A * dx * dx


def spec():
    x = z3.Real("x")
    s = Spec(title="Falsification of uniform scalar degree-4 closure")
    s.assume("x_fixed", x == z3.RealVal("13/20"))
    s.claim(gap_numerator(z3.IntVal(4), x) <= 0)
    s.role("refutation")
    s.pending("arc3", "This only falsifies the d=4 SCALAR test; not a physical obstruction")
    return s
