"""Erdos149 session 594: derivative signs for the d=4 envelope, exact.

The derivative of the envelope f(x,y) w.r.t. y equals
(1-x)/(4x)*(1-5*(1-x)/(16*y*y)) + 5*x/(9*(4*y-5)**2).
Both terms are nonnegative and second strictly positive in the region.
This file certifies the sign of the only nonobvious factor.

  certo prove examples/erdos149_arco3_degree4_heavy_slope.py
"""
import z3
from certo import Spec

def spec():
    x,y=z3.Reals("x y")
    s=Spec(title="Erdos149 heavy-root envelope monotone in y")
    s.assume("x_ge_7_10", x>=z3.RealVal("7/10"))
    s.assume("x_le_3_4", x<=z3.RealVal("3/4"))
    s.assume("y_ge_half",y>=z3.RealVal("1/2"))
    s.assume("y_le_x",y<=x)
    s.claim(16*y*y-5*(1-x)>0)
    s.role("consumer")
    s.pending("arc3", "Proof of scalar envelope monotonicity only")
    return s
