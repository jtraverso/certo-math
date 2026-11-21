"""Erdos149 session 594: quadratic-envelope stationary point is nonnegative.

For m0=(5/4-y)/(4*x), quadratic in a has derivative at zero
    y/(6*m0)-(1-x).
Strictly positive iff 2*x*y - 3*(1-x)*(5/4-y)>0. This is independently
certified on 7/10<=x<=3/4, 1/2<=y<=x.

  certo prove examples/erdos149_arco3_degree4_heavy_vertex.py
"""
import z3
from certo import Spec

def spec():
    x,y=z3.Reals("x y")
    s=Spec(title="Erdos149 heavy-root positive quadratic-envelope vertex")
    s.assume("x_ge_7_10",x>=z3.RealVal("7/10"))
    s.assume("x_le_3_4",x<=z3.RealVal("3/4"))
    s.assume("y_ge_half",y>=z3.RealVal("1/2"))
    s.assume("y_le_x",y<=x)
    s.claim(2*x*y-3*(1-x)*(z3.RealVal("5/4")-y)>0)
    s.role("consumer")
    s.pending("arc3", "Stationary-point domain only; not physical graph recoloring")
    return s
