"""Erdos 149 S595: exact universal scalar cut excluding a clean exclusive class.

For 0<x,y<1, K=5/4:
  K-y-x*(1-y) = 1/4+(1-x)*(1-y)>0.
This is the scalar part of the unilateral root-transfer contradiction.

Run:
  certo lint examples/erdos149_arco3_no_light_cut.py
  certo prove examples/erdos149_arco3_no_light_cut.py
  certo verify out/erdos149_arco3_no_light_cut.json
"""
import z3
from certo import Spec

def spec():
    x,y=z3.Reals("x y")
    p=Spec(title="Erdos149 S595 no-light-class scalar contradiction")
    p.assume("x_pos", x>0)
    p.assume("x_lt_one",x<1)
    p.assume("y_pos",y>0)
    p.assume("y_lt_one",y<1)
    p.claim(z3.RealVal("5/4")-y>x*(1-y))
    p.role("consumer")
    p.pending("physical_recolor","Only scalar inequality proved here; combinatorial recoloring is in S595 proof")
    return p
