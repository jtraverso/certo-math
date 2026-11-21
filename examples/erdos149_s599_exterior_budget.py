"""Erdos149 S599: exact universal algebra for radius-one exterior budget.

The physical row-counting lemma gives W_near<=1-(x+y)/2
and Hall gives root width B<=max(x,y), when 1/2<x,y<3/4.
Certo proves that W_far<=1/8 suffices for B+W_near+W_far<5/4.

No physical graph quantifiers are encoded in this file.
"""
import z3
from certo import Spec
def spec():
    x,y,B,near,far=z3.Reals("x y B W_near W_far")
    K=z3.RealVal("5/4")
    p=Spec(title="Erdos149 S599 uniform 1/8 exterior-edge budget")
    p.assume("x_lower",x>z3.RealVal("1/2"))
    p.assume("x_upper",x<z3.RealVal("3/4"))
    p.assume("y_lower",y>z3.RealVal("1/2"))
    p.assume("y_upper",y<z3.RealVal("3/4"))
    p.assume("root_band",z3.And(B>=0,B<=z3.If(x>=y,x,y)))
    p.assume("near_weight_row_bound",
             z3.And(near>=0,near<=1-(x+y)/2))
    p.assume("far_weight_budget",z3.And(far>=0,far<=z3.RealVal("1/8")))
    p.claim(z3.And(B+near<=z3.RealVal("9/8"),
                   B+near+far<K))
    p.role("consumer")
    p.pending("physical_count","Physical degree-row double counting is analytical")
    p.pending("hall","Full root-star synchronization follows S597")
    return p
