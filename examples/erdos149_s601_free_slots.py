"""S601 universal inequalities giving free C5 slots for all good edges
and all one-contact crossing edges.
delta=ab<1/144, W5>=5/4-delta, B<3/4.
Li=1/2-2delta; mi>L_i. Each C5 slot holds >=L_i^2.
The unpaired root-free slot width beats (72/35)*delta.
"""
import z3
from certo import Spec

def spec():
    delta,W,B=z3.Reals("delta W B")
    K=z3.RealVal("5/4")
    L=z3.RealVal("1/2")-2*delta
    s=Spec(title="S601 every root-free C5 color slot exceeds entire insertable annulus")
    s.assume("delta",z3.And(delta>0,delta<z3.RealVal("1/144")))
    s.assume("cycle_weight",z3.And(W>=K-delta,W<=K))
    s.assume("root_band",z3.And(B>=0,B<z3.RealVal("3/4")))
    s.claim(z3.And(
       L>0,
       L*L*(W-B)>z3.RealVal("72/35")*delta*W,
       delta<2*L*L))
    s.role("consumer")
    s.pending("physical_slots","C5 edge weight >=L^2 and W_good+W_cross1<72delta/35")
    return s
