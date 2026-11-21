"""Erdos #149 S600-C19: exact real algebra for thin near-tight C5 collars.

The physical ingredients W5>=K-delta, row feasibility and the
fixed-vertex C5 inequality W5<=1+z^2 are established separately.
This Certo specification certifies that a cycle vertex z<=1/2
must satisfy z>1/2-2delta, and the ratio of the upper to lower
cycle masses is strictly below 37/35 for delta<1/144.

It does NOT prove the G1 universal reinsertion gate.
"""
import z3
from certo import Spec

def spec():
    z,delta,W=z3.Reals("z delta W")
    K=z3.RealVal("5/4")
    L=z3.RealVal("1/2")-2*delta
    U=z3.RealVal("1/2")+2*delta
    s=Spec(title="Erdos149 S600 C19 thin-collar algebraic sharpness")
    s.assume("delta_positive",delta>0)
    s.assume("delta_small",delta<z3.RealVal("1/144"))
    s.assume("low_vertex_case",z3.And(z>=0,z<=z3.RealVal("1/2")))
    s.assume("near_tight_cycle",W>=K-delta)
    s.assume("five_cycle_stability",W<=1+z*z)
    s.claim(z3.And(
        z>L,
        35*U<37*L,
        4*delta<L,
        2*L+4*delta==1
    ))
    s.role("consumer")
    s.pending("five_cycle","Fixed-vertex C5 inequality is checked in another Certo spec")
    s.pending("graph_rows","Bound for the second layer uses original physical degree rows")
    return s
