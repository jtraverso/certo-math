"""Erdos149 S600 C20: universal rational inequalities for quadratic C5 collar.

Assumptions: near-tight cycle W5>=5/4-delta, root Hall width B<3/4,
0<delta=ab<1/144. Given C19 cycle edge masses >L=1/2-2delta,
the root-free portion of EACH cycle color slot exceeds the total
second-layer demand <37delta/35. The quadratic exceptional bound
2delta²/L < 144delta²/35 is also certified after clearing.

This verifies scalar algebra only, not the graph-theoretic
vertex-cover argument or the global Erdős conjecture.
"""
import z3
from certo import Spec

def spec():
    delta,B,W5=z3.Reals("delta B W5")
    K=z3.RealVal("5/4")
    L=z3.RealVal("1/2")-2*delta
    s=Spec(title="Erdos149 S600 C20 cycle-root-free slot and quadratic exception bounds")
    s.assume("delta_pos",delta>0)
    s.assume("delta_small",delta<z3.RealVal("1/144"))
    s.assume("root_band",z3.And(B>=0,B<z3.RealVal("3/4")))
    s.assume("cycle_neartight",z3.And(W5>=K-delta,W5<=K))
    s.claim(z3.And(
        L>z3.RealVal("35/72"),
        35*L*L*(W5-B)>37*delta*W5,
        144*L>70
    ))
    s.role("consumer")
    s.pending("C19","Uses C5 mass stability and second-layer W2<(37/35)delta")
    s.pending("C20","Physical vertex-cover proof needed for Wbad<2delta²/L")
    return s
