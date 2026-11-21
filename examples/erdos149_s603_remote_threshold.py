"""Erdos149 S603: universal threshold for completing ALL remote old demands.

Let C5 be near-tight W5>=K-delta, root Hall width B<3/4,
and all good second-ring plus one-contact crossing demand
Vinsert<(72/35)delta. Any old edge outside the complete C5
strong-conflict collar is compatible with ALL five cycle edges.
If total remote demand <= 1/2-(107/35)delta, then enough rootless
C5 colors remain for greedy insertion, preserving all root overlap.

This spec certifies the exact scalar inequality; the physical
compatibility and greedy process are proved separately.
"""
import z3
from certo import Spec

def spec():
    delta,B,W5,Vinsert,Wrem=z3.Reals("delta B W5 Vinsert Wrem")
    K=z3.RealVal("5/4")
    s=Spec(title="S603 G1 full-graph near-tight C5 remote mass threshold")
    s.assume("delta",z3.And(delta>0,delta<z3.RealVal("1/144")))
    s.assume("root_band",z3.And(B>=0,B<z3.RealVal("3/4")))
    s.assume("cycle",z3.And(W5>=K-delta,W5<=K))
    s.assume("free_insert",z3.And(Vinsert>=0,Vinsert<z3.RealVal("72/35")*delta))
    s.assume("remote_demand",z3.And(Wrem>=0,
             Wrem<=z3.RealVal("1/2")-z3.RealVal("107/35")*delta))
    s.claim(W5-B-Vinsert>Wrem)
    s.role("consumer")
    s.pending("C22","Root/C5/two-ring collar exact palette from signed Horn cancellation")
    s.pending("physical_remote","Remaining old edges are compatible with each original C5 edge")
    return s
