"""Erdos #149 S598: universal linear dual-negativity obstruction.

This SMT result is the algebraic implication of a separate analytical
result: a root-only Hall palette gives alpha>=min(r_s,r_t).
If a full palette had Jmax<D, its optimal dual requires weighted negative
nonroot prices exceeding 1/2. Only the implication is formalized here.

Run:
  certo lint examples/erdos149_s598_dual_negative.py
  certo prove examples/erdos149_s598_dual_negative.py
  certo verify out/erdos149_s598_dual_negative.json
"""
import z3
from certo import Spec

def spec():
    x, y, rs, rt, ab, alpha, positive, negative = z3.Reals(
        "x y rs rt ab alpha positive negative")
    K=z3.RealVal("5/4")
    small=z3.If(rs<=rt,rs,rt)
    big=z3.If(rs>=rt,rs,rt)
    s=Spec(title="S598 necessary weighted negative dual contribution")
    s.assume("x_positive",x>z3.RealVal("1/2"))
    s.assume("x_max",x<z3.RealVal("3/4"))
    s.assume("y_positive",y>z3.RealVal("1/2"))
    s.assume("y_max",y<z3.RealVal("3/4"))
    s.assume("root_s",z3.And(rs>=0,rs+ab<=x))
    s.assume("root_t",z3.And(rt>=0,rt+ab<=y))
    s.assume("inner_ab",ab>=0)
    s.assume("root_only_palette_dual",alpha>=small)
    s.assume("positive_price_mass",positive>=0)
    s.assume("negative_price_mass",negative>=0)
    s.assume("dual_below_threshold",
             alpha+positive-negative<rs+rt+ab-K)
    s.claim(z3.And(negative>K-big-ab,negative>z3.RealVal("1/2")))
    s.role("consumer")
    s.pending("root_hall","Uses the separately proved full root-only synchronization")
    s.pending("dual_support","Zero support outside anchored core follows via LP dual lifting")
    return s
