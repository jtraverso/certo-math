"""Erdos #149 S599: exact universal algebra of the palette-mixture gate.

Let beta<=K be the width of an old full palette,
B=max(root star demands), sigma=K-beta and D=rs+rt+ab-K.
Full Hall coupling of roots gives a palette of width B+beta
with joint overlap min(rs,rt). Mixing it with the old palette
at theta=sigma/B (when sigma<=B) yields J>=rs+rt-K+sigma*beta/B.

This spec PROVES ONLY THE CLEARED ALGEBRA of the sufficient test:
sigma*beta>=ab*B => J>=D.  The constructive coloring
argument is written in S599.
"""
import z3
from certo import Spec

def spec():
    K=z3.RealVal("5/4")
    beta,B,ab,rs,rt,sigma=z3.Reals("beta B ab rs rt sigma")
    s=Spec(title="Erdos149 C15-P exact global palette mixture algebra")
    s.assume("old_width", z3.And(beta>=B,beta<=K))
    s.assume("root_band",B>0)
    s.assume("sigma_def",sigma==K-beta)
    s.assume("mix_theta_at_most_one",sigma<=B)
    s.assume("positive_inner_demand",ab>=0)
    s.assume("mix_threshold",sigma*beta>=ab*B)
    s.claim(B*(rs+rt-K)+sigma*beta >= B*(rs+rt+ab-K))
    s.role("consumer")
    s.pending("root_hall","Requires the S597 physical root star synchronization")
    s.pending("palette_mix","Exact coverage by convex combination is an analytical proof, not encoded in Z3")
    return s
