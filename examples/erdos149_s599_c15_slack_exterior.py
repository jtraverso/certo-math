"""Erdos #149 G1 S599-C15: universal exact slack-vs-far dual implication.

Assuming a full palette of width beta=K-sigma and a root+near partial
palette with joint overlap m=min(rs,rt), EVERY dual obstructing J>=D
would require BOTH
   tau*Wfar > K-B-ab
   sigma*tau < ab-sigma.
The displayed condition sigma*(K-B-ab)>=(ab-sigma)*Wfar
makes that impossible. This Certo spec verifies only the nonlinear
real-algebra consequence; physical palette constructions are in S599.
"""
import z3
from certo import Spec

def spec():
    sigma,ab,B,W,tau=z3.Reals("sigma ab B W_far tau")
    K=z3.RealVal("5/4")
    P=K-B-ab
    s=Spec(title="Erdos149 S599 C15 universal slack exterior dual contradiction")
    s.assume("slack_nonnegative",sigma>=0)
    s.assume("inner_demand_positive",ab>0)
    s.assume("root_width_positive",B>=0)
    s.assume("root_plus_inner_below_one",B+ab<z3.RealVal("3/4"))
    s.assume("far_weight_nonnegative",W>=0)
    s.assume("dual_tau_nonnegative",tau>=0)
    s.assume("C15_sufficient_numeric",sigma*P>=(ab-sigma)*W)
    s.claim(z3.Not(z3.And(tau*W>P, sigma*tau<ab-sigma)))
    s.role("consumer")
    s.pending("partial_palette","Root+near synchronized palette exists by S597 and degree row count")
    s.pending("old_palette","Width beta=K-sigma must be certified on original H")
    s.pending("dual","Strong edge induced matching constraints imply singleton lambda_e >= -tau")
    return s
