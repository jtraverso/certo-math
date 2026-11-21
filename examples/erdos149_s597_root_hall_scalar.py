"""Erdos #149 S597: root-pair Hall threshold, exact UNIVERSAL scalar lemma.

On the S591 heavy residual (x,y in [1/2,3/4], D>0 and
r_s+ab<=x, r_t+ab<=y) prove BOTH roots have enough total
demand to meet the forbidden complete bipartite mass threshold:
  min(r_s,r_t) > x(1-y)+y(1-x).

This is the algebraic piece of a universal Hall theorem for TWO
root stars considered WITHOUT any non-root edge demands. This is
NOT a certificate of the full arc-3 reinsertion gate.
"""
import z3
from certo import Spec

def spec():
    x,y,rs,rt,ab=z3.Reals("x y rs rt ab")
    K=z3.RealVal("5/4")
    s=Spec(title="Erdos149 S597 universal heavy-root Hall bridge inequality")
    s.assume("x_lower", x>=z3.RealVal("1/2"))
    s.assume("x_upper", x<=z3.RealVal("3/4"))
    s.assume("y_lower", y>=z3.RealVal("1/2"))
    s.assume("y_upper", y<=z3.RealVal("3/4"))
    s.assume("root_nonneg", z3.And(rs>=0,rt>=0,ab>=0))
    s.assume("row_s", rs+ab<=x)
    s.assume("row_t", rt+ab<=y)
    s.assume("D_pos", rs+rt+ab>K)
    C=x*(1-y)+y*(1-x)
    s.claim(z3.And(rs>C,rt>C))
    s.role("consumer")
    s.pending("interior_edges","Hall synchronizes the two root stars ALONE, not all H")
    s.link("S597 root-pair Hall scalar part")
    return s
