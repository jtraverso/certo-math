"""Erdos #149 S597 mass shielding of root edges from a heavy 5-cycle.

If each cycle mass c_i exceeds max(1-x,1-y), the row constraints
forbid any edge from N(s) or N(t) to a cycle vertex. Nor can s or t
be incident to a cycle vertex, because two cycle neighbors already
supply at least 2*c_min mass.

Certo proves the scalar contradictions; graph-theoretic quantifiers
are handled in S597_WEIGHTED_CORE_AND_SPLIT.md.
"""
import z3
from certo import Spec

def spec():
    x,y,c=z3.Reals("x y c")
    s=Spec(title="Erdos149: shielding of near-heavy C5 from two root stars")
    s.assume("x_gt_half", x>z3.RealVal("1/2"))
    s.assume("x_lt_three_quarters",x<z3.RealVal("3/4"))
    s.assume("y_gt_half",y>z3.RealVal("1/2"))
    s.assume("y_lt_three_quarters",y<z3.RealVal("3/4"))
    s.assume("cycle_mass_gt_1_minus_x",c>1-x)
    s.assume("cycle_mass_gt_1_minus_y",c>1-y)
    s.claim(z3.And(x+c>1,y+c>1,x+2*c>1,y+2*c>1))
    s.role("consumer")
    s.pending("graph_combinatorics","The scalar inequality alone does not prove Q_F<=K")
    return s
