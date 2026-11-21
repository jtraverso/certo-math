"""Erdos 149, session 595: exact linear consequence of heavy exclusive classes.

The graph-theoretic claim that every root-exclusive class contains a heavy
interior edge is proved in docs/ERDOS149_S595_HEAVY_SATURATION.md.
This Certo spec verifies only its algebraic downstream implication.

Assume J<D, r_s+ab<=x, r_t+ab<=y, and nu_Z>=r_s+r_t-2J.
Then nu_Z>5/2-x-y. Reals, no numeric quantization.

Run:
  certo lint examples/erdos149_arco3_heavy_saturation.py
  certo prove examples/erdos149_arco3_heavy_saturation.py
  certo verify out/erdos149_arco3_heavy_saturation.json
"""
import z3
from certo import Spec

def spec():
    x,y,rs,rt,ab,j,nu = z3.Reals("x y rs rt ab j nu")
    K=z3.RealVal("5/4")
    p=Spec(title="Erdos149 S595 heavy-flow lower bound if J<D")
    p.assume("roots_positive", z3.And(x>0,y>0,x<1,y<1))
    p.assume("inner_weight_positive",ab>=0)
    p.assume("root_s_bound",rs+ab<=x)
    p.assume("root_t_bound",rt+ab<=y)
    p.assume("obstruction",j<rs+rt+ab-K)
    p.assume("exact_root_exclusive_flow",nu>=rs+rt-2*j)
    p.claim(nu>z3.RealVal("5/2")-x-y)
    p.role("consumer")
    p.pending("physical_recolor", "Combinatorial heavy-saturation lemma proved on paper, not encoded in SMT")
    return p
