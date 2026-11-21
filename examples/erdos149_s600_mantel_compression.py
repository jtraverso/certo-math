"""Exact algebraic invariants of weighted Mantel compression for C5.

For the complement C5 edges (i,i+2), indices 0 and 1 are nonadjacent.
If grad(0)>=grad(1), moving all z1 mass to z0 cannot reduce its
quadratic edge energy. Rotation/reflection and repetition shrink any
support to a clique of size at most 2. AM-GM finishes the proof.
"""
import z3
from certo import Spec
def spec():
    z=z3.Reals("z0 z1 z2 z3 z4")
    E=lambda v:z3.Sum([v[i]*v[(i+2)%5] for i in range(5)])
    merged=[z[0]+z[1],z3.RealVal(0),z[2],z[3],z[4]]
    s=Spec(title="S600 weighted Mantel no-loss merge and 2-point AM-GM")
    s.assume("nonnegative",z3.And(*[v>=0 for v in z]))
    s.assume("choose_no_loss_direction",z[2]>=z[4])
    s.claim(z3.And(E(merged)>=E(z),
                   4*z[0]*z[1]<=(z[0]+z[1])*(z[0]+z[1])))
    s.role("consumer")
    s.pending("graph_symmetry","Other nonadjacent pairs follow by five-cycle automorphisms")
    s.pending("termination","Each compression strictly reduces positive support")
    return s
