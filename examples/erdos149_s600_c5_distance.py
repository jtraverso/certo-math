"""G1 S600: combined local C5 shielding inequalities.
The three disjoint graph cases are proved in the paper:
distance 0 (root belongs to C5), distance 1 (neighbor belongs),
distance 2 (a neighbor of root touches a C5 vertex).
Certify their scalar consequences under G1 heavy residual.
"""
import z3
from certo import Spec
def spec():
    x,a,b,z,p,q,c,d=z3.Reals("x a b z p q c d")
    K=z3.RealVal("5/4")
    S=z*(p+q)+p*c+c*d+q*d
    s=Spec(title="S600 near-tight C5 cannot enter a root closed 2-ball")
    s.assume("root_heavy",z3.And(x>z3.RealVal("1/2"),x<z3.RealVal("3/4")))
    s.assume("arc_small",z3.And(a>0,b>0,a+b<z3.RealVal("1/6")))
    s.assume("root_defect_margin",x-z3.RealVal("1/2")>11*a*b)
    s.assume("cycle_nonnegative",z3.And(z>=0,p>=0,q>=0,c>=0,d>=0))
    s.claim(z3.And(
        # If root s itself is on C5, use rows at two neighbors:
        z3.Implies(z==x,
           z3.Implies(z3.And(p+q+a<=1,z+c<=1,z+d<=1),
                      S<K-a*b)),
        # If s is outside, adjacent to cycle vertex z, use degree rows,
        # the universal minimal-mass cap c,d<3/4, and exact cyclic sum.
        z3.Implies(z3.And(z!=x,p+q+x<=1,z+c<=1,z+d<=1,
                          c<z3.RealVal("3/4"),d<z3.RealVal("3/4")),
                  S<K-a*b),
        # If d_H(s,C5)=2 then z<=1-x and 5-cycle stability:
        z3.Implies(z3.And(z<=1-x,S<=1+z*z),
                  S<K-a*b)
    ))
    s.role("consumer")
    s.pending("cycle_stability","The S<=1+z^2 statement is proved by a separate Certo spec")
    s.pending("topology","Three distance cases use actual graph adjacency and are not encoded")
    return s
