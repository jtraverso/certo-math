"""S601 exact Horn row-price identity for balanced-below C5.

For every cycle mass mi (over arbitrary reals), let
alpha_i=(1-2mi)/4 and zi=1-m_(i-1)-m_(i+1).
Then K-sum(mi)+sum(mi*m_(i+1))=sum(alpha_i*zi).
If mi<=1/2 and rows hold, all alpha_i and zi are >=0.
The graph-theoretic double-edge charge is proved separately.
"""
import z3
from certo import Spec

def spec():
    m=z3.Reals("m0 m1 m2 m3 m4")
    alpha=[(1-2*m[i])/4 for i in range(5)]
    z=[1-m[(i-1)%5]-m[(i+1)%5] for i in range(5)]
    lhs=z3.RealVal("5/4")-z3.Sum(m)+z3.Sum([m[i]*m[(i+1)%5] for i in range(5)])
    rhs=z3.Sum([alpha[i]*z[i] for i in range(5)])
    s=Spec(title="S601 exact row-price identity for balanced C5")
    s.assume("balanced",z3.And(*[z3.And(m[i]>=0,m[i]<=z3.RealVal("1/2")) for i in range(5)]))
    s.assume("cycle_rows",z3.And(*[q>=0 for q in z]))
    s.claim(z3.And(lhs==rhs,*[q>=0 for q in alpha]))
    s.role("consumer")
    s.pending("physical_dd_charge","DD annulus edge weight charged twice to exterior rows")
    return s
