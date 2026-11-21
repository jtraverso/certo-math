"""G1 S600: sharp 5-cycle stability for one mass z<=1/2.

Let cycle masses (z,p,c,d,q) with rows
 z+c<=1,z+d<=1,p+d<=1,c+q<=1,p+q<=1.
Because the 5-cycle objective is increasing in c,d, its maximum
for fixed (z,p,q) has c=1-max(z,q), d=1-max(z,p).
Prove globally: w(C5)<=1+z^2.
Reflections permit p<=q without loss.
"""
import z3
from certo import Spec
def spec():
    z,p,q=z3.Reals("z p q")
    c=z3.If(z>=q,1-z,1-q)
    d=z3.If(z>=p,1-z,1-p)
    w=z*(p+q)+p*c+c*d+q*d
    s=Spec(title="S600 five-cycle fixed-vertex sharp stability")
    s.assume("nonnegative",z3.And(z>=0,p>=0,q>=0))
    s.assume("symmetry",p<=q)
    s.assume("z_half",z<=z3.RealVal("1/2"))
    s.assume("neighbor_row",p+q<=1)
    s.claim(w<=1+z*z)
    s.role("consumer")
    s.pending("graph_application","Uses physical cycle row constraints in paper")
    return s
