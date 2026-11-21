"""G1 S600: sharp cap-free five-cycle bound next to a heavy external root.

For masses (z,p,c,d,q) around C5 with an external neighbor root
of mass x>=1/2 at vertex z, its row implies p+q<=1-x.
Other rows imply c<=1-max(z,q), d<=1-max(z,p).
Then w(C5)<=1+(p+q)^2/4<=1+(1-x)^2/4<=17/16.
No 3/4 mass cap is needed. Reflection permits p<=q.
"""
import z3
from certo import Spec
def spec():
    x,z,p,q=z3.Reals("x z p q")
    u=p+q
    c=z3.If(z>=q,1-z,1-q)
    d=z3.If(z>=p,1-z,1-p)
    w=z*u+p*c+c*d+q*d
    s=Spec(title="S600 C5 neighbor shielding with no vertex mass cap")
    s.assume("root_mass",z3.And(x>=z3.RealVal("1/2"),x<1))
    s.assume("cycle_positive",z3.And(z>=0,z<=1,p>=0,q>=0,p<=q))
    s.assume("adjacent_root_row",u<=1-x)
    s.claim(z3.And(w<=1+u*u/4,
                   w<=1+(1-x)*(1-x)/4,
                   w<=z3.RealVal("17/16")))
    s.role("consumer")
    s.pending("graph","Cycle inequalities converted into endpoint bounds in proof")
    return s
