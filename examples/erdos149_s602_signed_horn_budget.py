"""S602: universal algebraic signed Horn cancellation.

Cycle masses may be ABOVE 1/2. Then alpha_i=(1-2mi)/4
can be negative, so the nonnegative C21 row-price argument does
not apply. The exact identity makes the signed terms cancel:
 K-W5-Wcross2 - bad_DD - bad_DS >= sum gamma_i*s_i >= 0,
assuming the physical DD/DS combinatorial charge inequalities.

This is a real-algebra implication under the assumptions; it does
NOT quantify arbitrary physical graphs or prove universal G1.
"""
import z3
from certo import Spec

def spec():
    m=z3.Reals("m0 m1 m2 m3 m4")
    p=z3.Reals("p0 p1 p2 p3 p4")  # X1 neighbor mass at cycle vertex
    q=z3.Reals("q0 q1 q2 q3 q4")  # X2 neighbor mass at cycle vertex
    srow=z3.Reals("s0 s1 s2 s3 s4")
    DD,DS=z3.Reals("badDD badDS")
    alpha=[(1-2*m[i])/4 for i in range(5)]
    gamma=[m[i]+alpha[i] for i in range(5)]
    W5=z3.Sum([m[i]*m[(i+1)%5] for i in range(5)])
    Wcross2=z3.Sum([m[i]*q[i] for i in range(5)])
    H=z3.RealVal("5/4")-z3.Sum(m)+W5
    a=z3.Sum([alpha[i]*q[i] for i in range(5)])
    b=z3.Sum([gamma[i]*p[i] for i in range(5)])
    s=Spec(title="S602 signed Horn row charge pays ALL C5 bad corona")
    s.assume("masses_positive",z3.And(*[m[i]>0 for i in range(5)]))
    s.assume("cycle_rows_and_external_profiles",z3.And(*[
        z3.And(p[i]>=0,q[i]>=0,srow[i]>=0,
               m[(i-1)%5]+m[(i+1)%5]+p[i]+q[i]+srow[i]==1)
        for i in range(5)]))
    s.assume("physical_bad_charge",z3.And(DD>=0,DD<=a,DS>=0,DS<=b))
    s.claim(z3.And(
        H==z3.Sum([alpha[i]*(p[i]+q[i]+srow[i]) for i in range(5)]),
        z3.RealVal("5/4")-W5-Wcross2-DD-DS>=
             z3.Sum([gamma[i]*srow[i] for i in range(5)]),
        z3.RealVal("5/4")-W5-Wcross2-DD-DS>=0))
    s.role("consumer")
    s.pending("physical_DD","Prove DD <= sum alpha_i q_i by double counting double-attachment vertex rows")
    s.pending("physical_DS","Prove DS <= sum gamma_i p_i from X1-X2 edge total and W1 bound")
    s.pending("remote_edges","This pays only C5+two-ring collar and root stars")
    return s
