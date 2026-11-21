"""Exact polynomial identity behind C5 incidence absorption.

For m_i, let z_i=1-m_i-m_(i+2). Then
4*(5/4 - sum(m_i) + sum(m_i*m_(i+1)))
  == (sum(z_i))^2 - 4*sum(z_i*z_(i+2)).
This identity is unconditional and checked over all real variables.
"""
import z3
from certo import Spec
def spec():
    m=z3.Reals("m0 m1 m2 m3 m4")
    z=[1-m[i]-m[(i+2)%5] for i in range(5)]
    W=z3.Sum([m[i]*m[(i+1)%5] for i in range(5)])
    RHS=z3.Sum(z)*z3.Sum(z)-4*z3.Sum([z[i]*z[(i+2)%5] for i in range(5)])
    s=Spec(title="Erdos149 S600 exact five-cycle Horn identity")
    s.claim(4*(z3.RealVal("5/4")-z3.Sum(m)+W)==RHS)
    s.role("consumer")
    s.pending("mantel","Nonnegativity of RHS by weighted triangle-free Mantel compression")
    return s
