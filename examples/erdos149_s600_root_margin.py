"""G1 S600: prove both heavy roots exceed 1/2 by >11ab.
Under the S591 heavy residual: a,b>0,a+b<1/6, x,y<3/4,
r_s<=x(1-a),r_t<=y(1-b),r_s+r_t+ab>5/4.
This checks only real algebra, not the entire graph argument.
"""
import z3
from certo import Spec
def spec():
    x,y,a,b,rs,rt=z3.Reals("x y a b rs rt")
    s=Spec(title="S600 G1 both root masses exceed 1/2+11ab")
    s.assume("positive",z3.And(a>0,b>0))
    s.assume("short_arc",a+b<z3.RealVal("1/6"))
    s.assume("root_bounds",z3.And(x>z3.RealVal("1/2"),x<z3.RealVal("3/4"),y>z3.RealVal("1/2"),y<z3.RealVal("3/4")))
    s.assume("degree_rows",z3.And(rs<=x*(1-a),rt<=y*(1-b)))
    s.assume("positive_defect",rs+rt+a*b>z3.RealVal("5/4"))
    s.claim(z3.And(x-z3.RealVal("1/2")>11*a*b,
                   y-z3.RealVal("1/2")>11*a*b))
    s.role("consumer")
    s.pending("other_G1_cases","Algebraic implication only; universal arc reinsertion OPEN")
    return s
