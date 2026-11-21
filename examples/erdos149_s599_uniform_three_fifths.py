"""Erdos #149 S599: universal narrow-slack obstruction factor 3/5.

If the easy G1 branch Q_H<=K-ab has failed, the root rows give
B+ab<3/4, so B/Q_H<3/5. Any obstruction to the constructive
two-palette theorem would require (K-Q_H)Q_H<ab B, hence
K-Q_H<3ab/5. Certo proves the scalar polynomial implication.
"""
import z3
from certo import Spec

def spec():
    K=z3.RealVal("5/4")
    beta,B,ab,sigma=z3.Reals("beta B ab sigma")
    s=Spec(title="Erdos149 S599 uniform sharp 3/5 slack consequence")
    s.assume("ab_positive",ab>0)
    s.assume("root_row",z3.And(B>0,B+ab<z3.RealVal("3/4")))
    s.assume("easy_branch_failed",z3.And(beta>K-ab,beta<=K))
    s.assume("sigma_def",sigma==K-beta)
    s.assume("mixture_obstruction",sigma*beta<ab*B)
    s.claim(z3.And(5*B<3*beta,5*sigma<3*ab))
    s.role("consumer")
    s.pending("palette_mixing","The necessary mixture_obstruction is proved analytically in S599")
    return s
