"""Erdos149 S597 exact two-scale budget for 0<eps<=1/1000.

Let c=(1-eps)/2, delta=eps/2, Q(C5)=5c^2, and
connector-demand=5*delta*(c+19/50).
The split argument (separate combinatorial proof) yields

Q_F <= max(1+29/400, 5c^2)+5delta(c+19/50)
    = 5/4-3eps/10 < 5/4.

Also 5c^2 > 5/4 - ab where a=b=1/20, for
every eps in (0, 1/1000]. This spec proves only the REAL
polynomial identities/inequalities, not the graph split.
"""
import z3
from certo import Spec

def spec():
    e=z3.Real("eps")
    K=z3.RealVal("5/4")
    c=(1-e)/2
    delta=e/2
    clique=5*c*c
    connectors=5*delta*(c+z3.RealVal("19/50"))
    arc=z3.RealVal("29/400")
    s=Spec(title="Erdos149 S597 symbolic two-scale absorption budget")
    s.assume("eps_positive",e>0)
    s.assume("eps_small",e<=z3.RealVal("1/1000"))
    s.claim(z3.And(
        clique> K-z3.RealVal("1/400"),
        clique>=1+arc,
        clique+connectors==K-z3.RealVal("3/10")*e,
        clique+connectors<K
    ))
    s.role("consumer")
    s.pending("physical_split","The CLI certifies only algebra; C12 checks graph compatibility.")
    return s
