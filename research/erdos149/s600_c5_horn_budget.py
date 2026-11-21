"""S600 universal physical C5 incidence-budget verification by exact rationals.

The analytical theorem is: for nonnegative cycle masses m_i with
m_(i-1)+m_(i+1)<=1, sum(m_i)-sum(m_i*m_(i+1))<=5/4.
If e crosses from C5 to its exterior, exact row counting gives
sum(C5 edge weights)+sum(external incidence weights)<=5/4.

The proof reduces its slack to weighted Mantel on a five-cycle.
The implementation replays the compression-to-clique proof for arbitrary
rational z>=0, with exact cost monotonicity at every transfer.
"""
from fractions import Fraction as F
from itertools import combinations
import json,sys
K=F(5,4)

def mantel(z):
    z=[F(q) for q in z]
    assert len(z)==5 and all(q>=0 for q in z)
    edges={frozenset((i,(i+2)%5)) for i in range(5)}
    def energy():
        return sum((z[i]*z[(i+2)%5] for i in range(5)),F())
    initial=energy();total=sum(z,F());count=0
    while True:
        pair=next(((i,j) for i,j in combinations(range(5),2)
                   if z[i]>0 and z[j]>0 and frozenset((i,j)) not in edges),None)
        if pair is None:break
        i,j=pair
        gi=sum((z[k] for k in range(5) if frozenset((i,k)) in edges),F())
        gj=sum((z[k] for k in range(5) if frozenset((j,k)) in edges),F())
        old=energy()
        if gi>=gj:z[i]+=z[j];z[j]=F()
        else:z[j]+=z[i];z[i]=F()
        assert energy()>=old and sum(z,F())==total
        count+=1
    assert sum(q>0 for q in z)<=2
    assert 4*energy()<=total*total and initial<=energy()
    return {"slack":total*total-4*initial,"steps":count}

def audit(data,cycle):
    mass={str(v):F(str(q)) for v,q in data["masses"].items()}
    physical={tuple(sorted(map(str,e))) for e in data["edges"]}
    assert len(cycle)==5 and len(set(cycle))==5
    N={v:set() for v in mass}
    for u,v in physical:N[u].add(v);N[v].add(u)
    assert all(sum((mass[w] for w in N[v]),F())<=1 for v in mass)
    assert all(tuple(sorted((cycle[i],cycle[(i+1)%5]))) in physical for i in range(5))
    m=[mass[v] for v in cycle]
    W=sum((m[i]*m[(i+1)%5] for i in range(5)),F())
    z=[1-m[i]-m[(i+2)%5] for i in range(5)]
    assert all(q>=0 for q in z)
    certificate=mantel(z)
    assert 4*(K-sum(m,F())+W)==certificate["slack"]
    C=set(cycle)
    outside=[sum((mass[w] for w in N[cycle[i]] if w not in C),F()) for i in range(5)]
    incident=sum((m[i]*outside[i] for i in range(5)),F())
    row_slack=[1-m[i-1]-m[(i+1)%5]-outside[i] for i in range(5)]
    assert all(x>=0 for x in row_slack)
    leftover=K-W-incident
    assert leftover==certificate["slack"]/4+sum((m[i]*row_slack[i] for i in range(5)),F())
    assert leftover>=0
    return {"status":"PASS_EXACT","cycle_weight":str(W),
            "incident_crossing_weight":str(incident),
            "remaining_budget":str(leftover),
            "horn_mantel_slack":str(certificate["slack"]),
            "weighted_row_slack":str(sum((m[i]*row_slack[i] for i in range(5)),F())),
            "compression_steps":certificate["steps"],
            "scope":"one rational instance of universal analytical C5 budget"}
if __name__=="__main__":
    from s600_neartight_fixture import make
    data=make()
    print(json.dumps(audit(data,["C0","C1","C2","C3","C4"]),indent=2))
