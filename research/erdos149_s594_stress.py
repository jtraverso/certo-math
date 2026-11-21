"""Erdos149 S594: parametric 400-vertex *nonminimal* stress input.

Generates physical graph H and exact masses.  For eps = 1/10^6:
  n=400, |E|=400, D=1741/40000,
  Q_H=5(1-eps)^2/4 by weighted clique gluing,
  K-ab < Q_H < K.
The original S593 directed-flow tests do not close the arc:
per-root nu=2443/4000>3/5.  This graph has articulations and is NOT
a counterexample to the conjecture; it is a counterexample to the
SUFFICIENCY of scalar filters alone.  Requires no dependencies.
"""
import json
from fractions import Fraction as F

def build(eps=F(1,1000000)):
    m={"s":F(13,20),"t":F(13,20)}
    ed=[]
    for r in ("s","t"):
        for i in range(4):
            a=f"{r}a{i}"
            m[a]=F(199,800)
            ed.append((r,a))
            for k in range(3):
                z=f"{r}z{i}_{k}"
                m[z]=F(7,60)
                ed.append((a,z))
                for j in range(3):
                    v=f"{r}v{i}_{k}_{j}"
                    d=f"{r}d{i}_{k}_{j}"
                    m[v],m[d]=F(1,4),F(3,4)
                    ed.extend([(z,v),(v,d)])
                    for h in range(3):
                        leaf=f"{r}e{i}_{k}_{j}_{h}"
                        m[leaf]=F(1,4)
                        ed.append((d,leaf))
    ed.append(("se0_0_0_0","te0_0_0_0"))
    m["omega"]=eps
    c=(1-eps)/2
    for i in range(5):
        m[f"c{i}"]=c
        ed.append((f"c{i}",f"c{(i+1)%5}"))
    ed.extend([("se0_0_0_1","omega"),("omega","c0")])
    nbr={v:[] for v in m}
    for u,v in ed:
        nbr[u].append(v)
        nbr[v].append(u)
    assert len(m)==400 and len(ed)==400
    for v in m:
        row=sum((m[w] for w in nbr[v]),F(0))
        if v in ("s","t"): row+=F(1,200)
        assert row<=1,(v,row)
    assert 0<eps<F(1,100000)
    Q=5*c*c
    K=F(5,4)
    ab=F(1,40000)
    assert K-ab<Q<K
    assert eps*c<=c*c
    D=sum((m[r]*sum((m[z] for z in nbr[r]),F(0)) for r in ("s","t")),F(0))+ab-K
    assert D==F(1741,40000)
    return {
        "masses":{v:str(w) for v,w in m.items()},
        "edges":ed,
        "s":"s", "t":"t", "a":"1/200", "b":"1/200",
        "meta":{"n":400,"edges":400,"eps":str(eps),"Q_H":str(Q),"D":str(D),
                "note":"Not minimal; has articulations; scalar S593 filters inconclusive."}
    }

if __name__=="__main__":
    import sys
    eps=F(sys.argv[1]) if len(sys.argv)>1 else F(1,1000000)
    obj=build(eps)
    print(json.dumps(obj,indent=2))
