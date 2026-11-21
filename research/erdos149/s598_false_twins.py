"""S598 exact false-twin vertex compression in weighted physical graphs.

Two distinct nonadjacent vertices u,v with identical open neighborhoods
may be merged as z with m_z=m_u+m_v, preserving every row constraint
and both the weighted strong-edge palette cost Q and Jmax provided
u,v are not the marked roots. Reversible palette maps are given below.
"""
from fractions import Fraction as F


def edge(u,v):
    u,v=str(u),str(v)
    assert u!=v
    return tuple(sorted((u,v)))


def compress(data,u,v,z):
    u,v,z=str(u),str(v),str(z)
    assert u!=v and u not in (data["s"],data["t"]) and v not in (data["s"],data["t"])
    m={str(k):F(str(q)) for k,q in data["masses"].items()}
    assert z not in m and u in m and v in m
    N={w:set() for w in m}
    for a,b in data["edges"]:
        N[a].add(b);N[b].add(a)
    assert N[u]==N[v] and v not in N[u]
    m[z]=m.pop(u)+m.pop(v)
    es=sorted({edge(z if a in (u,v) else a,z if b in (u,v) else b)
               for a,b in data["edges"]})
    return {**data,"masses":{k:str(q) for k,q in m.items()},
            "edges":[list(e) for e in es]}


def project(palette,u,v,z):
    answer=[]
    for color in palette:
        e=[list(edge(z if a in (u,v) else a,z if b in (u,v) else b))
           for a,b in color["edges"]]
        assert len(e)==len({tuple(f) for f in e})
        answer.append({"width":str(color["width"]),"edges":e})
    return answer


def lift(palette,u,v,z,mu,mv):
    mu,mv=F(str(mu)),F(str(mv))
    assert mu>0 and mv>0
    answer=[]
    for color in palette:
        edges=[edge(*e) for e in color["edges"]]
        if not any(z in e for e in edges):
            answer.append({"width":str(color["width"]),
                           "edges":[list(e) for e in edges]})
            continue
        assert sum(z in e for e in edges)==1
        for old,ratio in ((u,mu/(mu+mv)),(v,mv/(mu+mv))):
            answer.append({"width":str(F(str(color["width"]))*ratio),
                "edges":[list(edge(old if a==z else a,old if b==z else b))
                         for a,b in edges]})
    return answer
