"""C12: exact physical clique-absorber / two-scale split certificate.

Given an old weighted graph H and a strong clique R of its old edges:
 L = all old edges compatible with every edge in R;
 C = all remaining old edges outside R and L.

If the graph on L is bipartite and physically induced in H, and
each new arc edge is compatible with R, the prior weighted bipartite
bound Q_L<=1 supplies a width-(1+w_arc) palette for L+arc.
Overlay R singleton palette and spend w(C) on connector singletons.

Q_F <= max(1+w_arc, w(R)) + w(C).
This is a sufficient criterion, not a universal theorem.
"""
from fractions import Fraction as Q
import json,sys
import networkx as nx
K=Q(5,4)

def pair(u,v):
    u,v=str(u),str(v)
    assert u!=v
    return tuple(sorted((u,v)))

def assess(data,R_edges):
    m={str(k):Q(str(v)) for k,v in data["masses"].items()}
    E={pair(*e) for e in data["edges"]}
    R={pair(*e) for e in R_edges}
    assert R and R<=E
    def strong_conflict(e,f,physical=E):
        return bool(set(e)&set(f)) or any(pair(u,v) in physical for u in e for v in f)
    # Pairwise strong conflicts certify Q_R = sum(w_R), not just an upper bound.
    assert all(strong_conflict(a,b) for i,a in enumerate(sorted(R))
               for b in sorted(R)[i+1:])
    L={e for e in E-R if all(not strong_conflict(e,r) for r in R)}
    C=E-R-L
    V={v for e in L for v in e}
    # Extra physical connector edges between endpoints in L could invalidate
    # a bipartite palette that was only induced in the smaller L-subgraph.
    assert all(e in L for e in E if e[0] in V and e[1] in V)
    G=nx.Graph();G.add_nodes_from(V);G.add_edges_from(L)
    assert nx.is_bipartite(G)
    s,t=data["s"],data["t"]
    u,v="_new_u","_new_v"
    assert u not in m and v not in m
    new=[pair(s,u),pair(u,v),pair(v,t)]
    physical=E|set(new)
    assert all(not strong_conflict(e,r,physical) for e in new for r in R)
    a,b=Q(str(data["a"])),Q(str(data["b"]))
    wnew=m[s]*a+a*b+b*m[t]
    wr=sum((m[p]*m[q] for p,q in R),Q())
    wc=sum((m[p]*m[q] for p,q in C),Q())
    upper=max(Q(1)+wnew,wr)+wc
    return {"status":"PASS_C12" if upper<=K else "NO_CERTIFICATE",
            "L":len(L),"R":len(R),"C":len(C),
            "w_arc":str(wnew),"w_clique":str(wr),"w_connectors":str(wc),
            "QH_lower":str(wr),"QF_upper":str(upper),"K":"5/4",
            "external_premise":"weighted bipartite Q_L<=1 (S591)",
            "physical_shortcuts_excluded":True,
            "root_compatible_clique":True}

if __name__=="__main__":
    with open(sys.argv[1],encoding="utf8") as f: data=json.load(f)
    R=[[f"C{i}",f"C{(i+1)%5}"] for i in range(5)]
    print(json.dumps(assess(data,R),indent=2))
