"""Erdos149 S600: exact rational near-extremal C5 collar audit.

Given W5>=5/4-ab, root masses and all physical rows feasible,
every cycle mass is within 2ab of 1/2 and C5 has no chords.
Crossing incident weight <= ab; the second-layer interference
weight <=(37/35)ab; total weight conflicting with C5 outside
the cycle <=(72/35)ab.

Only one rational instance is checked here. A separate analytical
argument proves the inequalities for all real inputs.
"""
from fractions import Fraction as F
import json
import networkx as nx
from s600_c5_horn_budget import audit
K=F(5,4)

def key(u,v):return tuple(sorted((str(u),str(v))))
def check(data,cycle):
    m={str(v):F(str(w)) for v,w in data["masses"].items()}
    physical={key(*e) for e in data["edges"]}
    s,t=str(data["s"]),str(data["t"])
    a,b=F(str(data["a"])),F(str(data["b"]))
    delta=a*b
    assert F(0)<delta<F(1,144) and a+b<F(1,6)
    G=nx.Graph();G.add_nodes_from(m);G.add_edges_from(physical)
    assert all(F(0)<v for v in m.values())
    assert all(sum((m[u] for u in G.neighbors(v)),F())+
               (a if v==s else b if v==t else F())<=1 for v in m)
    cycle=list(map(str,cycle));V=set(cycle)
    assert len(V)==5
    base=audit(data,cycle);W=F(base["cycle_weight"])
    assert W>=K-delta
    L=F(1,2)-2*delta
    for v in cycle:assert L<m[v]<1-L,(v,m[v],L)
    inside={e for e in physical if set(e)<=V}
    assert len(inside)==5,("C5 must be induced in this regime",inside)
    for r in (s,t):
        assert not nx.has_path(G,r,cycle[0]) or all(
            not nx.has_path(G,r,v) or nx.shortest_path_length(G,r,v)>=3
            for v in cycle)
    X={u for v in cycle for u in G.neighbors(v) if u not in V}
    assert all(m[u]<4*delta for u in X)
    crossing={e for e in physical if len(set(e)&V)==1}
    annulus={e for e in physical if not(set(e)&V) and set(e)&X}
    W1=sum((m[e[0]]*m[e[1]] for e in crossing),F())
    W2=sum((m[e[0]]*m[e[1]] for e in annulus),F())
    assert W1<=delta and W2<=F(37,35)*delta
    assert W1+W2<=F(72,35)*delta
    assert W1==F(base["incident_crossing_weight"])
    rs=m[s]*sum((m[u] for u in G.neighbors(s)),F())
    rt=m[t]*sum((m[u] for u in G.neighbors(t)),F())
    D=rs+rt+delta-K
    assert D>0
    return {"status":"PASS_C19_RATIONAL","n":len(m),"edges":len(physical),
            "C5_weight":str(W),"ab":str(delta),
            "first_ring_demand":str(W1),"second_ring_demand":str(W2),
            "combined_ring_demand":str(W1+W2),
            "universal_bound":str(F(72,35)*delta),
            "number_of_ring_vertices":len(X),"D":str(D),
            "root_min_distances":[min((nx.shortest_path_length(G,r,v)
                for v in cycle if nx.has_path(G,r,v)),default=None) for r in (s,t)],
            "G1_universal":"OPEN"}
if __name__=="__main__":
    from s600_neartight_fixture import make
    from s597_pg4_3conn_hard import build
    for name,d in [("19_neartight",make()),("70_PG4",build())]:
        print(json.dumps({"name":name,**check(d,["C0","C1","C2","C3","C4"])},indent=2))
