"""C18-B: construct an exact K=5/4 palette for BOTH old root stars,
a near-tight physical C5, and ALL crossing incident C5 edges.

This supports arbitrary physical H with S591 heavy-residual rows.
It does NOT color other old edges and cannot by itself close G1 globally.
All compatibility tests use original physical H.
"""
from fractions import Fraction as F
from collections import defaultdict
import json
import networkx as nx
from s599_paired_shadow import load_model,hall_colors,K
from s600_c5_horn_budget import audit

def edge(u,v):return tuple(sorted((str(u),str(v))))
def construct(data,cycle):
    assert len(cycle)==5 and len(set(cycle))==5
    m={str(v):F(str(w)) for v,w in data["masses"].items()}
    E,w,conf,S,T,ab=load_model(data)
    D=sum((w[i] for i in S+T),F())+ab-K
    assert D>0
    G=nx.Graph();G.add_nodes_from(m)
    G.add_edges_from(E)
    for r in (str(data["s"]),str(data["t"])):
        for v in cycle:
            assert r!=v
            assert not nx.has_path(G,r,v) or nx.shortest_path_length(G,r,v)>=3,(r,v)
    cycle_idx=[]
    for i in range(5):
        e=edge(cycle[i],cycle[(i+1)%5])
        assert e in E
        cycle_idx.append(E.index(e))
    assert len(set(cycle_idx))==5
    W=sum((w[i] for i in cycle_idx),F())
    assert W>=K-ab
    P,rs,rt=hall_colors(w,conf,S,T)
    B=max(rs,rt);Jtarget=min(rs,rt)
    assert B<W
    root=[(mask,amount) for mask,amount in P if mask]
    assert sum((amount for _,amount in root),F())==B
    root.append((frozenset(),W-B))
    cyc=[(frozenset((i,)),w[i]) for i in cycle_idx]
    def intervals(P):
        t=F();r=[]
        for M,amount in P:
            assert amount>0
            r.append((t,t+amount,M));t+=amount
        return r
    A=intervals(root);C=intervals(cyc)
    cuts=sorted({F()}|{u for lo,hi,M in A+C for u in (lo,hi)})
    palette=[]
    for a,b in zip(cuts,cuts[1:]):
        if a==b:continue
        P1=next((mask for lo,hi,mask in A if lo<=a and b<=hi),frozenset())
        P2=next((mask for lo,hi,mask in C if lo<=a and b<=hi),frozenset())
        palette.append((P1|P2,b-a))
    V=set(cycle)
    incident=[i for i,e in enumerate(E) if len(V&set(e))==1]
    for i in incident:palette.append((frozenset((i,)),w[i]))
    Winc=sum((w[i] for i in incident),F())
    assert W+Winc<=K
    palette.append((frozenset(),K-W-Winc))
    covered=defaultdict(F);J=F()
    for M,amount in palette:
        if not amount:continue
        assert amount>0
        for i in M:
            assert not ((M-{i})&conf[i]),(E[i],M)
            covered[i]+=amount
        if set(M)&set(S) and set(M)&set(T):J+=amount
    demanded=set(S+T+cycle_idx+incident)
    assert set(covered)==demanded
    assert all(covered[i]==w[i] for i in demanded)
    assert J==Jtarget and J>=D
    cert=audit(data,cycle)
    assert F(cert["cycle_weight"])==W and F(cert["incident_crossing_weight"])==Winc
    return {"status":"PASS_C18_SUPPORT","vertices":len(m),"physical_edges":len(E),
            "covered_edges":len(demanded),"uncovered_edges":len(E)-len(demanded),
            "cycle_weight":str(W),"incidence_weight":str(Winc),
            "slack":str(K-W-Winc),"J":str(J),"D":str(D),
            "palette_classes":len(palette),
            "cycle_budget":cert,
            "universal_G1":"OPEN unless uncovered_edges=0"}
if __name__=="__main__":
    from s600_neartight_fixture import make
    from s597_pg4_3conn_hard import build
    for name,d in [("19_neartight",make()),("70_PG4",build())]:
        out=construct(d,["C0","C1","C2","C3","C4"])
        print(json.dumps({"name":name,**{k:v for k,v in out.items()
         if k!="cycle_budget"}},ensure_ascii=False))
