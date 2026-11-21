"""S600: exact root-preserving clique separator pruning of L(H)^2.

For demand support T and clique S in the PHYSICAL strong conflict graph,
a component U of C[T]-S disjoint from all root edges can be discarded
without altering Jmax at K=5/4, assuming Q_H<=K.
The proof glues palettes along S by aligning the disjoint S-color
profiles, using a restriction of the original exact K-palette.
This code proves only the graph-combinatorial premises for instances.
"""
from __future__ import annotations
from itertools import combinations
from fractions import Fraction as F
import json,sys
import networkx as nx

def key(u,v):
    u,v=str(u),str(v)
    assert u!=v
    return tuple(sorted((u,v)))

def conflict_graph(data):
    m={str(v):F(str(w)) for v,w in data["masses"].items()}
    E={key(*e) for e in data["edges"]}
    s,t=str(data["s"]),str(data["t"])
    assert s!=t
    adj={v:set() for v in m}
    for u,v in E:
        assert u in m and v in m
        adj[u].add(v);adj[v].add(u)
    C=nx.Graph();C.add_nodes_from(E)
    for a,b in combinations(sorted(E),2):
        if set(a)&set(b) or any(v in adj[u] for u in a for v in b):
            C.add_edge(a,b)
    R={e for e in E if s in e or t in e}
    return C,R

def verify(data,rec):
    C,R=conflict_graph(data);H=C.copy()
    for step in rec["cuts"]:
        S={key(*e) for e in step["clique"]}
        U={key(*e) for e in step["root_free_branch"]}
        assert S<=set(H) and U<=set(H)-S and not U&R and U
        assert all(H.has_edge(a,b) for a,b in combinations(sorted(S),2))
        other=H.copy();other.remove_nodes_from(S)
        assert U in [set(c) for c in nx.connected_components(other)]
        H.remove_nodes_from(U)
        assert R<=set(H)
    assert H.number_of_nodes()==rec["retained"]
    assert sorted(H.nodes)==[key(*e) for e in rec["retained_edges"]]
    return True

def prune(data,max_clique=2,max_support=80):
    C,R=conflict_graph(data)
    if C.number_of_nodes()>max_support:
        return {"status":"UNKNOWN","reason":"support_size_limit",
                "limit":max_support,"old":C.number_of_nodes()}
    H=C.copy();cuts=[]
    while True:
        chosen=None
        V=sorted(H.nodes)
        for size in range(max_clique+1):
            for S in combinations(V,size):
                if any(not H.has_edge(a,b) for a,b in combinations(S,2)):continue
                H2=H.copy();H2.remove_nodes_from(S)
                for U in nx.connected_components(H2):
                    if U and not U&R and len(U)<len(H):
                        key0=(-len(U),size,S)
                        if chosen is None or key0<chosen[0]:
                            chosen=(key0,S,tuple(sorted(U)))
            if chosen:break
        if not chosen:break
        _,S,U=chosen
        cuts.append({"clique":[list(e) for e in S],
                     "root_free_branch":[list(e) for e in U]})
        H.remove_nodes_from(U)
    rec={"status":"REDUCED" if cuts else "NO_SEPARATOR_FOUND",
         "old":len(C),"retained":len(H),
         "removed":len(C)-len(H),"roots":len(R),
         "cuts":cuts,"retained_edges":[list(e) for e in sorted(H.nodes)],
         "hypothesis":"Q_H<=5/4 required for gluing",
         "G1":"OPEN"}
    verify(data,rec)
    return rec

if __name__=="__main__":
    for path in sys.argv[1:]:
        with open(path,encoding="utf8") as f:d=json.load(f)
        r=prune(d)
        print(json.dumps({"file":path,**{k:v for k,v in r.items()
            if k not in ("cuts","retained_edges")}},ensure_ascii=False))
