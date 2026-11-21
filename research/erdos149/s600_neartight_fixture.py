"""S600 finite physical near-tight witness outside C15-P, with exact palette.

At eps=1/10^6, H has 19 vertices and 19 edges; a clique separator
of order 2 in its physical conflict graph isolates a root-free
branch of 8 demand edges including all five C5 edges.

The full exact K-palette is independently constructed: synchronise
four root pairs, add the A0-B0 edge as a singleton, overlay the
physically compatible C5 clique palette, and pay five connector edges
on a separate band. This tests S600 but does NOT prove G1 universal.
"""
from __future__ import annotations
from fractions import Fraction as F
from collections import defaultdict
import json,sys
from s600_conflict_clique_cut import prune,key
K=F(5,4)

def make(eps=F(1,1000000)):
    eps=F(str(eps))
    assert F(0)<eps<F(1,10000)
    d=eps/2;c=(1-eps)/2
    mass={"s":F(7,10),"t":F(7,10)}
    for side in "AB":
        for i in range(4):mass[f"{side}{i}"]=F(19,80)
    for i in range(4):mass[f"z{i}"]=d
    for i in range(5):mass[f"C{i}"]=c
    edges=[key("s",f"A{i}") for i in range(4)]
    edges +=[key("t",f"B{i}") for i in range(4)]
    edges +=[key("A0","B0"),key("A0","z0"),key("z0","z1"),
            key("z1","z2"),key("z2","z3"),key("z3","C0")]
    edges +=[key(f"C{i}",f"C{(i+1)%5}") for i in range(5)]
    assert len(mass)==19 and len(set(edges))==19
    adj={v:set() for v in mass}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    assert all(F(0)<w<F(3,4) for w in mass.values())
    for v in mass:
        row=sum((mass[z] for z in adj[v]),F())
        if v in ("s","t"):row+=F(1,20)
        assert row<=1,(v,row)
    return {"masses":{v:str(w) for v,w in mass.items()},
            "edges":[list(e) for e in edges],
            "s":"s","t":"t","a":"1/20","b":"1/20"}

def cert(data):
    m={v:F(w) for v,w in data["masses"].items()}
    E={key(*e) for e in data["edges"]}
    def compatible(e,f):
        return not(set(e)&set(f)) and all(key(u,v) not in E for u in e for v in f)
    c=m["C0"];eps=1-2*c
    cycle=[(frozenset([key(f"C{i}",f"C{(i+1)%5}")]),c*c) for i in range(5)]
    perm=(1,0,2,3)
    rw=m["s"]*m["A0"]
    root=[(frozenset([key("s",f"A{i}"),key("t",f"B{perm[i]}")]),rw)
          for i in range(4)]
    root.append((frozenset([key("A0","B0")]),m["A0"]*m["B0"]))
    cr=sum((w for _,w in cycle),F())
    rr=sum((w for _,w in root),F())
    assert cr>rr
    root.append((frozenset(),cr-rr))
    def intervals(seq):
        out=[];t=F()
        for mask,width in seq:
            out.append((t,t+width,mask));t+=width
        return out
    A=intervals(root);B=intervals(cycle)
    knots=sorted({F()}|{v for lo,hi,_ in A+B for v in (lo,hi)})
    palette=[]
    for start,end in zip(knots,knots[1:]):
        r=next((mask for lo,hi,mask in A if lo<=start and end<=hi),frozenset())
        b=next((mask for lo,hi,mask in B if lo<=start and end<=hi),frozenset())
        palette.append((r|b,end-start))
    connectors=[key("A0","z0"),key("z0","z1"),key("z1","z2"),
                key("z2","z3"),key("z3","C0")]
    for e in connectors:palette.append((frozenset([e]),m[e[0]]*m[e[1]]))
    cost=sum((width for _,width in palette),F())
    assert cost<K
    palette.append((frozenset(),K-cost))
    covered=defaultdict(F);J=F()
    for match,width in palette:
        assert width>0
        for e in match:
            assert all(e==f or compatible(e,f) for f in match)
            covered[e]+=width
        if any("s" in e for e in match) and any("t" in e for e in match):
            J+=width
    assert set(covered)==E
    assert all(covered[e]==m[e[0]]*m[e[1]] for e in E)
    assert J==F(133,200)
    D=F(33,400);ab=F(1,400);lower=5*c*c
    assert lower>K-ab and J>D
    assert K*(K-lower)<ab*J
    result=prune(data,max_clique=2)
    assert result["removed"]==8 and result["roots"]==8
    return {"status":"PASS_FINITE","n":len(m),"m":len(E),"J":str(J),
            "D":str(D),"old_Q_lower":str(lower),
            "old_Q_upper":str(cost),"palette_classes":len(palette),
            "clique_separator":result["cuts"][0]["clique"],
            "removed_by_separator":result["removed"],
            "C15_P_provably_not_applicable":True,
            "G1_universal":"OPEN"}

if __name__=="__main__":
    print(json.dumps(cert(make()),indent=2))
