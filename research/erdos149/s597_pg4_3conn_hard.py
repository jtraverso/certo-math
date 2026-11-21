"""Reproduce S597's 70-vertex 3-connected near-tight adversarial graph.

PG(2,4) is built from GF(4), not from an opaque edge list.
The graph obeys every weighted row with x=y=7/10, a=b=1/20.
All masses are positive <3/4. Its S591 local gate is ultimately PASS
by an explicit composition: bipartite PG/root core cost <=1,
arc cost 29/400, physically independent C5 palette, and tiny
connector bands. This is NOT a counterexample to Erdos #149.
"""
from fractions import Fraction as Q
from itertools import product
import json,sys

GF4=((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))
INV={1:1,2:3,3:2}
K=Q(5,4)
REMOVED={
    ("P14","L12"),("P20","L13"),("P17","L16"),("P4","L18"),
    ("P2","L2"),("P7","L20"),("P19","L3"),("P0","L5")
}
ATTACH={"sa0":17,"sa1":0,"sa2":19,"sa3":4,
        "ta0":7,"ta1":2,"ta2":14,"ta3":20}
W_LINES=(("L11","L17"),("L1","L9"),("L19","L15"),("L13","L4"),
         ("L14","L16"),("L20","L3"),("L8","L10"),("L18","L0"))

def normalize(v):
    v=tuple(v)
    for a in v:
        if a:return tuple(GF4[INV[a]][z] for z in v)
    raise ValueError("zero vector")

def build():
    points=sorted({normalize(x) for x in product(range(4),repeat=3)
                   if x!=(0,0,0)})
    assert len(points)==21
    incidence=[(f"P{i}",f"L{j}") for i,p in enumerate(points)
               for j,l in enumerate(points)
               if GF4[p[0]][l[0]]^GF4[p[1]][l[1]]^GF4[p[2]][l[2]]==0]
    assert len(incidence)==105 and REMOVED<=set(incidence)
    mass={"s":Q(7,10),"t":Q(7,10)}
    edges=[(r,f"{r}a{i}") for r in ("s","t") for i in range(4)]
    for r in ("s","t"):
        for i in range(4):mass[f"{r}a{i}"]=Q(19,80)
    for i in range(21):mass[f"P{i}"]=mass[f"L{i}"]=Q(19,100)
    edges.extend(e for e in incidence if e not in REMOVED)
    for a,p in ATTACH.items():edges.append((a,f"P{p}"))
    for i,(u,v) in enumerate(W_LINES):
        w=f"W{i}";mass[w]=Q(1,100)
        a=f"sa{i}" if i<4 else f"ta{i-4}"
        edges.extend(((a,w),(w,u),(w,v)))
    eps=Q(1,100000);delta=eps/2;c=(1-eps)/2
    for i in range(5):
        mass[f"C{i}"]=c;mass[f"omega{i}"]=delta
        edges.extend(((f"C{i}",f"C{(i+1)%5}"),
                      (f"omega{i}",f"C{i}"),
                      (f"omega{i}",f"P{4*i}"),
                      (f"omega{i}",f"L{(4*i+3)%21}")))
    assert len(mass)==70 and len(edges)==157
    row={v:Q() for v in mass}
    for u,v in edges:row[u]+=mass[v];row[v]+=mass[u]
    for v,d in row.items():
        assert d+(Q(1,20) if v in ("s","t") else Q())<=1,(v,d)
    return {"masses":{v:str(w) for v,w in mass.items()},
            "edges":[list(e) for e in edges],"s":"s","t":"t",
            "a":"1/20","b":"1/20"}

def budget():
    eps=Q(1,100000);delta=eps/2;c=(1-eps)/2
    q_c5=5*c*c
    connector=5*delta*(c+Q(19,50))
    arc=Q(29,400)   # x*a + a*b + b*y
    lower=q_c5
    upper=max(Q(1),q_c5)+connector
    upper_f=max(Q(1)+arc,q_c5)+connector
    assert lower>K-Q(1,400)
    assert upper_f<K and upper<=upper_f
    assert upper_f==Q(1249997,1000000)
    return {"QH_lower":str(lower),"QH_upper":str(upper),
            "QF_upper":str(upper_f),"arc_band":str(arc),
            "connector_band":str(connector),"K":"5/4",
            "requires":"The previously proved weighted bipartite bound Q<=1 for the PG/root component"}

if __name__=="__main__":
    graph=build()
    if len(sys.argv)>1:
        with open(sys.argv[1],"w",encoding="utf8") as f:
            json.dump(graph,f,indent=2,ensure_ascii=False)
    print(json.dumps({"vertices":len(graph["masses"]),"edges":len(graph["edges"]),**budget()},indent=2))
