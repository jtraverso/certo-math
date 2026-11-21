"""Exact, solver-independent regression for S595 cross-heavy max flow.
This tests finite physical graphs, NOT the universal Erdős problem."""
import importlib.util
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
P=ROOT/"research"/"erdos149_s595_cross_flow.py"
spec=importlib.util.spec_from_file_location("erdos149_s595_cross_flow",str(P))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
from fractions import Fraction as F

def make_path(remote=False):
    masses={str(i):m for i,m in enumerate(
        ["7/10","9/10","1/4","1/20","1/20","1/4","9/10","7/10"])}
    edges=[[str(i),str(i+1)] for i in range(7)]
    if remote:
        for j in range(5):masses["c"+str(j)]="1/2"
        for j in range(5):edges.append(["c"+str(j),"c"+str((j+1)%5)])
    return {"masses":masses,"edges":edges,"s":"0","t":"7","a":"1/10","b":"1/10"}

for label,record in [("path",make_path(False)),("remote_C5",make_path(True))]:
    result=module.evaluate(record)
    assert result["residual"] and result["status"]=="PASS",(label,result)
    assert result["nu_cross"]=="0",(label,result)
    assert F(result["cut_capacity"])==F(result["nu_cross"])
    if label=="remote_C5": assert result["heavy_edges"]==5
    print(label, "PASS", "nu_cross=",result["nu_cross"],"threshold=",result["threshold_exact"])

witness={"masses":{"1":"97/100","2":"1/200","3":"1/200","4":"97/100","5":"3/10","6":"1/200","7":"1/200","8":"97/100","10":"97/100","11":"1/200","t":"13/20","s":"13/20"},"edges":[["t","1"],["1","2"],["1","5"],["2","3"],["2","7"],["3","4"],["3","6"],["4","8"],["s","10"],["10","11"],["11","7"]],"s":"s","t":"t","a":"1/100","b":"1/100"}
result=module.evaluate(witness)
assert result["status"]=="PASS" and result["residual"],result
assert result["D"]=="111/10000",result
assert result["nu_cross"]=="1/40000",result
assert F(result["cut_capacity"])==F(result["nu_cross"])
assert result["cross_pairs"]==1,result
print("rooted_tree_nonzero", "PASS", "nu_cross=",result["nu_cross"],
      "threshold=",result["threshold_exact"])


# The two-connected near-tight adversary.  Verify it without a graph package,
# using rational arithmetic and independent physical compatibility checks.
Q=ROOT/"research"/"erdos149_s595_neartight.py"
s2=importlib.util.spec_from_file_location("erdos149_s595_neartight",str(Q))
g2=importlib.util.module_from_spec(s2);s2.loader.exec_module(g2)
H=g2.build();bounds=g2.bound()
vertices=H["masses"];masses={v:F(w) for v,w in vertices.items()}
edges=[tuple(sorted((u,v))) for u,v in H["edges"]]
es=set(edges)
assert len(vertices)==617 and len(es)==1049
nbr={v:set() for v in vertices}
for u,v in edges:nbr[u].add(v);nbr[v].add(u)
for v in vertices:
    degree=sum((masses[z] for z in nbr[v]),F(0))
    if v in ("s","t"):degree+=F(1,200)
    assert degree<=1,(v,degree)
# No articulation: for each deleted vertex, all others remain connected.
for deleted in vertices:
    root=next(v for v in vertices if v!=deleted)
    seen={root};queue=[root]
    for v in queue:
        for w in nbr[v]:
            if w!=deleted and w not in seen:
                seen.add(w);queue.append(w)
    assert len(seen)==len(vertices)-1,("articulation",deleted)

def compatible(e,f,physical):
    return not(set(e)&set(f)) and not any(tuple(sorted((u,v))) in physical
                                          for u in e for v in f)
leaves=[f"{r}e{i}_{k}_{j}_{h}" for r in ("s","t") for i in range(4)
        for k in range(3) for j in range(3) for h in range(6)]
assert len(leaves)==432
ring=[tuple(sorted((leaves[i],leaves[(i+1)%len(leaves)])))
      for i in range(len(leaves))]
ring_set=set(ring)
c5=[e for e in edges if e[0].startswith("c") and e[1].startswith("c")]
links=[e for e in edges if any(x.startswith("omega") for x in e)]
tree=[e for e in edges if e not in ring_set and e not in c5 and e not in links]
assert len(c5)==5 and len(links)==4 and len(tree)==608
special=[e for e in tree if any(v.startswith(("se","te")) and v.endswith("_5") for v in e)]
assert len(special)==72
special_set=set(special);forest=[e for e in tree if e not in special_set]
assert len(forest)==536
tree_set=set(tree)
# The forest's feasible bipartite palette remains legal after adding all
# the physical ring + omega + C5 connectors.
for i,e in enumerate(forest):
    for f in forest[i+1:]:
        assert not (compatible(e,f,tree_set) and not compatible(e,f,es)),(e,f)
# The 72 deleted leaf-edges form one induced matching.
for i,e in enumerate(special):
    for f in special[i+1:]:assert compatible(e,f,es),(e,f)
# Each residue class mod 3 of the 432 ring edges is an induced matching.
for offset in range(3):
    color=[tuple(sorted((leaves[i],leaves[(i+1)%len(leaves)])))
           for i in range(offset,len(leaves),3)]
    for i,e in enumerate(color):
        for f in color[i+1:]:assert compatible(e,f,es),(e,f)
# Core and C5 palettes can share the same colors: no physical cross-conflicts.
for e in tree+ring:
    for f in c5:assert compatible(e,f,es),(e,f)
assert bounds["core"]==F(73,64)
assert bounds["C5_lower"]>bounds["K_minus_ab"]
assert bounds["QH_upper"]<F(5,4) and bounds["QF_upper"]<F(5,4)
result=module.evaluate(H)
assert result["residual"] and result["status"]=="INCONCLUSIVE",result
assert result["nu_cross"]=="2587/2000",result
assert F(result["cut_capacity"])==F(result["nu_cross"])
print("connected_no_articulations_neartight", "PASS",
      "n=617 m=1049", "QH_lower=",bounds["C5_lower"],
      "QH_upper=",bounds["QH_upper"],"nu_cross=",result["nu_cross"])
