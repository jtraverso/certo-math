"""S597 exact weighted-core and adversarial graph checks.

Everything is checked using Fraction (no floating point), except the
independent 3-connectivity test via NetworkX.  Inconclusive filters
must remain INCONCLUSIVE; they are not falsifications of Erdős #149.
"""
import sys,json
from pathlib import Path
from fractions import Fraction as Q
import networkx as nx

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE))
sys.path.insert(0,str(HERE.parent))
from s597_verify_static_palettes import decode
from s597_weighted_core import analyze,verify
from s597_pg4_3conn_hard import build,budget
from s597_clique_absorb import assess as split_c12
from s597_proof_router import route
from erdos149_s595_neartight import build as build_617
from erdos149_s595_cross_flow import evaluate as c10
from s596_c11 import evaluate as c11

cases=[
    ("tree23",decode("tree23"),22,4,8),
    ("core18",decode("core18"),39,8,2),
    ("nearK_617",build_617(),1049,8,170),
]
for name,data,m,root,heavy in cases:
    p=analyze(data);assert verify(data,p)
    assert p["status"]=="PASS_ROOT_ONLY",(name,p)
    assert p["edges"]==m and p["core_nonroot"]==0 and p["initial_heavy"]==heavy,p
    assert p["removed_count"]==m-root
    assert Q(p["root_flow"])==min(Q(p["r_s"]),Q(p["r_t"]))
    assert route(data)["method"]=="weighted_core"
    print(json.dumps({"name":name,"status":p["status"],"peeled":p["removed_count"],
                      "initial_heavy":p["initial_heavy"],"residual_core":0}))

hard=build();assert len(hard["masses"])==70 and len(hard["edges"])==157
G=nx.Graph();G.add_nodes_from(hard["masses"]);G.add_edges_from(hard["edges"])
assert nx.node_connectivity(G)>=3
assert min(dict(G.degree()).values())>=3
assert not nx.is_bipartite(G)
assert all(Q(w)>0 and Q(w)<Q(3,4) for w in hard["masses"].values())
masks=budget()
cycle=[[f"C{i}",f"C{(i+1)%5}"] for i in range(5)]
proof12=split_c12(hard,cycle)
assert proof12["status"]=="PASS_C12" and proof12["L"]==137
assert proof12["R"]==5 and proof12["C"]==15
assert proof12["QF_upper"]==masks["QF_upper"]
smart=route(hard)
assert smart["status"]=="PASS" and smart["method"]=="C12_clique_absorption",smart
assert Q(smart["certificate"]["QF_upper"])==Q(1249997,1000000)
# The decomposition is a parametric mathematical family, not just one fixture.
for epsilon in (Q(1,1000),Q(1,10000),Q(1,100000),Q(1,1000000)):
    inst=build(epsilon)
    report=split_c12(inst,cycle)
    assert report["status"]=="PASS_C12",report
    assert Q(report["QF_upper"])==Q(5,4)-Q(3,10)*epsilon
    assert Q(report["QH_lower"])>Q(5,4)-Q(1,400)
assert Q(masks["QH_lower"])>Q(5,4)-Q(1,400)
assert Q(masks["QF_upper"])<Q(5,4)
p=analyze(hard);assert verify(hard,p)
assert p["status"]=="OPEN_KERNEL",p
assert p["core_nonroot"]==p["anchored_nonroot"]==111,p
assert p["removed_count"]==38,p
r10=c10(hard);r11=c11(hard,100000)
assert r10["status"]=="INCONCLUSIVE" and r10["nu_cross"]=="133/100",r10
assert r11["status"]=="INCONCLUSIVE" and r11["heavy"]==126,r11
print(json.dumps({"name":"GF4_70_3conn_nearK","status":"OPEN_KERNEL",
    "connected":True,"three_connected":True,"bipartite":False,
    "n":len(G),"m":G.number_of_edges(),
    "core_nonroot":p["core_nonroot"],"anchored_nonroot":p["anchored_nonroot"],
    "C10":r10["status"],"C11":r11["status"],"C12":proof12["status"],"C10_flow":r10["nu_cross"],
    **masks},ensure_ascii=False))
