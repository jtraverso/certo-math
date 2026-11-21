"""S597 certified finite-instance router: peeling -> C5 clique absorption.

No universal theorem is claimed. PASS is returned only with a reproducible
proof witness, an exact rational inequality, and explicit external premises.
OPEN never means the conjecture is false. Physical conflicts use all edges.
"""
from fractions import Fraction as Q
from itertools import combinations
import json, sys
import networkx as nx
from s597_weighted_core import analyze as peel
from s597_clique_absorb import assess as absorb

def canon(e):return tuple(sorted(e))

def candidate_five_cycles(graph):
    # Deduplicate canonical sets of 5 cycle edges.
    E={canon(e) for e in graph.edges}
    out=set()
    for start in graph.nodes:
        def walk(path):
            if len(path)==5:
                if canon((path[-1],start)) in E:
                    out.add(frozenset(canon((path[i],path[(i+1)%5])) for i in range(5)))
                return
            for v in graph[path[-1]]:
                if v!=start and v not in path:
                    walk(path+[v])
        walk([start])
    return [tuple(sorted(c)) for c in out]

def route(data,max_candidates=100):
    m={v:Q(w) for v,w in data["masses"].items()}
    core=peel(data)
    if core["status"] in ("PASS_ROOT_ONLY","PASS_C13_ANCHORED_BUDGET"):
        return {"status":"PASS","method":"weighted_core" if core["status"]=="PASS_ROOT_ONLY" else "C13_anchored_budget",
                "old_edge_count":core["edges"],
                "removed":core["removed_count"],"root_flow":core["root_flow"],
                "anchored_weight":core["anchored_weight"],
                "root_free_core":core["root_free_core"],
                "gate":"arc3","scope":"one finite physical graph, requires Q_H<=5/4"}
    E={canon(e) for e in data["edges"]}
    G=nx.Graph();G.add_nodes_from(m);G.add_edges_from(E)
    candidates=candidate_five_cycles(G)
    candidates.sort(key=lambda seq:sum((m[u]*m[v] for u,v in seq),Q()),reverse=True)
    tries=0
    for edges in candidates[:max_candidates]:
        tries+=1
        try:
            c12=absorb(data,edges)
        except AssertionError:
            continue
        if c12["status"]=="PASS_C12":
            return {"status":"PASS","method":"C12_clique_absorption",
                    "cut_R":[list(e) for e in edges], "tested_cliques":tries,
                    "certificate":c12,"scope":"one finite physical graph"}
    return {"status":"OPEN","method":"global_palette_required",
            "peeling_nonroot":core["core_nonroot"],"tested_cliques":tries,
            "scope":"Inconclusive, not a counterexample"}

if __name__=="__main__":
    with open(sys.argv[1],encoding="utf8") as f:d=json.load(f)
    print(json.dumps(route(d),indent=2,ensure_ascii=False))
