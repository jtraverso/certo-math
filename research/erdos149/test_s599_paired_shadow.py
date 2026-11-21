"""S599 exact rational regression for G1 paired-shadow peeling.

Exercises sixteen feasible cross-edge configurations and one
connected nonbipartite graph with two internally vertex-disjoint
old s-t paths. The full physical fractional palette is constructed
and verified at every PASS. S597 loads are checked independently.
"""
from fractions import Fraction as F
from itertools import combinations
import json
from s599_paired_shadow import prove_instance,load_model,K
from s597_weighted_core import analyze as old_analyze

def fixture(extra):
    m={"s":"7/10","t":"7/10"}
    m.update({f"s{i}":"19/80" for i in range(4)})
    m.update({f"t{i}":"19/80" for i in range(4)})
    E=[["s",f"s{i}"] for i in range(4)]
    E +=[["t",f"t{i}"] for i in range(4)]
    E += [list(e) for e in extra]
    return {"masses":m,"edges":E,"s":"s","t":"t",
            "a":"1/20","b":"1/20"}

def legacy_core(data):
    E,w,conf,S,T,ab=load_model(data)
    alive=set(range(len(E)));R=set(S)|set(T)
    while True:
        removable=[i for i in alive-R
                   if sum((w[j] for j in conf[i]&alive),F())<=K]
        if not removable:break
        alive.remove(removable[0])
    return len(alive-R)

n=improved=0
for size in range(5):
    for indices in combinations(range(4),size):
        d=fixture([(f"s{i}",f"t{i}") for i in indices])
        r=prove_instance(d)
        assert r["status"]=="PASS" and r["remaining"]==0
        assert F(r["J"])==F(133,200)
        assert legacy_core(d)==size,(size,legacy_core(d))
        n+=1
        if size: improved+=1

nonbip=fixture([("s0","s1"),("t0","t1"),("s2","t2"),("s3","t3")])
r=prove_instance(nonbip)
assert r["status"]=="PASS" and r["remaining"]==0
assert legacy_core(nonbip)==2
assert F(r["J"])==F(133,200) and F(r["D"])==F(33,400)
print(json.dumps({"test":"cross_root_family","status":"PASS",
    "instances":n,"strict_improvements_over_S597":improved,
    "nonbipartite_connected_case":{"edges":len(nonbip["edges"]),
       "S597_remaining":2,"S599_remaining":0,"J":r["J"],
       "D":r["D"],"palette_colors":r["palette_classes"]}}))
