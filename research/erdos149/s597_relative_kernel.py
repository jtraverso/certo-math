"""S597 exact relative anchored-conflict kernel extractor.

Does NOT delete physical edges: they remain in 'physical_edges' so all
compatibility queries refer to the same original graph H.
Under Q_H<=K, the optimal two-root overlap Jmax is EXACTLY preserved.
See S597_WEIGHTED_CORE_AND_SPLIT.md, Theorem 5.

Usage: python research/erdos149/s597_relative_kernel.py input.json
"""
import hashlib,json,sys
from fractions import Fraction as Q
from s597_weighted_core import analyze,prepare

def extract(d):
    m,E,w,conf,R,s,t,rs,rt,a,b=prepare(d)
    r=analyze(d)
    idx={e:i for i,e in enumerate(E)}
    alive=set(range(len(E)))
    for e,_ in r["removed"]:
        alive.remove(idx[tuple(sorted(e))])
    components=[];unseen=set(alive)
    while unseen:
        seed=unseen.pop();cc={seed};q=[seed]
        for i in q:
            for j in conf[i]&unseen:
                unseen.remove(j);cc.add(j);q.append(j)
        components.append(cc)
    anchor=set().union(*(cc for cc in components if cc&R))
    rootfree=alive-anchor
    assert R<=anchor and not (rootfree&anchor)
    assert all(not(conf[i]&rootfree) for i in anchor)
    out={
        "title":"S597 exact anchored relative conflict kernel",
        "status":r["status"],
        "hypotheses":{"Q_H_le_5_4_required":True,"S591_heavy_residual":r["residual"]},
        "physical_masses":{k:str(v) for k,v in m.items()},
        "physical_edges":[list(e) for e in E],
        "root_edges":[list(E[i]) for i in sorted(R)],
        "anchored_demand_edges":[list(E[i]) for i in sorted(anchor)],
        "rootfree_demand_edges":[list(E[i]) for i in sorted(rootfree)],
        "peeled_demand_edges":[e for e,_ in r["removed"]],
        "witness":{"root_flow":r["root_flow"],"peeling":r["removed"],
                   "anchored_weight":r["anchored_weight"],"root_band":r["root_band"],
                   "core_anchored_nonroot":r["anchored_nonroot"],"rootfree_nonroot":r["root_free_core"]},
        "conclusion":"Jmax(full physical H at K) == Jmax(anchored demand on same physical H at K), assuming Q_H<=K",
        "universal_arc3":"OPEN"
    }
    z=json.dumps(out,sort_keys=True,separators=(",",":")).encode("utf8")
    out["sha256_of_payload"]=hashlib.sha256(z).hexdigest()
    return out

if __name__=="__main__":
    with open(sys.argv[1],encoding="utf8") as f:d=json.load(f)
    out=extract(d)
    print(json.dumps({"status":out["status"],"physical_edges":len(out["physical_edges"]),
        "anchor_demand":len(out["anchored_demand_edges"]),
        "rootfree_demand":len(out["rootfree_demand_edges"]),
        "peeled_demand":len(out["peeled_demand_edges"]),
        "anchor_weight":out["witness"]["anchored_weight"],
        "sha256_of_payload":out["sha256_of_payload"]},ensure_ascii=False))
