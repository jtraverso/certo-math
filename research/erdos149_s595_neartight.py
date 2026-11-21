"""S595 617-vertex two-connected near-extremal adversary to C10.

Produces a GRAPH with x=y=13/20, a=b=1/200 and Q_H in
(K-ab,K), with no articulation, but nu_cross=2587/2000.
It does NOT contradict Erdos #149: a separate explicit palette bound
proves Q_F<=K. See docs/ERDOS149_S595_HEAVY_SATURATION.md.

Use: python research/erdos149_s595_neartight.py
No floating point and no external dependencies.
"""
from fractions import Fraction as F
import json

K=F(5,4)

def build(eps=F(1,1000000)):
    assert 0<eps<F(1,10000)
    m={"s":F(13,20),"t":F(13,20)}
    edges=[];leaves=[];parent={}
    for r in ("s","t"):
        for i in range(4):
            A=f"{r}a{i}";m[A]=F(199,800);edges.append((r,A))
            for k in range(3):
                Z=f"{r}z{i}_{k}";m[Z]=F(7,60);edges.append((A,Z))
                for j in range(3):
                    V=f"{r}v{i}_{k}_{j}";D=f"{r}d{i}_{k}_{j}"
                    m[V]=F(1,4);m[D]=F(3,4)
                    edges.extend(((Z,V),(V,D)))
                    for h in range(6):
                        W=f"{r}e{i}_{k}_{j}_{h}"
                        m[W]=F(1,8);edges.append((D,W))
                        leaves.append(W);parent[W]=D
    for i in range(len(leaves)):
        edges.append((leaves[i],leaves[(i+1)%len(leaves)]))
    c=(1-eps)/2
    for k,i in enumerate((0,len(leaves)//2)):
        W=leaves[i];m[parent[W]]-=eps
        h=f"omega{k}";m[h]=eps
        cidx=(0,2)[k]
        edges.extend(((W,h),(h,f"c{cidx}")))
    for i in range(5):
        m[f"c{i}"]=c
        edges.append((f"c{i}",f"c{(i+1)%5}"))
    assert len(m)==617 and len(edges)==1049
    return {"masses":{v:str(w) for v,w in m.items()},
            "edges":[list(e) for e in edges],"s":"s","t":"t",
            "a":"1/200","b":"1/200"}

def bound(eps=F(1,1000000)):
    c=(1-eps)/2
    # Remove the last leaf-edge from each 6-leaf block, and give all
    # 72 removed tree edges one separate matching color of width 3/32.
    # The remaining forest has a physical bipartite palette of width 1.
    # The leaf-ring edges (length 432) have 3 matching colors of width 1/64.
    core=F(1)+F(3,32)+F(3,64)  # 73/64
    cyc=5*c*c
    connectors=2*eps*(c+F(1,8))
    upper=max(core,cyc)+connectors
    new_arc_budget=2*F(13,20)*F(1,200)+F(1,40000)
    return {"core":core,"C5_lower":cyc,"connectors":connectors,
            "QH_upper":upper,
            "QF_upper":max(core+new_arc_budget,cyc)+connectors,
            "K_minus_ab":K-F(1,40000),
            "ab":F(1,40000)}

if __name__=="__main__":
    import sys
    import erdos149_s595_cross_flow as C
    e=F(sys.argv[1]) if len(sys.argv)>1 else F(1,1000000)
    data=build(e);r=C.evaluate(data);z=bound(e)
    assert z["C5_lower"]>z["K_minus_ab"] and z["QH_upper"]<K and z["QF_upper"]<K
    assert r["nu_cross"]=="2587/2000" and r["status"]=="INCONCLUSIVE"
    print(json.dumps({"n":len(data["masses"]),"edges":len(data["edges"]),
        "QH_lower":str(z["C5_lower"]),"QH_upper":str(z["QH_upper"]),
        "QF_upper":str(z["QF_upper"]),"nu_cross":r["nu_cross"],
        "threshold":r["threshold_exact"],"D":r["D"],
        "note":"Not a counterexample; demonstrates C10 incompleteness on a 2-connected, near-tight graph"},
        indent=2))
