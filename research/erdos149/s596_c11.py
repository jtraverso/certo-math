"""C11 exact simultaneous heavy blocker test for a physical graph H.

For any fixed root edge r=sw in an s-exclusive palette class, *one single*
induced matching containing r must carry heavy edges blocking every
compatible t-root type that appears t-exclusive. This is stronger than
the pairwise capacities underlying C10.

The test is exact rational, searches 2**k opposite-root target masks, and returns
UNKNOWN (never PASS) if the state budget is hit. A PASS additionally
requires Q_H <= 5/4, which must be certified separately.
"""
from __future__ import annotations
from fractions import Fraction as F
import sys, json
K=F(5,4)

def key(u,v):
    return tuple(sorted((str(u),str(v))))

def evaluate(data,max_states=500000):
    mass={str(k):F(str(v)) for k,v in data["masses"].items()}
    s,t=str(data["s"]),str(data["t"])
    a,b=F(str(data["a"])),F(str(data["b"]))
    edges=sorted({key(u,v) for u,v in data["edges"]})
    es=set(edges);nbr={v:set() for v in mass}
    for u,v in edges:
        assert u!=v and u in nbr and v in nbr
        nbr[u].add(v);nbr[v].add(u)
    assert all(w>0 for w in mass.values())
    row={v:sum((mass[z] for z in nbr[v]),F()) for v in mass}
    assert all(d<=1 for d in row.values())
    assert row[s]+a<=1 and row[t]+b<=1
    assert mass[s]+b<=1 and mass[t]+a<=1
    assert key(s,t) not in es and not(nbr[s]&nbr[t])
    def compatible(e,f):
        return not(set(e)&set(f)) and all(key(u,v) not in es for u in e for v in f)
    w={e:mass[e[0]]*mass[e[1]] for e in edges}
    r_s=[e for e in edges if s in e]
    r_t=[e for e in edges if t in e]
    ell={e:sum((w[f] for f in edges if not compatible(e,f)),F()) for e in edges}
    heavy=[e for e in edges if s not in e and t not in e and ell[e]>=K]
    rs=mass[s]*row[s];rt=mass[t]*row[t]
    D=rs+rt+a*b-K
    residual=(D>0 and F(1,2)<mass[s]<F(3,4)
             and F(1,2)<mass[t]<F(3,4) and mass[s]+mass[t]>K)
    if not residual:
        return {"status":"NOT_RESIDUAL","D":str(D)}
    out={"status":"INCONCLUSIVE","D":str(D),"heavy":len(heavy),
         "hypothesis":"Q_H<=5/4 independently, plus S595 recoloring lemma",
         "by_side":{}}
    for side,roots,opposite,x,y in [
        ("s",r_s,r_t,mass[s],mass[t]),
        ("t",r_t,r_s,mass[t],mass[s])]:
        hard_total=F();results=[]
        for root in roots:
            bad=[q for q in opposite if not compatible(root,q)]
            direct=sum((w[q] for q in bad),F())
            good=[q for q in opposite if compatible(root,q)]
            cand=[]
            for e in heavy:
                if compatible(e,root):
                    qidx=frozenset(i for i,q in enumerate(good) if not compatible(e,q))
                    if qidx:cand.append((e,qidx))
            # Exact type-cover branch-and-bound: at most k selected heavy
            # edges are needed to cover k opposite-root types. Enumerate
            # 2**k target masks, NOT all matchings of heavy edges.
            best=F();witness=();states=[0]
            k=len(good)
            n=len(cand)
            if n and k:
                masks=[sum(1<<j for j in cover) for _,cover in cand]
                cmasks=[sum((1<<j for j,(f,_) in enumerate(cand)
                             if i!=j and compatible(e,f)),0)
                        for i,(e,_) in enumerate(cand)]
                hitters=[sum((1<<i for i,mask in enumerate(masks)
                              if mask & (1<<j)),0) for j in range(k)]
                def weight(mask):
                    return sum((w[good[j]] for j in range(k)
                                if mask & (1<<j)),F())
                def exists(needed,available):
                    states[0]+=1
                    if states[0]>max_states:raise OverflowError()
                    if needed==0:return ()
                    targets=[j for j in range(k) if needed & (1<<j)]
                    target=min(targets,
                               key=lambda j:(hitters[j]&available).bit_count())
                    bits=hitters[target]&available
                    while bits:
                        bit=bits&-bits
                        i=bit.bit_length()-1
                        bits-=bit
                        rest=exists(needed & ~masks[i],available & cmasks[i])
                        if rest is not None:return (i,)+rest
                    return None
                try:
                    for target in sorted(range(1<<k),key=weight,reverse=True):
                        seq=exists(target,(1<<n)-1)
                        if seq is not None:
                            best=weight(target)
                            witness=tuple(cand[i][0] for i in seq)
                            break
                except OverflowError:
                    return {"status":"UNKNOWN","side":side,"root":list(root),
                            "reason":"matching_enumeration_budget_exhausted",
                            "visited":states[0],"limit":max_states}
            else:
                states[0]=1
                if states[0]>max_states:
                    return {"status":"UNKNOWN","side":side,"root":list(root),
                            "reason":"matching_enumeration_budget_exhausted",
                            "visited":states[0],"limit":max_states}
            critical=direct+best>K-x
            if critical:hard_total+=w[root]
            results.append({"root":list(root),"weight":str(w[root]),"I":str(direct),
                "B":str(best),"threshold":str(K-x),"hard":critical,
                "best_matching":[list(e) for e in witness],"states":states[0]})
        out["by_side"][side]={"hard_total":str(hard_total),
              "exclusive_lower_bound":str(K-y),"roots":results}
        if hard_total<=K-y:out["status"]="PASS_C11_"+side
    return out

if __name__=="__main__":
    with open(sys.argv[1],encoding="utf8") as f: inp=json.load(f)
    limit=int(sys.argv[2]) if len(sys.argv)>2 else 500000
    print(json.dumps(evaluate(inp,limit),ensure_ascii=False,indent=2))
