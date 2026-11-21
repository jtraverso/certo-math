"""Erdos #149 S595 exact cross-heavy-flow sufficient test (not universal).

Usage: python research/erdos149_s595_cross_flow.py input.json

For each root-edge r, allow a heavy interior edge e (ell(e)>=5/4)
as a witness ONLY if r,e are compatible and e conflicts with some
OLD root edge on the OPPOSITE side. A max-flow gives nu_cross.
Under the S591 arc-3 heavy residual and Q_H<=5/4:
 nu_cross <= 5/2 - r_s - r_t - 2ab  => J>=D.
Uses fractions only and independently checks the min cut. Does NOT
assert Q_H<=5/4 on arbitrary input; that is a separate hypothesis.
"""
from fractions import Fraction as F
from collections import deque
import json
import sys

K=F(5,4)

def ed(u,v):return tuple(sorted((u,v)))

def maxflow(n,links,source,sink):
    g=[[] for _ in range(n)]
    def add(u,v,c):
        g[u].append([v,c,len(g[v])])
        g[v].append([u,F(0),len(g[u])-1])
    for u,v,c in links:add(u,v,c)
    total=F(0)
    while True:
        prev={source:None};q=deque([source])
        while q and sink not in prev:
            u=q.popleft()
            for i,(v,c,_) in enumerate(g[u]):
                if c>0 and v not in prev:prev[v]=(u,i);q.append(v)
        if sink not in prev:break
        path=[];v=sink;f=None
        while prev[v] is not None:
            u,i=prev[v];f=g[u][i][1] if f is None else min(f,g[u][i][1]);path.append((u,i));v=u
        for u,i in path:
            v,_,rev=g[u][i];g[u][i][1]-=f;g[v][rev][1]+=f
        total+=f
    reachable={source};q=deque([source])
    while q:
        u=q.popleft()
        for v,c,_ in g[u]:
            if c>0 and v not in reachable:reachable.add(v);q.append(v)
    return total,reachable

def evaluate(data):
    m={str(k):F(str(v)) for k,v in data["masses"].items()}
    s,t=str(data["s"]),str(data["t"])
    a,b=F(str(data["a"])),F(str(data["b"]))
    edges=sorted({ed(str(u),str(v)) for u,v in data["edges"]})
    assert s!=t and all(u!=v and u in m and v in m for u,v in edges)
    assert all(z>0 for z in m.values()) and a>0 and b>0
    es=set(edges)
    neigh={v:set() for v in m}
    for u,v in edges:neigh[u].add(v);neigh[v].add(u)
    row={v:sum((m[w] for w in neigh[v]),F(0)) for v in m}
    assert all(z<=1 for z in row.values())
    assert row[s]+a<=1 and row[t]+b<=1 and m[s]+b<=1 and m[t]+a<=1
    assert ed(s,t) not in es and not (neigh[s]&neigh[t])
    def comp(e,f):
        return not(set(e)&set(f)) and all(ed(u,v) not in es for u in e for v in f)
    weights={e:m[e[0]]*m[e[1]] for e in edges}
    ell={e:sum((weights[f] for f in edges if not comp(e,f)),F(0)) for e in edges}
    roots_s=[e for e in edges if s in e]
    roots_t=[e for e in edges if t in e]
    roots=roots_s+roots_t
    Z=[e for e in edges if s not in e and t not in e and ell[e]>=K]
    pairs=[]
    for i,r in enumerate(roots):
        opp=roots_t if i<len(roots_s) else roots_s
        for j,e in enumerate(Z):
            if comp(r,e) and any(not comp(e,o) for o in opp):
                pairs.append((i,j))
    big=sum((weights[e] for e in roots),F(0))+1
    src=0;sink=len(roots)+len(Z)+1
    links=[(src,1+i,weights[r]) for i,r in enumerate(roots)]
    links += [(1+len(roots)+j,sink,weights[e]) for j,e in enumerate(Z)]
    links += [(1+i,1+len(roots)+j,big) for i,j in pairs]
    nu,reach=maxflow(sink+1,links,src,sink)
    U={i for i in range(len(roots)) if 1+i in reach}
    V={j for i,j in pairs if i in U}
    cut=sum((weights[r] for i,r in enumerate(roots) if i not in U),F(0))
    cut+=sum((weights[e] for j,e in enumerate(Z) if j in V),F(0))
    assert cut==nu
    rs=m[s]*row[s];rt=m[t]*row[t];D=rs+rt+a*b-K
    heavy_residual=(D>0 and F(1,2)<m[s]<F(3,4)
                    and F(1,2)<m[t]<F(3,4) and m[s]+m[t]>K)
    threshold=2*K-rs-rt-2*a*b
    coarse=2*K-m[s]-m[t]
    return {"status":"PASS" if D<=0 or (heavy_residual and nu<=threshold) else "INCONCLUSIVE",
            "requires":"Q_H<=5/4 separately; a PASS proves only arc-3 reinsertion for this input",
            "residual":heavy_residual,"D":str(D),"r_s":str(rs),"r_t":str(rt),
            "heavy_edges":len(Z),"cross_pairs":len(pairs),"nu_cross":str(nu),
            "threshold_exact":str(threshold),"threshold_uniform":str(coarse),
            "cut_capacity":str(cut),"cut_U":[list(roots[i]) for i in sorted(U)],
            "cut_Z":[list(Z[j]) for j in sorted(V)]}
if __name__=="__main__":
    with open(sys.argv[1],encoding="utf8") as f:data=json.load(f)
    print(json.dumps(evaluate(data),indent=2,ensure_ascii=False))
