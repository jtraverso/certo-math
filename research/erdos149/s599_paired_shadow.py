"""S599 exact paired-root shadow peeling for G1 (Erdos #149).

Theorem: Given a FULL Hall synchronization of the two root stars
and a peeling order of nonroot edges satisfying
  sigma_P(e) + sum_{f in remaining interior closed-conflict N[e]} w_f <= 5/4,
reverse insertion gives an exact K-palette with J=min(r_s,r_t).
Conflicts ALWAYS refer to the physical original graph.
PASS certifies only this fixed weighted graph; OPEN is inconclusive.
"""
from __future__ import annotations
from fractions import Fraction as F
from collections import deque
import json,sys
from pathlib import Path
K=F(5,4)

def canonical(u,v):return tuple(sorted((str(u),str(v))))

def load_model(data):
    m={str(v):F(str(q)) for v,q in data["masses"].items()}
    s,t=str(data["s"]),str(data["t"]);a,b=F(str(data["a"])),F(str(data["b"]))
    E=sorted({canonical(*e) for e in data["edges"]})
    adj={v:set() for v in m}; inc={v:set() for v in m}
    for i,(u,v) in enumerate(E):
        assert u in m and v in m and u!=v
        adj[u].add(v);adj[v].add(u);inc[u].add(i);inc[v].add(i)
    assert s!=t and canonical(s,t) not in E and not (adj[s]&adj[t])
    assert all(m[v]>0 for v in m)
    assert all(sum((m[z] for z in adj[v]),F())+(a if v==s else b if v==t else F())<=1 for v in m)
    assert m[s]+b<=1 and m[t]+a<=1
    w=[m[u]*m[v] for u,v in E]
    conflicts=[set().union(*(inc[z] for z in ({u,v}|adj[u]|adj[v]))) for u,v in E]
    S=[i for i,e in enumerate(E) if s in e]
    T=[i for i,e in enumerate(E) if t in e]
    return E,w,conflicts,S,T,a*b

def hall_colors(w,conf,S,T):
    rs=sum((w[i] for i in S),F());rt=sum((w[i] for i in T),F())
    small,large=(S,T) if rs<=rt else (T,S)
    n=len(small)+len(large)+2;src=0;sink=n-1
    g=[[] for _ in range(n)]
    def add(u,v,c):
        g[u].append([v,c,len(g[v]),c])
        g[v].append([u,F(),len(g[u])-1,F()])
    for i,r in enumerate(small):add(src,1+i,w[r])
    for j,r in enumerate(large):add(1+len(small)+j,sink,w[r])
    for i,r in enumerate(small):
        for j,q in enumerate(large):
            if q not in conf[r]:add(1+i,1+len(small)+j,max(rs,rt)+1)
    result=F()
    while True:
        prev={src:None};todo=deque([src])
        while todo and sink not in prev:
            u=todo.popleft()
            for j,(v,c,_,_) in enumerate(g[u]):
                if c>0 and v not in prev:prev[v]=(u,j);todo.append(v)
        if sink not in prev:break
        val=None;path=[];v=sink
        while prev[v] is not None:
            u,j=prev[v];val=g[u][j][1] if val is None else min(val,g[u][j][1])
            path.append((u,j));v=u
        for u,j in path:
            v,_,rev,_=g[u][j];g[u][j][1]-=val;g[v][rev][1]+=val
        result+=val
    assert result==min(rs,rt),("S597 Hall root hypothesis failed",result,rs,rt)
    colors=[];used={r:F() for r in large}
    for i,r in enumerate(small):
        for v,res,_,cap in g[1+i]:
            if 1+len(small)<=v<sink and cap>0 and cap>res:
                q=large[v-1-len(small)];amount=cap-res
                colors.append((frozenset((r,q)),amount));used[q]+=amount
    for r in large:
        if w[r]>used[r]:colors.append((frozenset((r,)),w[r]-used[r]))
    if K>max(rs,rt):colors.append((frozenset(),K-max(rs,rt)))
    assert sum((c for _,c in colors),F())==K
    return colors,rs,rt

def prove_instance(data,make_palette=True):
    E,w,conf,S,T,ab=load_model(data);R=set(S)|set(T);I=set(range(len(E)))-R
    P,rs,rt=hall_colors(w,conf,S,T)
    shadows=[sum((width for M,width in P if M&conf[i]),F()) for i in range(len(E))]
    # Initial load counts each interior edge's demand exactly once.
    loads={i:shadows[i]+sum((w[j] for j in I&conf[i]),F()) for i in I}
    trace=[]
    while True:
        eligible=[i for i in I if loads[i]<=K]
        if not eligible:break
        i=min(eligible,key=lambda x:(loads[x],E[x]))
        trace.append((i,loads[i]));I.remove(i)
        for j in I&conf[i]:loads[j]-=w[i]
    record={"status":"PASS" if not I else "OPEN_KERNEL",
            "vertices":len(data["masses"]),"edges":len(E),"roots":len(R),
            "initial_interior":len(E)-len(R),"removed":len(trace),"remaining":len(I),
            "D":str(rs+rt+ab-K),"root_width":str(max(rs,rt)),
            "root_J":str(min(rs,rt)),
            "certificate":[[list(E[i]),str(load)] for i,load in trace],
            "core_edges":[list(E[i]) for i in sorted(I)]}
    if I or not make_palette:return record
    for i,_ in reversed(trace):
        need=w[i];next_colors=[]
        for M,amount in P:
            if need and not (M&conf[i]):
                take=min(need,amount)
                next_colors.append((M|{i},take))
                if amount>take:next_colors.append((M,amount-take))
                need-=take
            else:next_colors.append((M,amount))
        assert need==0,(E[i],need)
        P=[(frozenset(M),amount) for M,amount in next_colors]
    assert sum((amount for _,amount in P),F())==K
    cover=[F() for _ in E];J=F()
    for M,amount in P:
        assert amount>0
        for i in M:
            assert not ((M-{i})&conf[i]),("physical conflict",E[i])
            cover[i]+=amount
        if (set(S)&M) and (set(T)&M):J+=amount
    assert cover==w
    assert J==min(rs,rt) and J>=rs+rt+ab-K
    record.update({"palette_classes":len(P),"J":str(J),
                   "palette":[{"edges":[list(E[i]) for i in sorted(M)],
                               "width":str(amount)} for M,amount in P]})
    return record

if __name__=="__main__":
    for path in sys.argv[1:]:
        d=json.loads(Path(path).read_text(encoding="utf8"))
        result=prove_instance(d)
        print(json.dumps({"file":path,**{k:v for k,v in result.items()
             if k not in ("palette","certificate","core_edges")}},ensure_ascii=False))
