"""Exact weighted strong-conflict peeling for the S597 root-reserve gate.

A nonroot edge e can be removed when the sum of currently present demands
in its closed conflict neighborhood is <= K=5/4. Reversing deletions
greedily restores every demand and preserves the root overlap J.

If the remaining edges are root edges only, a certified exact Hall flow
can pair the smaller root star entirely with the larger. PASS means
this instance's arc-3 gate closes; OPEN is not a counterexample.

All fractions exact. Physical conflict edges from the ORIGINAL graph
are retained even when their demand edge was peeled.
"""
from fractions import Fraction as Q
from collections import deque
import heapq, json, sys

K=Q(5,4)
def canon(u,v):
    u,v=str(u),str(v)
    assert u!=v
    return tuple(sorted((u,v)))

def prepare(data):
    m={str(k):Q(str(v)) for k,v in data["masses"].items()}
    s,t=data["s"],data["t"]
    E=sorted({canon(*e) for e in data["edges"]})
    A={v:set() for v in m};incident={v:[] for v in m}
    for i,(u,v) in enumerate(E):
        A[u].add(v);A[v].add(u)
        incident[u].append(i);incident[v].append(i)
    assert all(w>0 for w in m.values())
    assert canon(s,t) not in E and not A[s]&A[t]
    a,b=Q(str(data["a"])),Q(str(data["b"]))
    assert all(sum((m[z] for z in A[v]),Q())+(a if v==s else b if v==t else Q())<=1 for v in m)
    assert m[s]+b<=1 and m[t]+a<=1
    w=[m[u]*m[v] for u,v in E]
    conf=[{j for z in ({u,v}|A[u]|A[v]) for j in incident[z]} for u,v in E]
    R={i for i,e in enumerate(E) if s in e or t in e}
    rs=sum((w[i] for i in R if s in E[i]),Q())
    rt=sum((w[i] for i in R if t in E[i]),Q())
    return m,E,w,conf,R,s,t,rs,rt,a,b

def hall(m,E,w,conf,R,s,t,rs,rt):
    S=[i for i in sorted(R) if s in E[i]]
    T=[i for i in sorted(R) if t in E[i]]
    L,P=(S,T) if rs<=rt else (T,S)
    N=2+len(L)+len(P);src=0;sink=N-1
    G=[[] for _ in range(N)]
    def add(u,v,c):
        G[u].append([v,c,len(G[v])])
        G[v].append([u,Q(),len(G[u])-1])
    for i,k in enumerate(L):add(src,1+i,w[k])
    for j,k in enumerate(P):add(1+len(L)+j,sink,w[k])
    for i,u in enumerate(L):
        for j,v in enumerate(P):
            if v not in conf[u]:add(1+i,1+len(L)+j,max(rs,rt)+1)
    total=Q()
    while True:
        prev={src:None};todo=deque([src])
        while todo and sink not in prev:
            u=todo.popleft()
            for j,(v,c,_) in enumerate(G[u]):
                if c>0 and v not in prev:prev[v]=(u,j);todo.append(v)
        if sink not in prev:break
        path=[];cur=sink;f=None
        while prev[cur] is not None:
            u,j=prev[cur];f=G[u][j][1] if f is None else min(f,G[u][j][1])
            path.append((u,j));cur=u
        for u,j in path:
            v,_,rev=G[u][j];G[u][j][1]-=f;G[v][rev][1]+=f
        total+=f
    return total

def analyze(data):
    m,E,w,conf,R,s,t,rs,rt,a,b=prepare(data)
    loads=[sum((w[j] for j in C),Q()) for C in conf]
    heavy=sum(1 for i in range(len(E)) if i not in R and loads[i]>=K)
    alive=set(range(len(E)));removed=[]
    heap=[(loads[i],i) for i in alive-R if loads[i]<=K]
    heapq.heapify(heap)
    while heap:
        value,i=heapq.heappop(heap)
        if i not in alive or value!=loads[i] or value>K:continue
        removed.append((list(E[i]),str(value)))
        alive.remove(i)
        for j in conf[i]&alive:
            loads[j]-=w[i]
            if j not in R and loads[j]<=K:heapq.heappush(heap,(loads[j],j))
    assert all(loads[i]>K for i in alive-R)
    # Conflict components of the retained kernel. Components without
    # terminal root edges can be superposed at width K when Q_H<=K.
    components=[];unseen=set(alive)
    while unseen:
        seed=unseen.pop();group={seed};queue=[seed]
        for i in queue:
            for j in conf[i]&unseen:
                unseen.remove(j);group.add(j);queue.append(j)
        components.append(group)
    anchored=set()
    for group in components:
        if group&R:anchored|=group
    anchored_nonroot=len((alive-R)&anchored)
    root_free_nonroot=len((alive-R)-anchored)
    D=rs+rt+a*b-K
    flow=hall(m,E,w,conf,R,s,t,rs,rt)
    residual=D>0 and Q(1,2)<m[s]<Q(3,4) and Q(1,2)<m[t]<Q(3,4) and m[s]+m[t]>K
    status="PASS_ROOT_ONLY" if residual and alive==R and flow==min(rs,rt) else "OPEN_KERNEL"
    return {"status":status,"vertices":len(m),"edges":len(E),
            "initial_heavy":heavy,"removed":removed,"removed_count":len(removed),
            "core_nonroot":len(alive-R),"core_edges":[list(E[i]) for i in sorted(alive-R)],
            "anchored_nonroot":anchored_nonroot,"root_free_core":root_free_nonroot,
            "root_flow":str(flow),"r_s":str(rs),"r_t":str(rt),
            "D":str(D),"residual":residual}

def verify(data,result):
    m,E,w,conf,R,s,t,rs,rt,a,b=prepare(data)
    active=set(range(len(E)));index={e:i for i,e in enumerate(E)}
    for raw,claimed in result["removed"]:
        i=index[canon(*raw)]
        assert i in active and i not in R
        actual=sum((w[j] for j in conf[i]&active),Q())
        assert actual==Q(claimed) and actual<=K,(E[i],actual,claimed)
        active.remove(i)
    assert len(active-R)==result["core_nonroot"]
    assert all(sum((w[j] for j in conf[i]&active),Q())>K for i in active-R)
    if result["status"]=="PASS_ROOT_ONLY":
        assert active==R and max(rs,rt)<=K
        assert hall(m,E,w,conf,R,s,t,rs,rt)==min(rs,rt)
        assert rs+rt+a*b>K
    return True

if __name__=="__main__":
    for fn in sys.argv[1:]:
        with open(fn,encoding="utf8") as f: data=json.load(f)
        r=analyze(data);verify(data,r)
        print(json.dumps({"file":fn,**{k:v for k,v in r.items() if k not in ("removed","core_edges")}},ensure_ascii=False))
