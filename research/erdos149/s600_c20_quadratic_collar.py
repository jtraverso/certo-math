"""S600 C20: construct a rational full palette on ROOTS + near-tight C5 + its two-ring collar.

Original H physical conflicts are retained. Return PASS_C20_SUPPORT only if
all listed demands are covered; any other old edges remain OUT OF SCOPE.
Finite witness checker for the universal sufficient theorem in S600_C20.
"""
from fractions import Fraction as F
from collections import defaultdict
import json
from s599_paired_shadow import load_model,hall_colors,K
from s600_c5_collar import check as collar

def canon(e):return tuple(sorted(map(str,e)))

def build(data,cycle):
    m={str(v):F(str(w)) for v,w in data["masses"].items()}
    E,w,conf,S,T,ab=load_model(data)
    ix={e:i for i,e in enumerate(E)}
    C=[ix[canon((cycle[i],cycle[(i+1)%5]))] for i in range(5)]
    rootset=set(S+T);P0,rs,rt=hall_colors(w,conf,S,T)
    B=max(rs,rt); D=rs+rt+ab-K
    assert D>0 and B<F(3,4)
    stats=collar(data,cycle)
    W5=sum((w[i] for i in C),F())
    assert W5>=K-ab
    assert all(not(conf[i]&rootset) for i in C)
    adj={v:set() for v in m}
    for u,v in E:adj[u].add(v);adj[v].add(u)
    V=set(cycle);X={u for v in V for u in adj[v] if u not in V}
    first=[i for i,e in enumerate(E) if len(V&set(e))==1]
    second=[i for i,e in enumerate(E) if not(V&set(e)) and (X&set(e))]
    good=[i for i in second if any(j not in conf[i] for j in C)]
    bad=[i for i in second if i not in good]
    W1=sum((w[i] for i in first),F())
    Wgood=sum((w[i] for i in good),F())
    Wbad=sum((w[i] for i in bad),F())
    assert Wbad<F(144,35)*ab*ab
    free_min=min((w[j]*(W5-B)/W5 for j in C))
    assert Wgood<free_min
    if W5+W1+Wbad>K:
        return {"status":"INCONCLUSIVE","exceptional_mass":str(Wbad),
                "free_budget":str(K-W5-W1)}
    # Root Hall colors replicated proportionally over each C5 color slot,
    # leaving a guaranteed root-free subinterval in every slot.
    palette=[]
    for j in C:
        for mask,width in P0:
            if mask:  # do not scale the K-B empty tail; redistribute only root demand
                palette.append((frozenset(set(mask)|{j}),width*w[j]/W5))
        palette.append((frozenset((j,)),w[j]*(W5-B)/W5))
    for i in good:
        slot=next(j for j in C if j not in conf[i])
        need=w[i];other=[]
        for M,width in palette:
            if need and slot in M and not(M&rootset) and not(M&conf[i]):
                used=min(need,width)
                other.append((frozenset(set(M)|{i}),used))
                if width>used:other.append((M,width-used))
                need-=used
            else:other.append((M,width))
        assert need==0,(i,E[i])
        palette=other
    for i in first+bad:palette.append((frozenset((i,)),w[i]))
    remaining=K-sum((width for _,width in palette),F())
    assert remaining>=0
    if remaining:palette.append((frozenset(),remaining))
    demand=rootset|set(C)|set(first)|set(second)
    got=defaultdict(F);J=F()
    for M,width in palette:
        assert width>0
        for i in M:
            assert not((set(M)-{i})&conf[i]),(E[i],M)
            got[i]+=width
        if set(S)&M and set(T)&M:J+=width
    assert set(got)==demand and all(got[i]==w[i] for i in demand)
    assert sum((v for _,v in palette),F())==K
    assert J==min(rs,rt)>=D
    return {"status":"PASS_C20_SUPPORT","vertices":len(m),"edges":len(E),
        "covered":len(demand),"uncovered":len(E)-len(demand),
        "W5":str(W5),"W1":str(W1),"W2_good":str(Wgood),
        "W2_exceptional":str(Wbad),"spare":str(remaining),
        "J":str(J),"D":str(D),"palette_classes":len(palette),
        "universal_G1":"OPEN unless uncovered=0"}

def fixture():
    eps=F(1,1000);c=(1-eps)/2
    mass={"s":F(7,10),"t":F(7,10),"p":eps,"q":eps,"r":eps,"h":eps}
    for side in ("s","t"):
        for i in range(4):mass[f"{side}{i}"]=F(19,80)
    for i in range(5):mass[f"C{i}"]=c
    edges=[("s",f"s{i}") for i in range(4)]+[("t",f"t{i}") for i in range(4)]
    edges +=[(f"C{i}",f"C{(i+1)%5}") for i in range(5)]
    edges +=[("p","C0"),("p","C2"),("q","C3"),("q","C4"),
            ("r","C1"),("p","q"),("r","h")]
    return {"masses":{k:str(v) for k,v in mass.items()},"edges":[list(e) for e in edges],
            "s":"s","t":"t","a":"1/20","b":"1/20"}

if __name__=="__main__":
    result=build(fixture(),[f"C{i}" for i in range(5)])
    assert result["status"]=="PASS_C20_SUPPORT"
    assert result["W2_good"]==result["W2_exceptional"]=="1/1000000"
    assert result["spare"]=="1/4000000"
    assert result["covered"]==result["edges"]==20
    print(json.dumps(result,indent=2))
