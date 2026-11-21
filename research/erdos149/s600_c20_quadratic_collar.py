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

def build(data,cycle,balanced=False,signed=False,complete_far=False):
    if complete_far:assert signed
    if signed:balanced=True
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
    # C21 mode: masses <=1/2; C22 signed mode allows all C5 masses.
    # Classify exterior vertices
    # by their number of physical cycle neighbors; near-tightness
    # forbids three or more such neighbors.
    if balanced:
        if not signed:assert all(m[v]<=F(1,2) for v in cycle)
        near={u:set(adj[u]&V) for u in X}
        X1={u for u in X if len(near[u])==1}
        X2={u for u in X if len(near[u])==2}
        assert X==X1|X2
        first1=[i for i in first if any(u in X1 for u in E[i])]
        first2=[i for i in first if any(u in X2 for u in E[i])]
        assert set(first)==set(first1+first2)
        bad_ds=[i for i in bad if len(set(E[i])&X1)==1 and len(set(E[i])&X2)==1]
        bad_dd=[i for i in bad if set(E[i])<=X2]
        assert set(bad)==set(bad_ds+bad_dd)
    W1=sum((w[i] for i in first),F())
    Wgood=sum((w[i] for i in good),F())
    Wbad=sum((w[i] for i in bad),F())
    assert Wbad<F(144,35)*ab*ab
    if balanced:
        # Exact Horn dual decomposition. alpha_i>=0 is the
        # nonnegative price for a cycle row. Every X2-X2 edge
        # is paid by these prices, regardless of which C5 slots
        # it blocks; X1-X2 bad edges cost <= all X1 crossing demand.
        alpha={v:(1-2*m[v])/4 for v in cycle}
        if not signed:assert all(q>=0 for q in alpha.values())
        caps={v:1-sum((m[q] for q in (adj[v]&V)),F()) for v in cycle}
        assert all(q>=0 for q in caps.values())
        Horn=K-sum((m[v] for v in cycle),F())+W5
        assert Horn==sum((alpha[v]*caps[v] for v in cycle),F())
        charge=sum((m[u]*(1-sum((m[v] for v in near[u]),F()))/2 for u in X2),F())
        Wbad_dd=sum((w[i] for i in bad_dd),F())
        Wbad_ds=sum((w[i] for i in bad_ds),F())
        Wfirst1=sum((w[i] for i in first1),F())
        M1=sum((m[u] for u in X1),F())
        M2=sum((m[u] for u in X2),F())
        L=F(1,2)-2*ab
        assert 2*L*M2<=W1
        assert Wbad_ds<=M1*M2<=Wfirst1
        if signed:
            # Signed Horn charge. Every negative alpha contribution
            # is canceled by the row slack or by the one-contact
            # crossing-edge credit. No alpha_i>=0 hypothesis needed.
            Q1={v:sum((m[u] for u in X1 if v in near[u]),F()) for v in cycle}
            Q2={v:sum((m[u] for u in X2 if v in near[u]),F()) for v in cycle}
            slack={v:caps[v]-Q1[v]-Q2[v] for v in cycle}
            assert all(x>=0 for x in slack.values())
            gamma={v:m[v]+alpha[v] for v in cycle}
            assert all(x>0 for x in gamma.values())
            assert Horn==sum((alpha[v]*(Q1[v]+Q2[v]+slack[v]) for v in cycle),F())
            assert K-W5-W1==Horn+sum((m[v]*slack[v] for v in cycle),F())
            Wfirst2=sum((w[i] for i in first2),F())
            credit=sum((gamma[v]*(Q1[v]+slack[v]) for v in cycle),F())
            assert Wbad_dd<=charge
            assert K-W5-Wfirst2-Wbad_dd>=credit
            assert Wbad_ds<=M1*M2<=sum((gamma[v]*Q1[v] for v in cycle),F())
            assert K-W5-Wfirst2-Wbad_dd-Wbad_ds>=0
        else:
            assert Wbad_dd<=charge<=Horn<=K-W5-W1
        insert_free=good+first1
        insert_paid=first2+bad
    else:
        insert_free=good
        insert_paid=first+bad
    free_min=min((w[j]*(W5-B)/W5 for j in C))
    free_demand=sum((w[i] for i in insert_free),F())
    assert free_demand<free_min
    paid_demand=sum((w[i] for i in insert_paid),F())
    if balanced:assert W5+paid_demand<=K
    if W5+paid_demand>K:
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
    for i in insert_free:
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
    # C23: complete the original H when its ENTIRE remote demand
    # fits in the C5 color slots that carry no root edges. Remote
    # means outside C5, its crossing edges and its strong-conflict
    # second ring; every such physical edge is compatible with ALL
    # five C5 edges, but may conflict with nearby inserted edges.
    support=rootset|set(C)|set(first)|set(second)
    remote=[i for i in range(len(E)) if i not in support]
    remote_weight=sum((w[i] for i in remote),F())
    free_insert_weight=sum((w[i] for i in insert_free),F())
    if complete_far:
        assert all(not (conf[i]&set(C)) for i in remote)
        assert remote_weight+free_insert_weight<=W5-B
        for i in remote:
            need=w[i];nxt=[]
            for M,width in palette:
                if need and (M&set(C)) and not(M&rootset) and not(M&conf[i]):
                    take=min(need,width)
                    nxt.append((frozenset(set(M)|{i}),take))
                    need-=take
                    if width>take:nxt.append((M,width-take))
                else:nxt.append((M,width))
            assert need==0,(i,E[i],need)
            palette=nxt
    for i in insert_paid:palette.append((frozenset((i,)),w[i]))
    remaining=K-sum((width for _,width in palette),F())
    assert remaining>=0
    if remaining:palette.append((frozenset(),remaining))
    demand=rootset|set(C)|set(first)|set(second)|(set(remote) if complete_far else set())
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
    return {"status":"PASS_C23_FULL_G1" if complete_far else ("PASS_C22_SIGNED_SUPPORT" if signed else ("PASS_C21_BALANCED_SUPPORT" if balanced else "PASS_C20_SUPPORT")),
        "balanced_mode":balanced,"signed_mode":signed,
        "complete_far_mode":complete_far,"remote_weight":str(remote_weight),
        "root_free_cycle":str(W5-B),"free_insert_total":str(free_insert_weight),
        "vertices":len(m),"edges":len(E),
        "covered":len(demand),"uncovered":len(E)-len(demand),
        "W5":str(W5),"W1":str(W1),"W2_good":str(Wgood),
        "W2_exceptional":str(Wbad),"spare":str(remaining),
        "C21_Horn_slack":str(Horn) if balanced else None,
        "C21_bad_DD":str(Wbad_dd) if balanced else None,
        "C21_bad_DS":str(Wbad_ds) if balanced else None,
        "C22_signed_credit":str(credit) if signed else None,
        "J":str(J),"D":str(D),"palette_classes":len(palette),
        "universal_G1":"OPEN unless uncovered=0"}

def build_balanced(data,cycle):
    """Universal C21 support constructor when all 5 cycle masses <=1/2.

    It never needs the old C20 exceptional budget check; all physical
    annulus edges are paid by the Horn-Mantel row identity or by
    relocating one-contact crossing edges into C5 colors.
    """
    return build(data,cycle,balanced=True)

def build_general(data,cycle):
    """C22 universal TWO-RING support constructor for any near-tight C5.

    Uses signed alpha_i=(1-2m_i)/4 and its exact cancellation with
    one-contact crossing credit and row slacks. Original C20/C21
    implementations and their input contracts remain unchanged.
    """
    return build(data,cycle,signed=True)

def build_full_far(data,cycle):
    """C23 EXACT full-H G1 case: near-tight C5, signed Horn collar,
    and total demand of all remaining remote physical edges small
    enough for greedy insertion into root-free C5 color slots.
    """
    return build(data,cycle,signed=True,complete_far=True)

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
