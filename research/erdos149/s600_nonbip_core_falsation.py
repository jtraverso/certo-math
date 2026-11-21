"""S600: exact 18-vertex counterexample to 'every anchored core is bipartite'.
The exact old H-palette is stored as a short zlib+base85 rational JSON.
Independently rechecks hash, every physical conflict, every edge demand,
the full 5/4 palette, the weighted peeling and an odd rooted-core cycle.
This is NOT an Erdős #149 counterexample: Q_H<=23541/32000<1.
"""
from __future__ import annotations
import base64,hashlib,zlib,json
from fractions import Fraction as F
from collections import defaultdict
import networkx as nx
from s597_weighted_core import analyze
PAYLOAD="c-oy++iJrw4E+~B2Vz;i_E$z9IvTdY27?CnQ2Otab8+M(ZoIu6M?Q*tbi0d-I0<N#6peUYV0V4%ZsPRvBH~Gjb2B1LNGD_l1cYotE+L;#7}4Se7+WrMx$q+mkYU5HWq7);*nP$BD|TO{2hmOXtQocoo}gx4G`nJ!zhZi&PLZ4Oz2`=JU2eB1<(;%T3F}&r@qv&XqAARWXmYI?u!<>37K|sDOnSJc%ordUW{#x;P6kI<k9czBNBtM988!@Ch8@G6;gIm75#N{3uJ1dln)`13z*be#=jY?vzsIKpXoHn9x+?Qmb;0>ji#qn4N5)prT2iTkJSU!!HK{F+BKLX8F*<}`q1FDm3)Ud8RSz7r{*dqf!^d^<U`GLpUmnq2-iwTGin-gccl4vGab@|C&mYD@Z6#FF_{hnN1}N?tHg4I7CAQ{@XCWIO$|37@qSQ9esF0?_0X^iyl$VKg9?KD!-BQUT2(H*HreaKht>Le#)6sA!%@(un(4A*%1=QkNR(jY88=b>~aE!>jt+$%0Y1jQNTTf@}^Z8O^jf<+_Nd3XjutT<P*dDIlx2ZX07-mxDGb<!*!W=z)C-acaKH9|N7qV{`@&"
SHA256="4f6e6149e26ecb9dec602a493718ab2656cf82a55bd1003834645bf08f8d058f"
def key(e):
    u,v=map(str,e);assert u!=v;return tuple(sorted((u,v)))
def run():
    raw=zlib.decompress(base64.b85decode(PAYLOAD))
    assert hashlib.sha256(raw).hexdigest()==SHA256
    d=json.loads(raw.decode())
    mass={str(k):F(str(v)) for k,v in d["masses"].items()}
    E={key(e) for e in d["edges"]}
    N={v:set() for v in mass}
    for u,v in E:N[u].add(v);N[v].add(u)
    assert len(mass)==18 and len(E)==29
    for v in mass:
        load=sum((mass[u] for u in N[v]),F())
        if v in (d["s"],d["t"]):load+=F(1,20)
        assert load<=1,(v,load)
    weights={e:mass[e[0]]*mass[e[1]] for e in E}
    cover=defaultdict(F);total=F();joint=F()
    for color in d["palette"]:
        M={key(e) for e in color["edges"]}
        assert len(M)==len(color["edges"]) and M<=E
        for e in M:
            for f in M-{e}:
                assert not (set(e)&set(f)) and all(u not in N[v] for u in e for v in f)
        w=F(color["width"]);assert w>0
        for e in M:cover[e]+=w
        if any(d["s"] in e for e in M) and any(d["t"] in e for e in M):
            joint+=w
        total+=w
    assert cover==weights and total==F(5,4)
    old_cost=sum((F(c["width"]) for c in d["palette"] if c["edges"]),F())
    assert old_cost==F(23541,32000)<1
    core=analyze(d)
    assert core["core_nonroot"]>0 and core["anchored_nonroot"]>0
    support={key(e) for e in core["core_nonroot_edges"]}
    support|={e for e in E if d["s"] in e or d["t"] in e}
    V={v for e in support for v in e}
    physical=nx.Graph();physical.add_nodes_from(V)
    physical.add_edges_from(e for e in E if set(e)<=V)
    assert not nx.is_bipartite(physical)
    odd=next((c for c in nx.cycle_basis(physical) if len(c)%2),None)
    assert odd is not None
    return {"status":"PASS_FALSATION","vertices":18,"physical_edges":29,
            "surviving_anchored_nonroot":core["anchored_nonroot"],
            "induced_odd_cycle_length":len(odd),
            "Q_H_upper":str(old_cost),"palette_width":str(total),
            "sha256":SHA256,"G1_universal":"OPEN"}
if __name__=="__main__":
    print(json.dumps(run(),indent=2))
