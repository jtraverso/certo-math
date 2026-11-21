"""Erdos #149 S597: independently replay two STATIC exact rational palettes.

The embedded data are zlib+base85 representations of complete JSON
certificates. No solver is used for verification. The decoder checks
SHA-256, exact physical induced matchings, every edge demand and
the complete palette budget, and the 3-connectivity of the 18-vertex
instance. Both achieve J=min(r_s,r_t), hence this is optimal.

These are FINITE instance certificates, NOT the universal arc-3 lemma.
"""
from __future__ import annotations

import base64
import hashlib
import json
import zlib
from collections import deque
from fractions import Fraction as Q

DATA = {
    "tree23": """c-q~W+m4$s5Qgvb6cN`^!x#v-*S%^Vp{gQxv65|@gJ43dM0xjeNXT$7!d_t0-s}eRJ7&H)Fm^7p`P|w>;<&Xw&Mg^*hZtPGjy>+L<8Ac1|H+&WKjOpQT4c(dh+`S2(o1@kUS}UIe+hPeI~~CKz+ophA{zuU7z;Ze;!F22cFxBfDogSq22>W>^(A82@@)cIR)FRT(6RzFS7?44w%CA88?eO&Y}$Y=Heibl*t7v#Y`~@sNNq@muDL^HxXJzbH5V0sbH6Uik0O`P=ie4Jjj)O8tWuq+Dp9EtstQ%AkgB9gMV}p1&kpq2RjM;pB`Q@yRiR21Qk7Jw@S#B!cck1=#T_YkRB=bj9aY?saz_>S%CoENquf!&9VvHIaYxD>RoszsM-}%hm`YVqvRZY;trixuo3^NkMF<wfu)t#7Y9K4tvA$O?zhsx*(k-q&<tgr@iF&*JIajA6>^>454!AxYk1}f9I*MNsQI<)4xj*gi*ATa54Il<rivTsa#pr7C5lD@Bac#~$C_3j5cU9A_a~28XYB}nfh1EG_!gbCGYb%whbq|Bb|La1*-{HQqbb^)rHYZ>&Cx|-G^LRi-9Zs)V3DjqSHc}sgw87xcBuMKq5GVFnk&U7gjuL67Bl;l)9(bS|rj498;wg=IN-)TIFv)q@t5VcGm*|Hz1I~-Ep4bB;MzoO!>MW%ROV8D=5fjo(ObWHxJ8S@&j?JH!<uEapOjc=a*Y>BOIY`FZPhB&?^#+JdnC`tbnh%C(tQ_X}|2<52bK^hmiz{`38!+z~J@9@nAU0K&oAj9j?MPvw9VswB?e+P}drFx9TGQ?`TYuvuOajJmcW;*I@7Ex$xPEk+@tkriYIa&;7S}_x0^B63r;ATRFANc%E(`RVq=C@%YD3IUkp?;I^a8G(x=(*(DF#R<#+;R}olpav)W`{2UXwi>q|KdX%RA|*><Fd1CmG)d?H>=!a>MXM%COdSZVARL-acOi+Igr|8_ORD<^Hsjkw6))cLHCwulr55Mp`0Q#r;3xCHv73qm!In{{jI-oF@""",
    "core18": """c-q}rS#RPn5Ps)Zpgf}`;}h?5pSnL`RiP|cv{gBj1Z^e6f8Qh=buh+P$)<gQ`13dR%y^C*yTNdnEb?sgoctUnGM}#tAYxij!KZk(Uah9`JzH+x<d4^4y-G$keVG-7EGqu48dc-87Ug3|o9POGO90gXi1Fl%U=1M}LN$bG2-lE_h6oLTMrBY{1`R<Pf;EI_2-Og#A^eO~z`pURoG%)e{%$CT-^R70(<MrptEZ8XfvpT;Wzg#k_+T(AgIgIBD??mopbrKhJH=oPRw%?yF|0xqN@}MVHlp@bREoj-%#UI?A+AusPBE-9v9F?13{flWCoSx&Kx$v6#UTzHQwD&8K46cl7RQuJ$YC#sOlWbK1IMI~LrMX0(8nRxTO5-<*P?xJ<Rx{XJr=#BY-;i0Iy=;5be#Ir9{#F_bbPQPd8kJik4bu*er(tkf=)=jUYFDDW+QWLYLmUmvXtk7zdI@W_hnu-tr(A$Bsq77rv}-N3_<|B>T>B7!6PtKu3Cj(Z83^NH3?`-a7ALE{+m^-+FpkW3I~acO-}K9Q|4kD_!f>}|JNw&Z4?VQDcpCXctFUaz8f`hkU$qkF@K{{h^c=#Dyw?w_mKL>x;2X2CG9VRiTWEA*Gx%Nj`Y&+{?RUQj0<U0WOU#{+DXTv-@zz+<0k9N8b!X^N%4TniTiF;$h}3tt*!7XWe`wpdAAQ&5a4-gehzW%s!?tX&=H3mH839~1G0?xhX*seqCa-A=!P7rWI#0#y;SluJn5BcC_1-&y@LE7R&M0YU1}uuKR6oSYdni&ypsNhjXlpA`=2%K_`&oObnKwn;OG~7^zNmE_`kQ{(dEuJBHhF5{N+Hdwo933rJPTfSvh-tSuN@vDA2?7dp4^-D3tkD4)*^52EyQY""",
}
DIGEST = {
    "tree23": "e5fe80368fa07e6d45ec289bdb283c923bf2f7a960a85c013fba22b508f6342e",
    "core18": "f162313cc2b72cab19ad58d6134c5007b7f0978571353c4c2673ba6dd1bd8504",
}

def canon(u,v):
    assert u != v
    return tuple(sorted((u,v)))

def decode(name):
    data=zlib.decompress(base64.b85decode(DATA[name]))
    assert hashlib.sha256(data).hexdigest()==DIGEST[name],name
    return json.loads(data.decode("utf8"))

def connected_after_deleting(vertices,adj,deleted):
    remaining=[v for v in vertices if v not in deleted]
    if not remaining:return True
    found={remaining[0]};queue=deque([remaining[0]])
    while queue:
        v=queue.popleft()
        for w in adj[v]:
            if w not in deleted and w not in found:
                found.add(w);queue.append(w)
    return len(found)==len(remaining)

def check(name):
    cert=decode(name)
    m={str(v):Q(str(q)) for v,q in cert["masses"].items()}
    edges={canon(*e) for e in cert["edges"]}
    assert all(q>0 and q<Q(3,4) for q in m.values()),name
    adj={v:set() for v in m}
    for u,v in edges:
        assert u in m and v in m,(name,u,v)
        adj[u].add(v);adj[v].add(u)
    s,t=cert["s"],cert["t"]
    a,b=Q(cert["a"]),Q(cert["b"])
    assert s!=t and s in m and t in m
    assert canon(s,t) not in edges and not(adj[s]&adj[t])
    for v in m:
        d=sum((m[u] for u in adj[v]),Q())
        if v==s:d+=a
        if v==t:d+=b
        assert d<=1,(name,"degree row",v,d)
    assert m[s]+b<=1 and m[t]+a<=1
    if name=="tree23":
        assert len(m)==23 and len(edges)==22
        assert connected_after_deleting(m,adj,set())
    if name=="core18":
        assert len(m)==18 and len(edges)==39
        assert connected_after_deleting(m,adj,set())
        # Exactly 3-vertex-connected or higher: delete every pair.
        for v in m:
            assert connected_after_deleting(m,adj,{v}),("cut vertex",v)
            for u in m:
                if u!=v:
                    assert connected_after_deleting(m,adj,{u,v}),("cut pair",u,v)
        assert all(len(adj[v])>=3 for v in m)
    total=Q()
    covered={e:Q() for e in edges}
    joint=Q()
    for color in cert["palette"]:
        width=Q(color["width"])
        assert width>0
        M=[canon(*e) for e in color["edges"]]
        assert len(M)==len(set(M))
        assert all(e in edges for e in M)
        for i,e in enumerate(M):
            for f in M[i+1:]:
                assert len(set(e)|set(f))==4,(name,"share endpoint",e,f)
                for u in e:
                    for v in f:
                        assert canon(u,v) not in edges,(name,"physical conflict",e,f,u,v)
        for e in M:
            covered[e]+=width
        if any(s in e for e in M) and any(t in e for e in M):
            joint+=width
        total+=width
    for e in edges:
        assert covered[e]==m[e[0]]*m[e[1]],(name,"cover",e,covered[e])
    assert total==Q(5,4),(name,"budget",total)
    rs=m[s]*sum((m[v] for v in adj[s]),Q())
    rt=m[t]*sum((m[v] for v in adj[t]),Q())
    D=rs+rt+a*b-Q(5,4)
    assert D>0 and joint==min(rs,rt) and joint>=D,(name,D,joint,rs,rt)
    assert cert["D"]==str(D) and cert["J"]==str(joint)
    result={"name":name,"status":"PASS","vertices":len(m),"edges":len(edges),
       "colors":len(cert["palette"]),"J":str(joint),"D":str(D),
       "optimal_J":str(min(rs,rt)),"sha256":DIGEST[name],
       "scope":"ONE FIXED GRAPH, NOT UNIVERSAL"}
    print(json.dumps(result,ensure_ascii=False))
    return result

if __name__=="__main__":
    check("tree23")
    check("core18")
