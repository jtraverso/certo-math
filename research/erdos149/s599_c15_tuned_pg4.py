"""S599: exact rational 70-vertex 3-connected G1 instance closed by C15.

This is NOT a counterexample and NOT a universal proof of G1.
It verifies that the new slack/exterior sufficient condition can pass
even when the simple Q_H<=K-ab, exterior <=1/8 and C14 peeling
criteria all fail.  The known beta upper bound is physically certified
by the C12 old-graph clique split.
"""
from fractions import Fraction as F
import json
import networkx as nx
from s597_pg4_3conn_hard import build
from s597_clique_absorb import assess
from s597_relative_kernel import extract
from s597_weighted_core import analyze
from s599_paired_shadow import prove_instance

K=F(5,4)
eps=F(1,1000)
delta=F(1,100000000)
H=build(eps)
for i in range(5):
    H["masses"][f"omega{i}"]=str(delta)
m={v:F(str(q)) for v,q in H["masses"].items()}
assert len(m)==70 and len(H["edges"])==157
G=nx.Graph();G.add_nodes_from(m);G.add_edges_from(H["edges"])
assert nx.node_connectivity(G)>=3 and min(dict(G.degree()).values())>=3
s,t=H["s"],H["t"]
a,b=F(str(H["a"])),F(str(H["b"]))
for v in m:
    row=sum((m[z] for z in G.neighbors(v)),F())
    if v==s:row+=a
    if v==t:row+=b
    assert row<=1,(v,row)
assert m[s]+b<=1 and m[t]+a<=1
r_s=m[s]*sum((m[z] for z in G.neighbors(s)),F())
r_t=m[t]*sum((m[z] for z in G.neighbors(t)),F())
B=max(r_s,r_t);D=r_s+r_t+a*b-K
assert B==F(133,200) and D==F(33,400)
R=[[f"C{i}",f"C{(i+1)%5}"] for i in range(5)]
split=assess(H,R)
assert split["status"]=="PASS_C12",split
beta=max(F(1),F(split["w_clique"]))+F(split["w_connectors"])
sigma=K-beta
assert beta==F(49900051759,40000000000)
assert 0<sigma<a*b and beta>K-a*b
kernel=extract(H)
assert len(kernel["anchored_demand_edges"])==119
assert not kernel["rootfree_demand_edges"]
neighbors_s=set(G.neighbors(s))
neighbors_t=set(G.neighbors(t))
near=neighbors_s|neighbors_t
rooted={tuple(sorted(e)) for e in kernel["root_edges"]}
Wfar=sum((m[u]*m[v] for raw in kernel["anchored_demand_edges"]
          for u,v in [tuple(raw)]
          if tuple(sorted((u,v))) not in rooted
          and not ({u,v}<=near)),F())
assert Wfar==F(38741,10000)
P=K-B-a*b
lhs=sigma*P
rhs=(a*b-sigma)*Wfar
assert Wfar>F(1,8) and lhs>rhs
Jlower=B-Wfar*(beta-B)/(Wfar+sigma)
assert Jlower>D
assert analyze(H)["status"]=="OPEN_KERNEL"
assert prove_instance(H,make_palette=False)["status"]=="OPEN_KERNEL"
print(json.dumps({
 "status":"PASS_C15","scope":"ONE FIXED 3-CONNECTED PHYSICAL GRAPH",
 "vertices":70,"edges":157,
 "beta_upper_old_H":str(beta),"simple_gap_K_minus_ab":str(K-a*b),
 "slack_sigma":str(sigma),"J_lower":str(Jlower),"target_D":str(D),
 "J_margin":str(Jlower-D),"far_weight_rooted_core":str(Wfar),
 "C15_left":str(lhs),"C15_right":str(rhs),
 "S597":"OPEN_KERNEL","S599_C14":"OPEN_KERNEL",
 "universal_G1":"OPEN","global_Erdos149":"OPEN"
},indent=2))
