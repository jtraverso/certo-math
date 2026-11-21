"""S603 C23: full weighted G1 closure on a 22-vertex physical graph
with a large remote old edge (weight 1/10) conflicting with the
annulus but compatible with all five near-tight C5 edges.

The theorem applies to arbitrary H whenever total demand of all
edges outside roots+C5+its full two-step collar is small enough.
This test certifies only a rational fixed instance.
"""
from fractions import Fraction as F
import json
from s600_c20_quadratic_collar import build_full_far
from test_s602_general_c5 import unequal
d=unequal()
d["masses"]["h"]="2/5"
d["masses"]["remote"]="1/4"
d["edges"].append(["h","remote"])
r=build_full_far(d,[f"C{i}" for i in range(5)])
assert r["status"]=="PASS_C23_FULL_G1",r
assert r["covered"]==r["edges"]==25
assert r["vertices"]==22 and r["palette_classes"]==38
assert r["uncovered"]==0
assert r["J"]=="133/200" and r["D"]=="33/400"
assert r["remote_weight"]=="1/10"
assert r["root_free_cycle"]=="11680003/20000000"
assert r["free_insert_total"]=="6999/100000000"
assert r["spare"]=="169981/200000000"
delta=F(1,400)
assert F(r["remote_weight"])<=F(1,2)-F(107,35)*delta
print(json.dumps({"name":"22-vertex_remote_cycle_coupled","status":r["status"],
 "n":r["vertices"],"m":r["edges"],"colors":r["palette_classes"],
 "J":r["J"],"D":r["D"],"far_demand":r["remote_weight"],
 "root_free_cycle":r["root_free_cycle"],
 "scope":"one whole physical H, universal G1 still open"},indent=2))
