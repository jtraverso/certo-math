"""S602 signed Horn C5 collar: exact full 24-edge physically legal palette.

At least one cycle vertex has mass above 1/2; C21 nonnegative-alpha
hypothesis fails, while S602 signed cancellation still constructs all
colors without a C20 exceptional-budget assumption.
"""
from fractions import Fraction as F
import json
from s600_c20_quadratic_collar import build_general,build_balanced,fixture

def unequal():
    M={"s":F(7,10),"t":F(7,10),
       "p":F(1,20000),"q":F(1,20000),"v":F(1,20000),
       "g":F(1,20000),"r":F(1,20000),"h":F(1,20000)}
    dev=[-F(1,10000),F(3,10000),F(2,10000),F(3,10000),F(3,10000)]
    for side in ("s","t"):
        for i in range(4):M[f"{side}{i}"]=F(19,80)
    for i in range(5):M[f"C{i}"]=F(1,2)-dev[i]
    E=[("s",f"s{i}") for i in range(4)]+[("t",f"t{i}") for i in range(4)]
    E +=[(f"C{i}",f"C{(i+1)%5}") for i in range(5)]
    E +=[("p","C0"),("p","C2"),("q","C3"),("q","C4"),
         ("v","C2"),("v","C3"),("g","C0"),("r","C1")]
    E +=[("p","q"),("g","v"),("r","h")]
    return {"masses":{v:str(m) for v,m in M.items()},
            "edges":[list(e) for e in E],
            "s":"s","t":"t","a":"1/20","b":"1/20"}

data=unequal()
assert F(data["masses"]["C0"])>F(1,2)
d=build_general(data,[f"C{i}" for i in range(5)])
assert d["status"]=="PASS_C22_SIGNED_SUPPORT" and d["signed_mode"]
assert d["edges"]==d["covered"]==24
assert d["C21_bad_DD"]==d["C21_bad_DS"]=="1/400000000"
assert d["C21_Horn_slack"]=="3/20000000"
assert d["C22_signed_credit"]=="21247/25000000"
assert d["spare"]=="169981/200000000"
assert d["J"]=="133/200" and d["D"]=="33/400"
assert d["palette_classes"]==37
print(json.dumps({"name":"unequal_C5_with_vertex_above_half",**d},sort_keys=True))
# No regression of C20/C21: general signed mode should also close
# the original balanced C5 with both classes of nonzero blockers.
old=build_general(fixture(),[f"C{i}" for i in range(5)])
b=build_balanced(fixture(),[f"C{i}" for i in range(5)])
assert old["status"]=="PASS_C22_SIGNED_SUPPORT"
assert b["status"]=="PASS_C21_BALANCED_SUPPORT"
assert old["J"]==b["J"]=="133/200"
print(json.dumps({"name":"balanced_regression","signed":"PASS","nonnegative":"PASS"}))
