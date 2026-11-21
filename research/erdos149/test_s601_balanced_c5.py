"""S601 C21: exact rational complete physical palettes with both bad types.

The five C5 masses are <1/2.  Exceptional DD and DS annulus
edges are both nonzero, so the check exercises BOTH structural
charges rather than winning by a vacuous classification.
"""
from fractions import Fraction as F
import json
from s600_c20_quadratic_collar import build_balanced,build,fixture

def mixed_fixture():
    eps=F(1,8000)
    c=F(1,2)-eps
    mass={"s":F(7,10),"t":F(7,10),"p":eps,"q":eps,
          "v":eps,"g":eps,"r":eps,"h":eps}
    for side in ("s","t"):
        for i in range(4):mass[f"{side}{i}"]=F(19,80)
    for i in range(5):mass[f"C{i}"]=c
    E=[("s",f"s{i}") for i in range(4)]
    E +=[("t",f"t{i}") for i in range(4)]
    E +=[(f"C{i}",f"C{(i+1)%5}") for i in range(5)]
    E +=[("p","C0"),("p","C2"),("q","C3"),("q","C4"),
         ("v","C2"),("v","C3"),("g","C0"),("r","C1")]
    E +=[("p","q"),("g","v"),("r","h")]
    return {"masses":{k:str(v) for k,v in mass.items()},
            "edges":[list(e) for e in E],
            "s":"s","t":"t","a":"1/20","b":"1/20"}

for name,data,edges in [("S600_original",fixture(),20),
                        ("S601_mixed",mixed_fixture(),24)]:
    proof=build_balanced(data,[f"C{i}" for i in range(5)])
    assert proof["status"]=="PASS_C21_BALANCED_SUPPORT",proof
    assert proof["covered"]==proof["edges"]==edges,proof
    assert F(proof["J"])==F(133,200) and F(proof["D"])==F(33,400)
    assert F(proof["C21_bad_DD"])>=0 and F(proof["C21_bad_DS"])>=0
    if name=="S601_mixed":
        assert proof["C21_bad_DD"]==proof["C21_bad_DS"]=="1/64000000",proof
        assert proof["C21_Horn_slack"]=="1/12800000"
        assert proof["spare"]=="15999/64000000"
        assert proof["palette_classes"]==37
    print(json.dumps({"test":name,**proof},sort_keys=True))
legacy=build(fixture(),[f"C{i}" for i in range(5)])
assert legacy["status"]=="PASS_C20_SUPPORT"
print(json.dumps({"test":"backward_compatibility","status":"PASS"}))
