"""Exact finite graph regression, without Jacobian or a floating solver."""
from pathlib import Path
import json
from fractions import Fraction as F
from s596_c11 import evaluate

HERE=Path(__file__).resolve().parent
path_graph={"masses":{str(i):w for i,w in enumerate(
 ["7/10","9/10","1/4","1/20","1/20","1/4","9/10","7/10"])},
 "edges":[[str(i),str(i+1)] for i in range(7)],
 "s":"0","t":"7","a":"1/10","b":"1/10"}
nonzero=json.loads((HERE/"fixture_nonzero.json").read_text())

def check(name,inp,expected,heavy):
    r=evaluate(inp,50000)
    assert r["status"].startswith("PASS_C11"),(name,r)
    assert r["heavy"]==heavy,(name,r)
    for side in r["by_side"].values():
        assert F(side["hard_total"])>=0
    print(name,r["status"],"D",r["D"],"heavy",r["heavy"])

check("seven_edge_path",path_graph,"PASS",0)
check("nonzero_heavy_blocker",nonzero,"PASS",1)
r=evaluate(nonzero,0)
assert r["status"]=="UNKNOWN" and r["reason"]=="matching_enumeration_budget_exhausted",r
print("budget_exhaustion",r["status"],"not PASS")
