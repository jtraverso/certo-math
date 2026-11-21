"""Exact, solver-independent regression for S595 cross-heavy max flow.
This tests finite physical graphs, NOT the universal Erdős problem."""
import importlib.util
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
P=ROOT/"research"/"erdos149_s595_cross_flow.py"
spec=importlib.util.spec_from_file_location("erdos149_s595_cross_flow",str(P))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
from fractions import Fraction as F

def make_path(remote=False):
    masses={str(i):m for i,m in enumerate(
        ["7/10","9/10","1/4","1/20","1/20","1/4","9/10","7/10"])}
    edges=[[str(i),str(i+1)] for i in range(7)]
    if remote:
        for j in range(5):masses["c"+str(j)]="1/2"
        for j in range(5):edges.append(["c"+str(j),"c"+str((j+1)%5)])
    return {"masses":masses,"edges":edges,"s":"0","t":"7","a":"1/10","b":"1/10"}

for label,record in [("path",make_path(False)),("remote_C5",make_path(True))]:
    result=module.evaluate(record)
    assert result["residual"] and result["status"]=="PASS",(label,result)
    assert result["nu_cross"]=="0",(label,result)
    assert F(result["cut_capacity"])==F(result["nu_cross"])
    if label=="remote_C5": assert result["heavy_edges"]==5
    print(label, "PASS", "nu_cross=",result["nu_cross"],"threshold=",result["threshold_exact"])

witness={"masses":{"1":"97/100","2":"1/200","3":"1/200","4":"97/100","5":"3/10","6":"1/200","7":"1/200","8":"97/100","10":"97/100","11":"1/200","t":"13/20","s":"13/20"},"edges":[["t","1"],["1","2"],["1","5"],["2","3"],["2","7"],["3","4"],["3","6"],["4","8"],["s","10"],["10","11"],["11","7"]],"s":"s","t":"t","a":"1/100","b":"1/100"}
result=module.evaluate(witness)
assert result["status"]=="PASS" and result["residual"],result
assert result["D"]=="111/10000",result
assert result["nu_cross"]=="1/40000",result
assert F(result["cut_capacity"])==F(result["nu_cross"])
assert result["cross_pairs"]==1,result
print("rooted_tree_nonzero", "PASS", "nu_cross=",result["nu_cross"],
      "threshold=",result["threshold_exact"])
