"""S598 exact false-twin split/merge fixture with root overlap unchanged."""
from fractions import Fraction as F
from s598_false_twins import compress, project, lift, edge
from test_s598_conflict_twins import check_physical
import json

p={"masses":{"s":"7/10","t":"7/10",
             **{f"s{i}":"19/80" for i in range(4)},
             **{f"t{i}":"19/80" for i in range(4)}},
   "edges":[["s",f"s{i}"] for i in range(4)] +
           [["t",f"t{i}"] for i in range(4)] + [["s0","t0"]],
   "s":"s","t":"t","a":"1/20","b":"1/20"}
q={**p,"masses":dict(p["masses"]),"edges":[]}
q["masses"].pop("s0")
q["masses"]["s0a"]=q["masses"]["s0b"]="19/160"
for a,b in p["edges"]:
    if "s0" in (a,b):
        for v in ("s0a","s0b"):
            q["edges"].append([v,b] if a=="s0" else [a,v])
    else:q["edges"].append([a,b])
merged=compress(q,"s0a","s0b","s0")
assert merged["masses"]==p["masses"]
assert {edge(*e) for e in merged["edges"]}=={edge(*e) for e in p["edges"]}
palette=[{"width":"133/800",
          "edges":[["s",f"s{i}"],["t",f"t{[1,0,2,3][i]}"]]} for i in range(4)]
palette.append({"width":"361/6400","edges":[["s0","t0"]]})
palette.append({"width":str(F(5,4)-4*F(133,800)-F(361,6400)),"edges":[]})
J=check_physical(p,palette)
original=lift(palette,"s0a","s0b","s0",F(19,160),F(19,160))
assert check_physical(q,original)==J==F(133,200)
roundtrip=project(original,"s0a","s0b","s0")
assert check_physical(p,roundtrip)==J
print(json.dumps({"status":"PASS","original_vertices":len(q["masses"]),
  "quotient_vertices":len(p["masses"]),"original_colors":len(original),
  "J":str(J),"budget":"5/4","physical_edges_original":len(q["edges"]),
  "physical_edges_quotient":len(p["edges"])}))
