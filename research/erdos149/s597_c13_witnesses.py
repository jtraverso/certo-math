"""S597 exact C13 witnesses: nonzero anchored heavy and root-free Petersen."""
from fractions import Fraction as Q
import json
from s597_verify_static_palettes import decode
def anchored_cross():
    mass={"s":"7/10","t":"7/10"}
    mass.update({f"s{i}":"19/80" for i in range(4)})
    mass.update({f"t{i}":"19/80" for i in range(4)})
    edges=[["s",f"s{i}"] for i in range(4)]+[["t",f"t{i}"] for i in range(4)]
    edges.append(["s0","t0"])
    return {"masses":mass,"edges":edges,"s":"s","t":"t","a":"1/20","b":"1/20"}

def petersen_bridge():
    import networkx as nx
    base=decode("tree23")
    m={k:Q(str(v)) for k,v in base["masses"].items()}
    E=[list(e) for e in base["edges"]]
    epsilon=Q(1,1000);delta=epsilon/2;c=(1-epsilon)/3
    for i in range(10):m["P"+str(i)]=c
    for u,v in nx.petersen_graph().edges():E.append(["P"+str(u),"P"+str(v)])
    m["link"]=delta
    E.extend([["se1","link"],["link","P0"]])
    base["masses"]={k:str(v) for k,v in m.items()}
    base["edges"]=E
    return base

if __name__=="__main__":
    from s597_weighted_core import analyze,verify
    for name,d in [("cross",anchored_cross()),("petersen",petersen_bridge())]:
        r=analyze(d);verify(d,r)
        print(json.dumps({"name":name,**{k:v for k,v in r.items()
            if k not in ("removed","core_edges")}},indent=2))
