"""Jacobian exact LP relaxation for C11's simultaneous heavy blockers.

For a *fixed* physical root edge r, binary induced-matching cover variables
are relaxed to [0,1]. Every selected matching gives a feasible LP point,
hence the exact rational LP optimum is a rigorous UPPER bound on B_s(r).
If this LP upper bound is below the S596 threshold, C11 closes that root
without enumerating matchings. Otherwise it is INCONCLUSIVE, not a refutation.

This script independently checks the upper bound and the matching it bounds
on the small physical nonzero-blocker fixture.
"""
import json
from fractions import Fraction as F
from pathlib import Path
from jacobian._exact import CanonicalRational
from jacobian.math.optimization import general_linear_program
from jacobian.math.optimization._general_models import GeneralRationalLinearProgramRequest
from s596_c11 import evaluate

K=F(5,4)

def frac(v):
    v=F(str(v))
    return CanonicalRational.from_integer_ratio(v.numerator,v.denominator)

def calc(data,side="s"):
    m={str(v):F(str(w)) for v,w in data["masses"].items()}
    s,t=data["s"],data["t"]
    edges=sorted({tuple(sorted((str(u),str(v)))) for u,v in data["edges"]})
    E=set(edges)
    def key(u,v):return tuple(sorted((u,v)))
    def compatible(e,f):
        return not(set(e)&set(f)) and all(key(u,v) not in E for u in e for v in f)
    w={e:m[e[0]]*m[e[1]] for e in edges}
    heavy=[e for e in edges if s not in e and t not in e
           and sum((w[f] for f in edges if not compatible(e,f)),F())>=K]
    left=s if side=="s" else t
    right=t if side=="s" else s
    roots=[e for e in edges if left in e]
    opp=[e for e in edges if right in e]
    results=[]
    for root in roots:
        good=[q for q in opp if compatible(q,root)]
        candidates=[e for e in heavy if compatible(e,root)
                    and any(not compatible(e,q) for q in good)]
        if not good or not candidates:
            results.append({"root":list(root),"upper":"0","variables":0});continue
        nz,ny=len(candidates),len(good)
        names=[f"z{i}" for i in range(nz)]+[f"y{i}" for i in range(ny)]
        n=len(names)
        var=[{"name":name,"lower_bound":frac(0),"upper_bound":frac(1)} for name in names]
        obj={"sense":"MAXIMIZE","coefficients":
             [frac(0)]*nz+[frac(w[q]) for q in good]}
        rows=[]
        for j,q in enumerate(good):
            coef=[F(-1) if not compatible(e,q) else F(0) for e in candidates]+[
                F(1) if i==j else F() for i in range(ny)]
            rows.append({"label":f"blocked{j}","coefficients":[frac(k) for k in coef],
                         "relation":"LE","rhs":frac(0)})
        for i,e in enumerate(candidates):
            for j in range(i+1,nz):
                if not compatible(e,candidates[j]):
                    coef=[F(1) if v in (i,j) else F() for v in range(nz)]+[F()]*ny
                    rows.append({"label":f"conflict{i}_{j}",
                                 "coefficients":[frac(k) for k in coef],
                                 "relation":"LE","rhs":frac(1)})
        req=GeneralRationalLinearProgramRequest.model_validate(
            {"program":{"variables":var,"objective":obj,"constraints":rows}})
        result=general_linear_program(req.program)
        assert result.status=="OPTIMAL",result.status
        upper=result.primal_objective.as_fraction()
        assert upper==result.dual_objective.as_fraction()
        results.append({"root":list(root),"upper":str(upper),
                        "variables":n,"candidate_heavy":nz,
                        "q_types":ny,"constraints":len(rows)})
    return results

if __name__=="__main__":
    here=Path(__file__).resolve().parent
    data=json.loads((here/"fixture_nonzero.json").read_text(encoding="utf8"))
    exact=evaluate(data)
    output=calc(data,"s")
    assert exact["status"].startswith("PASS_C11")
    target=exact["by_side"]["s"]["roots"][0]
    assert len(output)==1 and output[0]["upper"]==target["B"]=="1261/2000"
    print(json.dumps({"status":"PASS","tool":"Jacobian 0.23.0 exact primal/dual",
                      "C11_B_s_upper":output[0],"exact_enumerated_B":target["B"],
                      "scope":"one physical nonzero-blocker graph, not universal"},indent=2))
