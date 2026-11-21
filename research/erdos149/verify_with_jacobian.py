"""Independent exact LP replay of the physical 7-edge path with Jacobian.

Jacobian computes the optimum for the SAME induced-matching LP used by
Certo `opt` (19 palette columns, exact weights). The result is meaningful
only for this finite example, not for the universal Erdős-149 conjecture.

Usage:
  python research/erdos149/verify_with_jacobian.py
"""
from __future__ import annotations
import json
from pathlib import Path
from fractions import Fraction as F
from jacobian._exact import CanonicalRational
from jacobian.math.optimization import general_linear_program
from jacobian.math.optimization._general_models import GeneralRationalLinearProgramRequest

ROOT=Path(__file__).resolve().parents[2]
K=F(5,4)

def q(value):
    v=F(str(value))
    return CanonicalRational.from_integer_ratio(v.numerator,v.denominator)

def main():
    source=ROOT/"examples"/"erdos149_arco3_palette_path.json"
    lp=json.loads(source.read_text(encoding="utf8"))
    names=lp["var_names"]
    vars=[{"name":name,"lower_bound":q(0),"upper_bound":q(K)} for name in names]
    objective={"sense":"MAXIMIZE","coefficients":[q(lp["obj"].get(v,0)) for v in names]}
    rel={"==":"EQ","<=":"LE",">=":"GE"}
    rows=[{"label":name,"coefficients":[q(coeff.get(v,0)) for v in names],
           "relation":rel[sign],"rhs":q(rhs)}
          for name,coeff,sign,rhs in lp["cons"]]
    req=GeneralRationalLinearProgramRequest.model_validate(
      {"program":{"variables":vars,"objective":objective,"constraints":rows}})
    answer=general_linear_program(req.program)
    if answer.status!="OPTIMAL":
        print(json.dumps({"status":answer.status,"note":"No theorem-level consequence"}))
        raise RuntimeError("Jacobian did not prove exact optimum on finite path LP")
    vals=tuple(v.as_fraction() for v in answer.primal_candidate)
    got=answer.primal_objective.as_fraction()
    dual=answer.dual_objective.as_fraction()
    assert all(v>=0 and v<=K for v in vals)
    for _name,coeff,sign,rhs in lp["cons"]:
        lhs=sum((F(str(coeff.get(name,0)))*vals[j] for j,name in enumerate(names)),F())
        value=F(str(rhs))
        assert {"==":lhs==value,"<=":lhs<=value,">=":lhs>=value}[sign],(_name,lhs,value)
    assert got==sum((F(str(lp["obj"].get(name,0)))*vals[j] for j,name in enumerate(names)),F())
    assert got==dual==F(63,100),(got,dual)
    print(json.dumps({"status":"PASS","backend":"Jacobian general exact rational LP",
                      "problem":"7-edge physical path exact palette",
                      "variables":len(vars),"constraints":len(rows),
                      "J_max":str(got),"dual":str(dual),"scope":"ONE FIXED GRAPH"},indent=2))

if __name__=="__main__":
    main()
