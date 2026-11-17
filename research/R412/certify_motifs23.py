"""Generate and verify exact LP certificates for 22 balanced F23 digit motifs.

These are obstructions to asymptotic full-support fixed-composition
constructions, NOT to arbitrary finite caps.
"""
from pathlib import Path
from fractions import Fraction
import subprocess
from certo import LPSpec
from certo.engines import lp
from certo import store

SOURCE=Path(__file__).with_name("motifs23.txt")
OUT=Path("out/r412/motifs")

def instances():
    for line in SOURCE.read_text().splitlines():
        if not line.strip() or line.startswith("#"): continue
        t,digits=line.split(":")
        yield int(t),tuple(map(int,digits.split(",")))

def build(t,D):
    s=LPSpec(sense="max",title=f"Balanced nontrivial F23 motif t={t} digits={D}")
    idx=set(D)
    triples=[(a,b,((1-t)*a+t*b)%23) for a in D for b in D
             if a!=b and ((1-t)*a+t*b)%23 in idx]
    if not triples: raise RuntimeError("No collinear triples")
    names=[f"p_{i}" for i in range(len(triples))]
    for p in names:s.variable(p,0,1)
    s.objective({p:1 for p in names})
    s.constraint({p:1 for p in names},"==",1,name="normalize")
    for a in D:
        v={names[i]:int(x==a)-int(z==a)
           for i,(x,y,z) in enumerate(triples) if (x==a)!=(z==a)}
        if v:s.constraint(v,"==",0,name=f"first_third_{a}")
        v={names[i]:int(y==a)-int(z==a)
           for i,(x,y,z) in enumerate(triples) if (y==a)!=(z==a)}
        if v:s.constraint(v,"==",0,name=f"second_third_{a}")
    return s

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    for i,(t,D) in enumerate(instances()):
        result=lp.opt(build(t,D))
        if not result.meta.get("exact") or result.certificate is None:
            raise RuntimeError(f"Uncertified motif {i}: {result}")
        if Fraction(str(result.meta["objective"]))!=1:
            raise RuntimeError(f"Non-unit optimum motif {i}")
        path=OUT/f"motif_{i:02d}.json"
        store.write_certificate(result.certificate,str(path))
        v=subprocess.run(["certo","verify",str(path)],capture_output=True,text=True)
        if v.returncode or "VALID" not in v.stdout:
            raise RuntimeError(f"Invalid motif {i}: {v.stdout} {v.stderr}")
        print(f"MOTIF_{i:02d} EXACT_PASS t={t} size={len(D)}",flush=True)
    print("ALL_22_MOTIFS_CERTIFIED",flush=True)

if __name__=="__main__":main()
