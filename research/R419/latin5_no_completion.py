"""R419: exact non-completability of a 7-entry partial Latin square of order 5.

A completion is encoded by 125 Boolean variables x[row,column,symbol].
The three Latin constraints are exact-one: each cell has one symbol, each
row uses each symbol once, each column uses each symbol once.
Certo proves UNSAT with a DRAT certificate, independently checked.
"""
from certo import CNF, CNFSpec

P = [(2,2,2),(1,2,1),(3,1,4),(0,3,1),
     (0,4,0),(2,3,0),(4,0,3)]

def spec():
    c = CNF(title="R419 partial Latin square order 5 cannot be completed")
    x = {(r,k,s): c.var(f"x_{r}_{k}_{s}")
         for r in range(5) for k in range(5) for s in range(5)}
    for r in range(5):
        for k in range(5):
            c.exactly_one([x[r,k,s] for s in range(5)])
    for r in range(5):
        for s in range(5):
            c.exactly_one([x[r,k,s] for k in range(5)])
    for k in range(5):
        for s in range(5):
            c.exactly_one([x[r,k,s] for r in range(5)])
    for r,k,s in P:
        c.add(x[r,k,s])
    return CNFSpec(cnf=c, title="7-entry noncompletable partial Latin 5",
                   expect="unsat")
