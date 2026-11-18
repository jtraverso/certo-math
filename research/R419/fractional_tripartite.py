"""R419 integer checker of a 3-colour H with 54 edges and exact fractional packing."""
from itertools import product
P = {(2,2,2),(1,2,1),(3,1,4),(0,3,1),
     (0,4,0),(2,3,0),(4,0,3)}
# Allowed triples of role indices, each has a vertex of every geometric colour.
D = [
    [[2,4],[2,3],[3,4],None,None],
    [[0,2],[0,2],None,[3,4],[3,4]],
    [[1,4],[1,3],None,None,[3,4]],
    [[0,1],[0,3],None,None,[3,4]],
]
# Explicit table kept below as one witness for all 36 weight-1/2 triangles.
SUPPORT=[
 [(2,4),(2,3),(3,4),None,None],
 [(0,2),(0,2),None,(3,4),(3,4)],
 [(1,4),(1,3),None,None,(3,4)],
 [(0,1),None,(0,3),(2,3),(1,2)],
 [None,(0,1),(0,4),(2,4),(1,2)],
]
E={('ab',a,b) for a in range(5) for b in range(5)}
E|={('ac',a,c) for a in range(5) for c in range(5)}
E|={('bc',b,c) for b in range(5) for c in range(5)}
for a,b,c in P:
    E.difference_update({('ab',a,b),('ac',a,c),('bc',b,c)})
assert len(E)==54
counts={e:0 for e in E};tris=[]
for a in range(5):
  for b in range(5):
    entry=SUPPORT[a][b]
    if entry is None: continue
    for c in entry:
      t=(a,b,c);tris.append(t)
      for e in (('ab',a,b),('ac',a,c),('bc',b,c)):
        assert e in counts,(t,e)
        counts[e]+=1
assert len(tris)==36 and set(counts.values())=={2}
# Every H-edge is covered twice by 36 triangles of weight one-half.
print("PASS H=K5,5,5 minus seven edge-disjoint triangles")
print("54 H edges; 36 fractionally selected triangles; every edge load exactly 1")
print("F_loc = 36, primal checker integral-only")
