# R419: a three-colour fractional/nonintegral gadget and improved almost-quadratic split gap

**Status (2026-11-17):** mathematical proof below; the finite Latin obstruction is certified by Certo-Math v0.40.0 with solver-independent DRAT checking and the fractional witness is verified exactly. A complete Lean formalization and independent audit of the asymptotic transfer are pending. Only the research branch is modified.

## 1. The 15-position tripartite gadget

Let A,B,C be disjoint five-vertex classes indexed by 0,...,4. Start from K_(5,5,5), delete the union of the 21 edges of seven edge-disjoint triangles indexed by

    (2,2,2),(1,2,1),(3,1,4),(0,3,1),
    (0,4,0),(2,3,0),(4,0,3).

Call the resulting graph H. Thus |E(H)| = 75-21 = 54. Its degree into each of the other two colour classes is equal at every vertex.

The following table defines 36 H-triangles of weight 1/2: in each non-prescribed cell (row a, column b), use each listed c. The bracketed singletons indicate the seven prescribed triples that have been DELETED, not triangles of H.

| a\\b | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
|0|2,4|2,3|3,4|[1]|[0]|
|1|0,2|0,2|[1]|3,4|3,4|
|2|1,4|1,3|[2]|[0]|3,4|
|3|0,1|[4]|0,3|2,3|1,2|
|4|[3]|0,1|0,4|2,4|1,2|

Every edge of H occurs in EXACTLY TWO of these 36 triangles, so mass 1/2 is a fractional triangle decomposition. Its residual objective is 36 (each triangle has w=2).

H has no integral triangle decomposition: an integral completion is equivalent to a Latin square of order 5 extending the seven prescribed entries. For symbols 0,1,2, only the two compatible triples of row-to-column permutations below remain:

    symbol0  (4,0,3,2,1)     symbol1  (3,2,1,0,4)     symbol2 (0,1,2,4,3)
    symbol0  (4,1,3,0,2)     symbol1  (3,2,0,4,1)     symbol2 (1,0,2,3,4)

None is compatible with any of the four candidate permutations for symbol 3. This short enumeration is reproduced by the complete CNF encoding. Certo's DRAT certificate is separately verified against the same obligation by `certo verify --obligation --complete`.

## 2. Universal tripartite residual estimate

For ANY tripartite graph B and Q of cardinality v>=2 set
  e=e_B(Q), w(Q)=2e-v(v-1)/2-1.

Turán's inequality e <= floor(v²/3), together with direct checks at v=2,...,8, proves

    w(Q) <= (2/3)e.

Equality can occur only for a B-triangle on 3 vertices or an induced B-copy of K_(2,2,2) on 6 vertices.

Moreover, unless Q is one of those equality pieces, the slack
  s(Q) = (2/3)e - w(Q) = v(v-1)/2 + 1 - (4/3)e
satisfies s(Q) >= e/27. For v>=9 this follows from e<=v²/3 and
  v(v-1)/2 + 1 >= 37v²/81,
with equality possible at v=9; the finitely many smaller v follow from their maximum tripartite edge counts.

## 3. Selected directions and confinement

Let p be an odd prime, K>=1 and p>2K. For each block dimension d_i choose a nonempty integer sphere

  A_i = {x in {0,...,K}^{d_i}: sum(x_j²)=R_i},

and C=product(A_i) subset F_p^k, where k=sum d_i. For each c in C and each line in F_p^(k+1) of direction (1,c), place H on the fifteen points (colour t in {0,1,2}, clone layer r in {0,...,4}) of that line.

The graph B of all installed edges is tripartite, with 54 tau edges, where tau=|C| p^k. Its edges are disjoint between blocks because an edge joining different first colours determines a unique selected direction.

Every B-triangle is inside a unique selected line: the directions of its edges satisfy a+b=2c mod p. Since each coordinate of a,b,c is in [0,K] and p>2K, this holds over the integers. Strict convexity of Euclidean squared norm on each sphere gives a=b=c.

If Q induces K_(2,2,2) in B, all eight B-triangles in Q belong to the SAME line: its triangles are connected through edge overlaps, and B-edges belong to unique selected blocks. Hence every equality piece belongs entirely to one block.

## 4. Global integer defect, no fragmentation lemma

Let P be any packing of core cliques (pairwise edge-disjoint, all pairs count). Define good pieces as triangles or K_(2,2,2) with equality in w<=2e/3, and bad pieces as all others. Then

  (2/3)|E(B)| - sum_(Q in P)w(Q)
     = sum_Q s(Q) + (2/3)(number of B-edges unused by P)
     >= (1/27)(number of B-edges not covered by good pieces).

A good K_(2,2,2) is edge-decomposable into FOUR triangles; because it is confined to a single selected block, the good edges INSIDE EACH BLOCK form a triangle-decomposable subgraph of H.

H is locally balanced (at every vertex, its degrees into the other two parts coincide), as is a union of edge-disjoint triangles. The complementary bad-edge set in each block is therefore locally balanced. If it were empty, H would be triangle-decomposable, a contradiction. Its cardinality is divisible by 3 (the three part-pair edge counts are equal). If it had three edges, local balance would force those three edges to form a triangle, which could be added to the good decomposition; contradiction. Therefore EVERY BLOCK has at least SIX bad edges.

As installed B-edge sets are disjoint, the number of bad edges is at least 6 tau, and

  I(B) <= 36 tau - (6/27) tau = (36 - 2/9) tau.

The 36 weight-1/2 triangles per block provide a feasible global fractional residual packing because each of their edges lies in B and B-edge sets of distinct blocks are disjoint. Thus F(B)=36 tau, and

  F(B)-I(B) >= (2/9)tau.

This does not use the R407/R418 fragmentation lemma, which does not directly extend to five clones per geometric colour.

## 5. Host realization

Take the core to be {0,1,2} x F_p^k x (Z/5). Its 15p^k vertices form a clique. Hosts are independent vertices, with B-independent palettes; every marked (non-B) core pair is assigned to one host, with a matching of assigned pairs per host:

1. Equal first colour: full colour-class palette, host indexed by first colour and the group sum of tail and clone layer (Z/5), at most 15p^k hosts.
2. Different first colours, selected direction: host indexed by c in C and a nonedge of H between the two corresponding role types, exactly 21|C| hosts.
3. Exterior normalized direction z not in C: choose a linear separator K_z containing (1,z) and no (1,c), c in C. Its codimension r_z is one if some digit of z is outside {0,...,K}, otherwise the dimension of the first failed sphere block. For each affine coset, first-colour midpoint (three choices) and unordered clone-layer pair (15 choices), install one host. At most 45 p^(r_z) per exterior z.

An endpoint, a direction, a midpoint and a clone-layer multiset uniquely determine the partner endpoint. This proves matching assignments. The cosets avoid all selected directions, proving B-independent palettes. The standard packing-to-clique-partition bridge then yields D(G)=F(B)-I(B)>=(2/9)tau.

A separate exhaustive model at p=5,k=2,C={(0,1),(1,0)} verified the resulting 375-vertex core, 50 blocks, 2700 B-edges, 2250 B-triangles (all confined), 67425 marked pairs (all uniquely assigned), 7392 actually used hosts, and both the independent palettes and matching conditions.

## 6. Quantitative asymptotics

For q=K+1 and K=floor((p-1)/2), q/p -> 1/2. An integer sphere is selected by pigeonhole with

  |A_i| >= q^(d_i)/(d_i K²+1).

As in R418, the classical bound on representations as a sum of two squares implies the upper density |A_i|/q^(d_i) <= p^(-2+o(1)) when p=exp(Theta((ln n)^(1/3))) and d_i=O((ln n)^(1/3)). The first-failed-block count and staircase optimization therefore transfer unchanged, except that ln 3 is replaced by ln 2; the extra clone/host factor is constant and has no leading logarithmic effect.

Conditional on the quantitative estimate and bridge in R418, this yields for every eta>0 and all sufficiently large n:

  Gamma(n) >= n² exp( -(sqrt(3)*(2 ln 2)^(1/3)+eta) * (ln n)^(2/3) ).

The coefficient is approximately 1.9312823860392643.

**Pending:** independent adversarial audit of the complete asymptotic derivation; Lean assembly. The finite gadgets and the nonextendability obstruction have independent exact certificates. There is no claim to have improved the logarithmic power 2/3.
