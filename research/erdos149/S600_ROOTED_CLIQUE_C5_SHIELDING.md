# Erdős #149 — S600: root-preserving conflict clique sums and near-tight C5 shielding

**Mathematical status: new UNIVERSAL reductions and local structural lemmas
under declared S591 hypotheses; G1 itself remains OPEN.**
Neither Certo nor Jacobian nor any finite test is a proof of the full
Erdős–Nešetřil conjecture.

## 1. Root-preserving clique separator theorem (S600.1)

Let H be the full old PHYSICAL graph, and C=L(H)^2 its conflict graph
with vertices E(H). Let T be any demand support retaining every root
edge R=E_H(s)∪E_H(t); conflicts between types are always defined by
the ORIGINAL physical H, not by the demand support.

Suppose S⊆T is a CLIQUE of C[T] and U is a connected component
of C[T]−S with U∩R=∅. Define T'=T\U.

For K=5/4, if Q_H≤K (hence an old exact K-palette exists), then

    Jmax(T;K) = Jmax(T';K).

This holds for any clique size, including S=∅, and for rooted overlap
J defined by colors containing one s-edge and one t-edge.

**Proof ≤.** Restrict any full T-palette to T'; all demands of
T' remain exact and the root marks of each color remain unchanged.

**Proof ≥.** Take a K-palette P of T' maximizing J and a K-palette
P0 of H, restricted to S∪U. The restriction P0 has exact demands
on S∪U. Since S is a clique in the CONFLICT graph, a color can
contain at most one S-type. Accordingly, either palette may be
reparameterized by a measure-preserving permutation of [0,K] so
that they have identical S-type labels at every time: label e∈S
occupies exactly w_e of measure; the no-S label occupies
K−Σ_{e∈S}w_e. Overlay them. There is no conflict between
U and T'\S, by definition of the separated component; the S
type appears only once. Thus every merged class is physical
induced matching, all demands are exact, and because U contains
no root edge, J is precisely the value of P. This proves ≥.

Iterating yields a rooted **clique-prime conflict kernel**. Any
G1 obstruction can be reduced to one where no root-free branch
is detached by any clique separator. This is NOT the same as
a vertex separator of the physical graph and does not imply
a bounded-size kernel.

Executable physical graph witness verifier:
\`research/erdos149/s600_conflict_clique_cut.py\`.

## 2. A finite near-tight physical witness beyond C15-P

The graph \`research/erdos149/s600_neartight_fixture.py\` has 19 vertices
and 19 edges. Its roots s,t have masses x=y=7/10; each has four
old neighbors of mass 19/80, so r_s=r_t=133/200,
and a=b=1/20, D=33/400>0.

A physical 5-cycle has all five vertex masses
c=(1−epsilon)/2, epsilon=1/1000000.
The connector path A0−z0−z1−z2−z3−C0 has all internal
masses delta=epsilon/2. The other old root-side edges include
A0−B0. All physical degree rows, including the proposed new
arc, are satisfied, and all vertex masses are in (0,3/4).

An order-two conflict clique separator
S={A0−z0,z0−z1} isolates an 8-demand root-free branch
including the five edges of the near-extremal C5.

A complete exact palette can be built without LP solving:
four pairs {s−Ai,t−B_pi(i)} of width 133/800 each,
permutation pi=(1,0,2,3), plus a singleton A0−B0 of width
361/6400. This root-side palette of width <1 is physically
compatible with all five C5 edges. Overlay it with five C5
singleton colors of width c² each. Pay the five connector-path
edges in new disjoint bands, and finish with the empty color
to budget K=5/4.

All demanded edges and physical conflicts are checked exactly
with fractions by the script. It obtains

    J=133/200 > D=33/400,
    K−ab < 999998000001/800000000000
             <= Q_H
             <= 4999991475007/4000000000000 <K.

The lower bound is the sum of five mutually conflicting C5
edge demands. The C15-P sufficient condition cannot hold for
this physical input, since even at the smallest possible beta
its maximum slack credit obeys

    K*(K − 999998000001/800000000000)
       = 1999999/640000000000
       < ab*B = 133/80000.

This is a **finite control of the structural strategy**, not
a universal G1 proof. The old weighted load peeling may also
certify this same input; S600 does not claim otherwise.

## 3. Sharp five-cycle fixed-vertex stability

Let (z,p,c,d,q) be five consecutive masses around a physical
5-cycle, satisfying the five row constraints. If 0≤z≤1/2,

    w(E(C5)) = z(p+q)+pc+cd+dq <= 1+z².        (S600.2)

**Proof.** For fixed z,p,q, the objective increases with c,d, so
put c=1−max(z,q) and d=1−max(z,p) from the cycle rows.
By reversal assume p≤q.

- z≥q≥p: objective = p+q+(1−z)²
  ≤2z+(1−z)²=1+z².
- z≤p≤q: objective = 1−pq+z(p+q)
  =1+z²−(p−z)(q−z) ≤1+z².
- p≤z≤q: objective = 1+z²−(z−p)(1+z−q)
  ≤1+z², since 0≤q≤1.

Reflection covers q≤z≤p. Sharpness is witnessed by
p=q=z and c=d=1−z for z≤1/2 (within the cycle row regime).
The optional minimal-counterexample mass cap m_v<3/4
can further strengthen the bound in other configurations.

## 4. Heavy root gap from the residual assumptions

In S591's hard residual,
K=5/4, 1/2<x,y<3/4, a,b>0, a+b<1/6,
r_s≤x(1−a), r_t≤y(1−b),
and r_s+r_t+ab>K.

Consequently:

    x−1/2 > (a+b)/2−ab > 11ab,
    y−1/2 > (a+b)/2−ab > 11ab.              (S600.3)

Indeed x+y−xa−yb+ab>K and the other root is
strictly less than 3/4. Moreover, since (a+b)<1/6,
ab ≤(a+b)²/4 <(a+b)/24, hence (a+b)/2>12ab.

## 5. Main local structural theorem: near-tight C5 are at DISTANCE THREE

For every physical 5-cycle C5 in H, if

    w(E(C5)) >= K−ab,

then BOTH distinguished roots satisfy

    d_H(s,V(C5))>=3,   d_H(t,V(C5))>=3.       (S600.4)

Proof by exhaustive distance cases for root s of mass x
(the argument for t is its mirror):

(i) s itself belongs to C5. Write (x,p,c,d,q)
around the cycle. The row at s gives p+q≤1−a,
and the rows at its two cycle neighbors give c,d≤1−x.
Thus
    w(C5)=p(x+c)+q(x+d)+cd
          ≤1−a+(1−x)² <K−a<K−ab
because x>1/2 and 0<b<1. Contradiction.

(ii) s is outside but adjacent to vertex z of C5. The
row at z gives p+q≤1−x and the two neighboring
cycle rows give z+c≤1,z+d≤1. Thus
    w(C5)=p(z+c)+q(z+d)+cd
          ≤p+q+cd.
A cap-free inequality, valid for every physical C5, says

    w(C5)≤1+(p+q)²/4≤1+(1−x)²/4≤17/16<K−ab.

To derive it, maximize c,d for fixed z,p,q using the
cycle rows: c=1−max(z,q), d=1−max(z,p). Reflecting
the cycle assume p≤q. If z≥q, w(C5)=p+q+(1−z)²
≤1+(p+q)²/4. If z≤p, w(C5)=1−pq+z(p+q)
≤1+p²≤1+(p+q)²/4. If p≤z≤q,
w(C5)=1+p²−(z−p)(1−p−q)
≤1+p²≤1+(p+q)²/4, using p+q≤1/2.
Thus no minimal-model vertex mass cap is needed for
this distance-one case. Contradiction.

(iii) s is at distance two from C5. Choose s−w−v
with v∈C5. Since the row at w includes both x and
z=m_v, z≤1−x<1/2. By S600.2,

    w(C5)≤1+z²≤1+(1−x)².

But
    K-[1+(1−x)²]
       =(x−1/2)(3/2−x)
       > (11ab)(3/4)>ab
by S600.3 and x<3/4. Contradiction.

**Corollary:** every edge of such a near-tight physical C5
is compatible with EVERY old root edge of s or t, because
its cycle vertices are at physical distance >=3 from both roots.
Its strong clique palette may therefore share colors directly
with the two root stars. Physical connector edges outside C5
still need to be paid; the theorem does not bound their total
demand automatically.

Certo specifications (real algebra only):
- \`examples/erdos149_s600_root_margin.py\`;
- \`examples/erdos149_s600_c5_fixed_vertex.py\`;
- \`examples/erdos149_s600_c5_distance.py\`;
- \`examples/erdos149_s600_c5_adjacent_capfree.py\`.

Each is an implication with explicit hypotheses, not a
quantified proof that all near-K fractional chromatic graphs
contain a heavy C5.

## 6. Negative calibration: rooted cores need not be bipartite

The certified 18-vertex, 29-edge physical instance in
\`research/erdos149/s600_nonbip_core_falsation.py\` has
all positive vertex masses <3/4 and all proposed arc rows
feasible. Its K-palette is explicitly encoded, with
26 nonempty rational colors of combined width 23541/32000
and an empty complement. Every edge is covered exactly
and all physical conflicts are checked.

Nevertheless S597 weighted peeling retains a root-anchored
demand core whose endpoint-induced ORIGINAL physical graph
contains an odd cycle. Thus the attractive shortcut

    'every stable anchored demand core is bipartite'

is **FALSE**, even with Q_H<1.
This does not refute G1: the instance passes the easy
Q_H≤K−ab test.

## 7. Remaining precise gate

G1 still asks that for EVERY physically feasible H with Q_H≤K
in the residual, one can construct a palette of width K with

    J>=r_s+r_t+ab−K.

From S599, a counterexample must satisfy
K−Q_H<(3/5)ab and a nonempty rooted heavy conflict
core with W_far(A*)>1/8.
From S600, it may also be assumed clique-prime after
root-free cut pruning, and any near-tight strong C5 is
compatible with both root stars.

**The missing universal result is an extremal/stability
statement for the remaining connectors and/or non-C5 dual
supports.** None of the above proves that the entire old
near-K demand is carried by a single near-tight C5.
Do not mark G1 or Erdős #149 closed.


## 8. New universal Horn–Motzkin–Straus C5 incidence budget (C18)

Let \`v0,...,v4\` be five vertices of a physical 5-cycle, with
masses \`m_i>=0\` satisfying the physical row inequalities.
Denote the total weight of the *five cycle edges* by

    W_5 = sum_{i mod 5} m_i*m_(i+1),

and the weight of all physical edges with EXACTLY ONE endpoint
on those five vertices by \`I_5=w(delta(V(C5)))\`.
Any chords among the five vertices remain separate demands.

**THEOREM C18-A, global local budget:**

    sum_i m_i - W_5 <= 5/4,
    W_5 + I_5 <= 5/4.                         (S600.7)

The second inequality is a NONTRIVIAL absorption budget:
the five pairwise strongly conflicting cycle edges may receive
disjoint colors of width W_5, and every crossing edge may
receive its own singleton colors of total width I_5.
These classes fit within the SAME total K=5/4.

**Algebraic proof of first inequality.**
Set \`u_i=m_i−1/2\` and \`z_i=1−m_i−m_(i+2)>=0\`
(modulo five). By the physical row at the intermediate vertex,
every z_i is nonnegative.

A direct polynomial expansion, verified independently by Certo,
gives the exact identity

    4*(K - sum_i m_i + W_5)
       = (sum_i z_i)^2 - 4*sum_i z_i*z_(i+2).

The five edges {i,i+2} form ANOTHER triangle-free 5-cycle.
For any nonnegative masses z_i on a triangle-free graph,
the weighted adjacency product sum is at most
\`(sum_i z_i)^2/4\` (weighted Mantel/Motzkin–Straus).

A self-contained proof is available by pairwise COMPRESSION:
if i,j are nonadjacent and both masses are positive, the
edge-energy is affine in the transfer of their combined mass
between i and j. Move all mass to the vertex whose
current neighbor-mass sum is larger. The energy cannot decrease,
the total mass is preserved, and the number of positive
vertices strictly falls. Repeating leaves support on a
clique, of size at most two in a triangle-free graph.
Then AM–GM bounds the sole remaining product by
one quarter of the square of the total mass.
This proves the first inequality **for ALL nonnegative reals**.
Certo checks the five-variable polynomial identity, a
representative no-loss transfer, and the two-variable AM–GM
conclusion; the compression induction is the analytic step
and is not claimed to have been quantified in a single SMT spec.

**Exact row-slack decomposition.**
Let \`r_i=sum_{v outside C5, v~v_i}m_v\` and
\`s_i=1−m_(i−1)−m_(i+1)−r_i >=0\`.
This includes any chord demands as additional slack constraints.
By the physical rows,

    I_5=sum_i m_i*r_i
       =sum_i m_i−2 W_5−sum_i m_i*s_i.

Therefore

    K−W_5−I_5
     =1/4*((sum z_i)^2−4*sum z_i*z_(i+2))
      +sum_i m_i*s_i >=0.                  (S600.8)

Each term is nonnegative. This identity gives an exact
quantitative *stability budget*, not just an inequality.
It is replayed with fractions and a logged Motzkin–Straus
compression in \`research/erdos149/s600_c5_horn_budget.py\`.

### C18-B, a complete G1 subcase (not universal G1)

Assume the G1 heavy residual S591 and choose a C5 with
\`W_5 >= K−ab\`. By S600.4, the entire C5 lies at
physical distance at least 3 from BOTH roots, hence each
of its five edges is compatible with ALL old root edges.
Also \`W_5 > K−1/144 >3/4 >B=max(r_s,r_t)\`.

The root-star Hall palette has width B and joint overlap
\`m=min(r_s,r_t)\`. Overlay it with the five disjoint
cycle singleton colors in width W_5, padding the root
palette with empty colors. This is PHYSICALLY legal.
Add all crossing edges of the cycle in independent
singleton bands of total width I_5. By C18-A,

    total width <=W_5+I_5<=K,
    J = min(r_s,r_t) >= D.

Therefore the G1 reinsertion gate is CLOSED for the full
demand support

    T = old root edges R
        union the five cycle edges
        union delta(V(C5)),

even if the crossing edges connect to arbitrary exterior
vertices. It is important that T need not contain all
edges of H; if there are chords on C5 or additional
exterior edges not in T, those demands STILL need to
be added by a valid extension (peeling, clique-sum,
or a separate palette proof). The full G1 universal
statement remains OPEN.

This removes the previous need to estimate each connector
edge's contribution separately in this support family.
In the 19-vertex S600 finite witness, the cycle and
its single crossing edge consume exactly

    W_5 = 999998000001/800000000000,
    I_5 = 999999/4000000000000,
    remaining K-W_5-I_5 = 2249999/1000000000000.

The other four path edges and the cross-edge A0−B0
are handled by its independently checked full rational palette.


## 9. C19 — Quantitative near-tight five-cycle conflict collar

**Universal local theorem, not G1 closure.** Under the S591 heavy residual, set delta=ab in (0,1/144). Suppose an old physical C5 of five-cycle demand W5 >= 5/4-delta.

**Cycle vertex stability.** Put L=1/2-2delta and U=1/2+2delta. If a C5 vertex has mass z<=1/2, the fixed-vertex theorem S600.2 gives W5<=1+z². Hence z²>=1/4-delta>L² (because 0<delta<1/144), so z>L. For a larger z>1/2 this is automatic. The cycle row m_i+m_(i+2)<=1 then forces every m_i<U. Thus L<m_i<U at all five vertices.

**Induced cycle and neighbor masses.** At each cycle vertex v, its two cycle neighbors already have total mass >2L. Hence the sum of exterior neighbor masses is <1-2L=4delta. A chord would itself have mass >L>4delta, impossible: the near-tight C5 is induced. Every external neighbor u in X=N_H(V(C5))\V(C5) has mass m_u<4delta.

**First and second conflict layers.** Let W1 be the demand of physical edges crossing from V(C5) to X; Horn S600.8 gives W1<=5/4-W5<=delta. Let W2 be the demand of all physical edges with at least one endpoint in X and neither endpoint on C5. Write c(u)=sum of masses of C5 neighbors of u. We have c(u)>L and the row at u gives d_(H-C5)(u)<=1-c(u). Therefore

    W2 <= sum_(u in X) m_u*(1-c(u))
       < ((1-L)/L)*sum_(u in X)m_u*c(u)
       = (U/L)*W1
       < (37/35)*delta,

where U/L<37/35 follows by exact clearing for delta<1/144. All physical edges outside the induced C5 which strongly conflict with a C5 edge belong to the first or second layer, thus

    W1+W2 < (72/35)*ab.                                  (C19)

The bound is exact and valid for ANY physical graph satisfying the stated rows. This is a bound on **demands**, not on the number of edges and not on the chromatic cost of the remaining graph.

Verification: research/erdos149/s600_c5_collar.py checks two physical instances with fractions, while examples/erdos149_s600_c19_collar_scalar.py checks the real-algebra part using Certo. The graph-theoretic double-counting is proved above.

**OPEN:** Neither Q_H nearly 5/4 implies the existence of a near-tight physical C5, nor does a small collar guarantee a global palette preserving the root overlap J. Thus the universal G1 obligation and Erdős #149 remain OPEN.
