# Erdős #149 — S599: paired-root shadow peeling and an exterior-mass barrier

**Status:** new universal SUFFICIENT criteria and necessary restrictions on a hypothetical G1 obstruction. **G1 universal OPEN; Erdős #149 OPEN.** These lemmas do not close other gates.

## Hypotheses

Let H be a finite simple *physical* graph carrying vertex masses m_v>0, with distinguished nonadjacent roots s,t having no common neighbors. Let x=m_s, y=m_t, a,b be the masses of a proposed arc s-u-v-t. Assume all old and new degree rows hold, 1/2<x,y<3/4, x+y>5/4, Q_H≤K=5/4, and D=r_s+r_t+ab-K>0 where r_s=x d_H(s), r_t=y d_H(t).

Put R=E_H(s)∪E_H(t), I=E(H)\R, and B=max(r_s,r_t)<3/4. The universal Hall lemma S597 synchronizes ALL the smaller root star against the larger one in a palette P_R of width B, with exact joint overlap J=min(r_s,r_t). Complete to width K with empty colors. The compatibility of root edges and all other pairs ALWAYS uses the original physical H, even when edges cease to demand colors.

## Theorem C14-A: paired-shadow peeling

For a fixed fully synchronized root palette P_R, and each interior edge e, define the **root shadow**

    sigma_P(e)=measure of root-palette colors containing a root edge
                 physically incompatible with e.

For any nonempty T⊆I define

    Lambda_T(e)=sum{w_f: f∈T and (f=e or f conflicts strongly with e)}.

If there is an order e_1,...,e_k that removes all interior edges,
each satisfying

    sigma_P(e_i) + Lambda_{T_i}(e_i) <= K,      (C14-A)

where T_i is the interior set still present immediately before its
removal, then H admits an **exact** palette of width K with
J=min(r_s,r_t)≥D, and the proposed three-edge arc is reinsertable.

**Proof:** start with the fixed Hall palette P_R. Restore the
e_i in reverse order. At the time of restoring e_i, root edges
block a measure at most sigma_P(e_i), while previously restored
interior edges block at most Lambda_{T_i}(e_i)-w_{e_i}
(by exact coverage and the union bound). Hence at least

    K-sigma_P(e_i)-Lambda_{T_i}(e_i)+w_{e_i} >= w_{e_i}

of measure permits e_i. Split the classes as necessary and insert
exactly w_{e_i}. No root edge is ever removed or added, so J
remains min(r_s,r_t). This works for rational palettes and,
by continuity or real interval measures, real masses. QED.

**Strict improvement over S597:** A physical cross-edge e joining
N(s) to N(t) conflicts with ALL root edges on both sides.
S597 adds their individual demands r_s+r_t in its load.
The synchronized palette occupies just B, because paired root
edges share colors: sigma_P(e)=B.
More explicitly, if z_{pq} is the measure of a paired root color
containing s-root p and t-root q, and S_e,T_e are the root edges
incompatible with e, then

    sigma_P(e) = sum_{p∈S_e}w_p + sum_{q∈T_e}w_q
                 - sum_{p∈S_e,q∈T_e} z_{pq}.     (C14.shadow)

This is a *single-palette simultaneous* overlap correction.
The program \`s599_paired_shadow.py\` builds the Hall flow in
rational arithmetic, calculates every sigma exactly, peels, and
reconstructs the complete physical palette in reverse, checking
each conflict and every demand.

**C14-B, palette-independent criterion.** Since sigma_P(e)≤B,
it suffices that an interior peeling order obey

    Lambda_{T_i}(e_i) <= K-B.                  (C14-B)

Because B<3/4, K-B>1/2. Consequently every hypothetical
obstruction G1 must possess a nonempty interior conflict core
which has Lambda_U(e)>1/2 for ALL its edges e∈U, i.e. it is not
weighted-1/2-degenerate. This is a necessary obstruction, not a
claim that all such cores obstruct.

## Theorem C14-C: exterior mass at least 1/8

Let A=N_H(s), C=N_H(t), which are disjoint. Split I into:

- I_near={uv∈I: u,v∈A∪C};
- I_far=I\I_near.

Write W_near=sum_{e∈I_near}w_e and W_far similarly.
A degree-row double count yields

    2 W_near <= (1-x)d_H(s)+(1-y)d_H(t).

Indeed, for each v∈A its old neighbor load excluding s is ≤1-x;
for v∈C it is ≤1-y. Each edge entirely within A∪C is counted
twice, and additional incident edges can only increase the sum.

Since d_H(s),d_H(t)≤1 and B≤max(x,y),

    B+W_near
       <= max(x,y)+[(1-x)+(1-y)]/2
       = 1+|x-y|/2 <9/8.

**Therefore if W_far≤1/8,**

    B+W_near+W_far < K.

Take the completely synchronized Hall palette of width B and pay
each interior edge separately in disjoint bands of total width
W_near+W_far. Complete to K with empty colors.
Every physical conflict is respected, and J=min(r_s,r_t)≥D.

This proof does NOT even need the inductive hypothesis Q_H≤K.

**Stronger relative-core consequence.** Let A* be the
root-ANCHORED surviving demand support of the S597 relative
conflict-core reduction, retaining the same original H for
physical conflicts. S597.5 says Jmax(H)=Jmax(A*) assuming Q_H≤K.
Apply the preceding argument to the interior edges of A* only.
If their far mass W_far(A*)≤1/8, then Jmax(A*)=min(r_s,r_t)
and hence G1 closes in H.

Thus a hypothetical G1 obstruction must meet BOTH necessary tests:

    (i) a nonempty interior weighted >1/2 conflict core;
    (ii) W_far(A*)>1/8, measured AFTER S597 root-anchored reduction.

These restrict, but do not contradict, a general graph. An isolated
near-tight C5 is removed from A* if it has no physical strong-conflict
path to the root demands; a near-tight C5 joined by a conflict chain
can survive (as in the S597 PG(2,4) construction), and then C12
provides a different sufficient argument.

## Exact verification examples

At x=y=7/10, a=b=1/20, and four neighbors per root of masses
19/80, each star has r_s=r_t=133/200 and D=33/400.

For one cross-edge e=s0-t0:
- w_e=361/6400;
- S597 closed-conflict load is
  2*(133/200)+361/6400=8873/6400 >5/4;
- C14 paired-root load is
  133/200+361/6400=4617/6400 <5/4.
Thus S597 leaves a heavy anchored edge, while C14 eliminates
it and constructs six legal palette classes with J=133/200.

The exact regression tests cover every subset of four disjoint cross
edges (16 graphs; 15 strict improvements in the peeling stage),
plus a connected non-bipartite graph with triangles at s and t and
two internally vertex-disjoint old s–t paths. All satisfy the degree
rows and yield exact rational full palettes and J=133/200.

**What remains OPEN:** the universal G1 statement
Jmax(A*;K)≥D for arbitrary physically realizable anchored cores
with the two necessary properties above. G2–G5 are unchanged.


## Theorem C15: quantitative global stability from palette slack and far mass

This is a NEW analytic G1 certificate coupling the partial near-root palette
to a complete old palette via the exact LP dual. It does **not** assume the
conclusion G1, and it can pass when all elementary C14 and exterior-budget
tests are inconclusive.

Under the same S591 hypotheses, let A* be S597's root-anchored conflict
support, and let W be the total demand on its FAR interior edges, i.e.
those with at least one endpoint outside N_H(s)∪N_H(t).
Assume we have ANY old exact palette of H of width beta<=K=5/4
(not necessarily optimal). Put

    sigma = K-beta >= 0,
    B = max(r_s,r_t),  m = min(r_s,r_t),
    D = r_s+r_t+ab-K >0.

For sigma+W>0, the following bound is UNIVERSALLY valid:

    Jmax(H;K) >= m - W*(beta-B)/(W+sigma).      (C15.0)

When sigma=W=0, the near-root palette directly shows Jmax=m.

Equivalently, a sufficient condition for G1 is

    sigma*(K-B-ab) >= (ab-sigma)*W.              (C15.1)

**Proof (all quantities exact).** S597.5 permits the entire LP to be
restricted to A*, with original physical conflicts. Its dual variables
are tau>=0 and unrestricted lambda_e, with constraints

    tau + sum_{e in M}lambda_e >= h(M)

for every physical induced matching M on A*. Write Phi for
K*tau+sum_e lambda_e*w_e.

(1) The root+NEAR partial palette from C14-C, padded with empty
colors to width K, has joint overlap m and covers R plus every near
edge of A* exactly. Integrating dual inequalities over it gives

    K*tau+sum_{R union near}lambda_e*w_e >= m.

The singleton matching of each far edge has h=0 and therefore
lambda_e>=-tau. Consequently

    Phi >= m-tau*W.                              (C15.a)

(2) Restrict the old complete beta-palette of H to A*.
The two root stars still occupy measures r_s,r_t and their
intersection has width >=r_s+r_t-beta=m+B-beta (inclusion-exclusion).
Integration gives

    beta*tau+sum_{e in A*}lambda_e*w_e >= m+B-beta.

Thus, putting sigma=K-beta,

    Phi >= m+B-beta+sigma*tau.                   (C15.b)

By strong linear programming duality,
Jmax(H;K)=min Phi. For every tau>=0, Phi is bounded below
by the maximum of the two affine functions in (C15.a,b).
For W+sigma>0, their intersection is

    tau_*=(beta-B)/(W+sigma)>=0,

because beta>=B (all root edges must be covered).
The minimum of their maximum occurs at tau_* and equals
m-W*(beta-B)/(W+sigma), proving C15.0.

The inequality C15.0 >= D is equivalent to

    W*(beta-B) <= (K-B-ab)*(W+sigma),
    W*(ab-sigma) <= sigma*(K-B-ab),

which is C15.1. If beta<=K-ab (sigma>=ab), this specializes to
the standard easy reinsertion by extra empty colors. QED.

**Dual necessary interval.** If G1 fails with sigma>0, every
obstructive dual must satisfy BOTH

    tau*W > K-B-ab,
    sigma*tau < ab-sigma.

A certificate passes whenever these intervals are disjoint.
Certo's \`examples/erdos149_s599_c15_slack_exterior.py\` verifies
the universal real-algebra contradiction under C15.1.
The combinatorial root/near construction and LP integration
are proved above, not encoded as graph quantifiers by Certo.

### Strict finite control: tuned 3-connected 70-vertex PG(2,4) profile

Keep S597's physical incidence graph (70 vertices, 157 edges,
3-vertex-connected), with x=y=7/10, a=b=1/20.
Choose C5 cycle masses c=999/2000 and tiny positive
connector masses delta=1/100000000. All degree rows remain feasible.

C12's independent physical old-graph split verifies an
upper bound beta on Q_H:

    beta = 5c^2+5delta*(c+19/50)
         = 49900051759/40000000000.

The C5 strong clique alone has demand 998001/800000, which is
strictly GREATER than K-ab=499/400; hence Q_H>K-ab:
the trivial spare-budget criterion is UNAVAILABLE.

The exact S597 rooted-core extractor leaves 111 nonroot
ANCHORED edges, no root-free components, and gives

    W_far(A*)=38741/10000 > 1/8.

The old S597 peeling and C14 paired-shadow peeling
both remain OPEN on this graph. Nevertheless

    sigma=K-beta=99948241/40000000000,
    K-B-ab=233/400,
    D=33/400,

and, with exact rational arithmetic,

    sigma*(K-B-ab) = 23287940153/16000000000000,
    (ab-sigma)*W  = 2005195419/400000000000000.

The first is strictly greater than the second.
Consequently C15 proves G1 for this PHYSICAL GRAPH without
needing a palettisation of the complete graph F:

    Jmax >= 128507950607231/1550639482410000
         = 0.0828741638949527... > D=0.0825.

Its exact positive margin over D is

    290096654203/775319741205000.

The independent script
\`research/erdos149/s599_c15_tuned_pg4.py\` checks the
70-vertex original physical rows and 3-connectivity,
C12's upper bound on Q_H, the anchored core, far mass,
both failed simpler filters, and the rational C15 margin.

**Status:** C15 is a universal CONDITIONAL CRITERION; it is NOT
proved that every H satisfies the C15.1 hypothesis.
G1 universal and Erdős #149 remain OPEN.


## Theorem C15-P: a stronger CONSTRUCTIVE two-palette interpolation

This theorem is independent of the C15 dual formula. It requires only
two explicit operations on exact physical fractional palettes, and is
particularly useful in the near-K regime.

Fix a complete exact palette P0 of H of width beta<=K. Let its
joint root-star overlap be alpha. Trivially

    r_s+r_t-beta <= alpha <= m=min(r_s,r_t).

Construct a second exact full palette P1 of H as follows:
- synchronize both root stars by the Hall theorem S597 in
  a root band of width B=max(r_s,r_t), with overlap m;
- restrict P0 to ALL nonroot old edges by removing root
  edges from each matching; retain its width beta;
- put the two bands in DISJOINT time intervals.
P1 has exact demand coverage, width B+beta and overlap m.
All conflicts are physical; P1 is not required to fit in K.

Put sigma=K-beta. If sigma<=B, take the convex combination

    P=(1-theta)P0+theta P1,  theta=sigma/B.

It has exactly the old demands because BOTH P0 and P1 are full
palettes, and its width equals

    (1-theta)*beta+theta*(B+beta) = beta+sigma = K.

Its joint overlap satisfies

    J(P)=(1-theta)*alpha+theta*m
         >= r_s+r_t-K + (sigma*beta)/B.

If sigma>B, the entire P1 has width beta+B<K and already
satisfies J=m>=D, so no interpolation is needed.

Consequently the new **universal sufficient criterion**

    (K-beta)*beta >= ab*B  ==>  Jmax(H;K)>=D.       (C15-P)

This argument constructs a complete valid palette, rather than
merely excluding a dual. It does NOT require a bound on far-edge
mass, a low weighted conflict core or a clique absorber.

The argument may be sharpened with any known old palette's ACTUAL
joint overlap alpha instead of the minimal
r_s+r_t-beta. Another strengthening is to replace the restricted
interior palette of width beta by an independently certified
interior-only palette of width q_I<=beta; in that case P1 has
width B+q_I and interpolation gains a larger theta.

### New necessary narrow-slack region for every G1 obstruction

Take beta=Q_H (a fractional optimum, attained by an exact palette).
If G1 fails, then

    Q_H*(K-Q_H) < ab*max(r_s,r_t).                (S599.narrow)

In S591's hardest residual we already know:
- Q_H>K-ab (otherwise direct padding reinserts the arc);
- 0<a+b<1/6 hence ab<1/144;
- B=max(r_s,r_t)<3/4.

Therefore

    B/Q_H < (3/4)/(K-1/144)
          = (3/4)/(179/144) = 108/179,

and hence every G1 obstruction must satisfy the purely
uniform NECESSARY condition

    K-Q_H < (108/179)*ab.                         (S599.uniform)

The former easy condition only forced K-Q_H<ab.
The residual window for the old-palette slack has been
cut to at most 60.34% of its previous width.

For the standard rational slice B=133/200, ab=1/400,
K=5/4, solving sigma*(K-sigma)=ab*B gives

    sigma_* approximately 0.00133141813940951.
    G1 obstruction requires sigma<sigma_*
    (equivalently Q_H>1.2486685818605905).

### Strict 70-vertex physical example

For the tuned PG(2,4) instance from C15 above,

    beta=49900051759/40000000000,
    sigma=99948241/40000000000,
    B=133/200, ab=1/400,

so theta=sigma/B=99948241/26600000000 and the
mixing lemma produces the exact LOWER bound

    Jmax>=90107422399121005919/1064000000000000000000
        =0.084687427066843... > D=33/400.

The exact positive margin over D is

    2327422399121005919/1064000000000000000000.

The older C15 dual minimax lower bound was only
0.08287416389495...; the constructive palette mixture
strictly improves it. All arithmetic is rational and
reproducible in \`s599_c15_tuned_pg4.py\`.

The theorem is UNIVERSAL AS A SUFFICIENT CRITERION, but the
hypothesis (K-Q_H)Q_H>=ab B is not known for every H.
The G1 arc-3 universal statement remains OPEN.
