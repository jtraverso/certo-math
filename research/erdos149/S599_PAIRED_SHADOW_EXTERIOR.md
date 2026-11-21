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
