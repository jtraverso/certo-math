# Erdős #149 — S603: global G1 completion under a quantitative remote-demand bound

**Theorem:** Fix the S591 weighted heavy residual with K=5/4, delta=ab in (0,1/144), roots s,t, and an old physical C5 of cycle-edge demand W5>=K-delta. Let B=max(r_s,r_t)<3/4 and D=r_s+r_t+delta-K>0. Write S for ALL old root edges, the five C5 edges, all edges crossing from the C5 to its exterior neighbor set X, and all old edges with an endpoint in X but none in C5. Let T=E(H)\S be the REMOTE old demand edges, of total demand W_rem.

The full S602 signed Horn theorem constructs an exact K-palette P_S of S whose root overlap J=min(r_s,r_t)>=D. More precisely, five cycle singleton colors of total width W5 carry a Hall-synchronized root palette of width B. The remaining rootless C5 slots have total width W5-B. S602 inserts, into these rootless slots, every GOOD second-layer edge and every one-contact crossing edge, of total demand

    W_insert < W2+W1 < (37/35+1)delta = (72/35)delta.

All other C5 corona edges are paid in disjoint singleton bands using the signed Horn budget, which does not consume any further rootless C5 slots.

**Key physical observation:** An old edge e∈T has neither endpoint in V(C5) nor in X=N_H(V(C5))\V(C5), hence neither endpoint is adjacent to a C5 vertex. Therefore e is compatible with ALL five C5 edges in the ORIGINAL H, even though e may conflict with root edges or with some previously inserted corona edges.

Now greedily insert remote edges e∈T into rootless C5 color slots, taking measure w_e in slots containing no previously inserted edge that physically conflicts with e. Root edges are excluded from every chosen slot, and all C5 edges are compatible with e.

After the good corona insertions and any earlier remote insertions, the total measure of rootless C5 colors occupied by inserted edges is bounded above by their total EXACT demand. Consequently, if

    W_rem + W_insert <= W5-B,                        (S603.1)

then every remote edge can be inserted in any order. The final palette is an EXACT K-palette of ALL H, preserving J=min(r_s,r_t)>=D.

Because W5>=K-delta and B<3/4, condition (S603.1) is implied by the convenient uniform test

    W_rem <= 1/2-(107/35)delta.                     (S603.2)

Indeed W5-B>1/2-delta and W_insert<(72/35)delta. Since delta<1/144, the right side of (S603.2) is strictly larger than

    1/2-107/5040 = 2413/5040 ≈ 0.47876984.

This is a **universal sufficient condition that closes G1 for the entire old H**, not just its C5 collar. It assumes existence of a near-tight physical C5 and a bound on the total demand outside its two-step strong-conflict collar. It does NOT assert either hypothesis holds for every possible G1 residual.

## Exact nontrivial full-graph witness

The file research/erdos149/test_s603_full_far.py extends S602's signed near-tight C5 example with one remote old edge h-remote of demand exactly 1/10, even though that edge conflicts with the GOOD annulus edge r-h. It is compatible with every C5 cycle edge and every physical row stays feasible.

The exact constructor (research/erdos149/s600_c20_quadratic_collar.py, build_full_far) reconstructs a complete 25-edge, 22-vertex fractional palette of width K with 38 positive classes and root overlap J=133/200>D=33/400. Its original C5 has m_0=0.5001>1/2, so the older S601 nonnegative-charge hypothesis does not apply. The first/second corona includes both nonzero BAD DD and BAD DS edges.

The example has:
- remote demand 1/10;
- rootless C5 color capacity 11680003/20000000 ≈0.584;
- total earlier rootless insertions 6999/100000000;
- final empty-color budget 169981/200000000.

All old demands, all original physical strong conflicts, every mass row, and exact palette width are verified with Fraction. The G1 conclusion holds for this entire fixed H.

Certo tests the exact all-real arithmetic threshold (S603.2) in examples/erdos149_s603_remote_threshold.py. The independent greedy and physical compatibility proof is given above, not hidden inside the SMT model.

## What is still OPEN

Universal G1 asks for every weighted physically feasible H with Q_H<=K. It is NOT known that such a near-tight C5 must exist when Q_H is nearly K; there may be other global fractional dual obstructions. Even if such a C5 exists, the remote demand W_rem may be arbitrarily large, and the inequality (S603.2) need not hold. S603 is therefore a genuine additional solved subfamily, NOT the universal closure of G1. Erdős–Nešetřil #149 remains OPEN.
