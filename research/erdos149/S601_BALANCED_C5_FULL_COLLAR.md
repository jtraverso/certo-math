# Erdős #149 — S601: complete C5 collar with all cycle masses at most 1/2

**Status:** new UNIVERSAL SUBCASE under S591 hypotheses; global G1 and Erdős #149 OPEN. The result colors exactly the root stars, the five C5 edges, and BOTH layers of its strong-conflict collar. Edges farther away remain uncolored.

Let K=5/4, delta=ab in (0,1/144) and D=r_s+r_t+delta-K>0, with positive S591 masses, 1/2<x,y<3/4 and all physical degree rows feasible. Let C5 have masses m_0,...,m_4 at most 1/2 and cycle-edge demand W5>=K-delta. By S600 it is induced and at physical distance >=3 from both roots; every C5 edge is compatible with the root stars. The S597 root Hall palette has width B=max(r_s,r_t)<3/4 and overlap m=min(r_s,r_t)>=D.

Set L=1/2-2delta>35/72. All cycle masses exceed L. Each exterior vertex has either one or two C5 neighbors: X1 denotes the single-neighbor class; X2, the double-neighbor class. Define W1 as demand of edges crossing between C5 and its exterior, W2 as demand of edges with at least one endpoint in X=X1 union X2 but none in C5. S600 yields W1<=delta, W2<(37/35)delta.

An annulus edge is GOOD when compatible with at least one C5 edge, BAD otherwise. Every BAD edge joins X1 to X2 or two vertices of X2: no outside endpoint has three C5 neighbors, and two one-contact vertices cannot jointly cover all five cycle edges.

## Exact Horn dual charge for bad double-double edges

For each cycle vertex let alpha_i=(1-2*m_i)/4>=0, and q_i=1-m_(i-1)-m_(i+1)>=0.

The exact identity is:

    H := K - sum_i(m_i) + W5 = sum_i(alpha_i*q_i).          (S601.1)

For any u in X2 adjacent to C5 vertices i,j, its exterior degree row gives

    d_(H-C5)(u) <= 1-m_i-m_j = 2*(alpha_i+alpha_j).

Therefore the weight of ALL edges with both endpoints in X2 is at most

    W_DD <= 1/2 sum_(u in X2) m_u*d_(H-C5)(u)
         <= sum_i alpha_i * sum_(u in X2, u~v_i) m_u
         <= sum_i alpha_i*q_i = H.                         (S601.2)

The last inequality critically uses alpha_i>=0. The exact C18 row decomposition also gives

    K-W5-W1 = H + sum_i m_i*s_i >= H,

where s_i=q_i - sum_(u in X, u~v_i)m_u>=0. Thus ALL BAD DD edges can be paid with Horn slack, without any extra assumption.

## Mixed one-contact/two-contact bad edges

Let M1=sum_(u in X1)m_u and M2=sum_(u in X2)m_u. Since every u in X2 sees two cycle masses greater than L,

    2 L M2 <= W1 <= delta, so M2 <= delta/(2L)<L.

The weight of BAD X1-X2 edges is at most M1*M2. Meanwhile each u in X1 contributes a unique crossing edge with weight >L*m_u, so the total W_cross1 exceeds L*M1. Consequently

    W_bad_DS <= M1*M2 <= W_cross1.                         (S601.3)

## Constructing exact colors within K

Superpose the root Hall palette proportionally into each of the five singleton C5 colors: cycle edge i, of weight w_i, hosts a scaled copy of the root palette by factor w_i/W5. Its remaining root-free slot has width

    f_i = w_i*(W5-B)/W5
        > L^2*(1-(3/4)/(K-delta))
        > (72/35)*delta.                                  (S601.4)

The combined demand of ALL GOOD annulus edges and ALL crossing edges at one-contact vertices is below W2+W1<(72/35)delta. Every GOOD annulus edge is compatible with at least one cycle edge by definition. Every one-contact crossing edge is compatible with exactly the opposite cycle edge because C5 is induced. Insert them greedily into the free portion of a compatible cycle slot, always avoiding root colors; since all earlier insertions combined weigh less than every f_i, each insertion succeeds without changing palette width or root overlap.

The only remaining collar demands are double-contact crossing edges and BAD DS/DD edges. Pay these with separate singleton colors. By S601.2–3, their total combined cost is at most W1+H; hence the full color width is

    W5 + W_cross2 + W_bad_DS + W_bad_DD
      <= W5 + W1 + H
      <= K.                                                (S601.5)

The root overlap is precisely J=m>=D, proving **C21**.

## Independent exact controls

The implementation is research/erdos149/s600_c20_quadratic_collar.py with balanced=True, plus the wrapper build_balanced(). It retains the original C20 behavior when balanced=False.

The new exact 21-vertex, 24-edge instance (research/erdos149/test_s601_balanced_c5.py) contains BOTH BAD DD and BAD DS edges, each of demand 1/64000000, and a nonzero GOOD annulus edge. The full rational palette has 37 positive classes, exact width K, J=133/200>D=33/400, and empty-color remaining budget 15999/64000000. All physical conflicts and all demanded edges are checked, not just numeric budgets.

Certo real-algebra subchecks:
- examples/erdos149_s601_horn_row_charge.py
- examples/erdos149_s601_free_slots.py

The graph combinatorics (type classification, double-counting, greedy color insertion) are proved above and are not encoded as one solver formula.

## Precisely what remains open

G1 for arbitrary H is **NOT** established. The new theorem assumes a near-tight C5 with every cycle mass <=1/2, and it covers only its two-step strong-conflict collar and the roots, NOT any other remote demand edges. Other near-tight C5 mass profiles and a universal classification of all near-K old palettes remain OPEN. The general Erdős–Nešetřil conjecture remains OPEN.
