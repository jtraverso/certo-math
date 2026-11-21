# Erdős #149 — S602: signed Horn cancellation eliminates the remaining C5 exceptional-budget assumption

**New universal subcase theorem:** Under S591's residual hypotheses, for ANY physical near-tight C5 (five-cycle edge demand W5>=K-ab, K=5/4) with arbitrary feasible positive vertex masses, the old root stars, five cycle edges, and their ENTIRE two-step strong-conflict collar admit an exact palette of width K with root overlap J=min(r_s,r_t)>=D. **No assumption m_i<=1/2 and no C20.2 inequality is needed.**

The theorem is about this specified support. Other H demands remain uncolored. G1 and Erdős #149 are still OPEN.

## A. Setup and geometry from S600

Let delta=ab in (0,1/144), 1/2<x=m_s,y=m_t<3/4, D=r_s+r_t+delta-K>0, and all weighted degree rows feasible after adding the proposed three-edge arc. Suppose H has a physical C5 with vertex masses m_i and cycle demands W5>=K-delta. By S600:
- C5 is induced;
- its vertices are all at physical distance >=3 from both roots;
- every cycle mass lies in (L,U), L=1/2-2delta>35/72 and U=1/2+2delta;
- all C5 edges are compatible with the root edges;
- the first and second strong-conflict collar demand weights W1, W2 satisfy W1<=delta and W2<(37/35)delta.

Let X1 denote exterior vertices adjacent to exactly one C5 vertex; X2 those adjacent to exactly two. There are no vertices adjacent to three or more C5 vertices since 3L>1 and all degree rows are <=1. A second-layer edge is GOOD if compatible with at least one cycle edge and BAD otherwise. Every BAD second-layer edge is either X1-X2 or X2-X2: the union of cycle attachment sets of the endpoints must cover all five cycle edges, whose vertex-cover number is three.

## B. The signed identity and the exact cancellation

Set, for i modulo five,

    alpha_i = (1-2m_i)/4,  gamma_i=m_i+alpha_i=(1+2m_i)/4>0,
    q_i=1-m_(i-1)-m_(i+1)>=0.

Unlike S601, alpha_i may be NEGATIVE when m_i>1/2.

Write p_i for the mass of X1 neighbors of v_i, h_i for the mass of X2 neighbors, and s_i=q_i-p_i-h_i>=0 for the actual row slack. Let C1=sum_i m_i*p_i denote all X1 crossing demand and C2=sum_i m_i*h_i all X2 crossing demand, so W1=C1+C2.

The exact five-cycle Horn identity, valid with alpha of ANY sign, is

    H := K-sum_i m_i+W5 = sum_i alpha_i*q_i
       = sum_i alpha_i*(p_i+h_i+s_i).            (S602.1)

The original Horn row decomposition gives

    K-W5-(C1+C2) = H+sum_i m_i*s_i.              (S602.2)

**DD charge.** For each u∈X2 attached to cycle vertices i,j, its own degree row implies

    d_(H-V(C5))(u) <= 1-m_i-m_j
                   = 2*(alpha_i+alpha_j).

Every BAD DD edge is counted twice in the sum over X2, hence

    Bad_DD <= (1/2)sum_(u∈X2)m_u*d_(H-V(C5))(u)
           <= sum_i alpha_i*h_i.                (S602.3)

This inequality remains valid with signed alpha because it is obtained by summing an inequality for EACH double-contact exterior vertex. It is essential NOT to bound each alpha_i*h_i separately.

Subtract (S602.3) from the available budget AFTER omitting X1 crossing edges:

    K-W5-C2-Bad_DD
      >= sum_i gamma_i*(p_i+s_i).                (S602.4)

Every coefficient gamma_i is strictly POSITIVE. Thus all negative alpha contributions have canceled exactly against the X1 crossing credit and the physical row slack.

**Mixed DS charge.** Put M1=sum_(u∈X1)m_u and M2=sum_(u∈X2)m_u. Every double-contact exterior vertex sees two cycle masses >L, so

    2L M2 <= W1 <= delta, hence M2 <= delta/(2L).

Since delta<1/144 and L>35/72,

    M2 < 1/140 < 71/144 < gamma_i

for every cycle vertex. Therefore all BAD DS edge demand satisfies

    Bad_DS <= M1*M2
           < sum_i gamma_i*p_i.                 (S602.5)

Combining (S602.4) and (S602.5),

    K-W5-C2-Bad_DD-Bad_DS >= sum_i gamma_i*s_i >= 0.

This is a UNIFORM BUDGET INEQUALITY for arbitrary feasible near-tight cycle masses. It disproves the need for the extra C20.2 hypothesis; it does NOT disprove G1.

## C. Exact physical coloring construction

Synchronize the two root stars with the S597 Hall palette: width B=max(r_s,r_t)<3/4 and overlap m=min(r_s,r_t)>=D. Superpose its colors proportionally into the five disjoint C5 singleton colors. The free rootless portion of each cycle color i has width

    f_i=w_i*(W5-B)/W5 > L^2*(1-(3/4)/(K-delta))
       > (72/35)*delta.

All GOOD second-layer edges together have weight <(37/35)delta, and all X1 crossing edges have weight <=W1<=delta. Every GOOD edge is compatible with a cycle singleton by definition; every X1 crossing edge is compatible with its unique opposite cycle edge. Greedily place these edges into root-free subportions of compatible cycle colors; the TOTAL demand of all these inserted edges is <(72/35)delta<every f_i, so the assignment works regardless of mutual conflicts.

Pay all remaining X2 crossing edges and BAD DD/DS second-layer edges separately in singleton colors. By the signed inequality above, this requires at most the remaining K−W5 budget. The entire support receives an exact K-palette with J=m>=D, proving **C22**.

The full graph H may contain other old edges beyond the cycle's two-step conflict collar and the roots. C22 does NOT color them, and these are NOT automatically compatible with the full root/collar palette. This is why G1 universal is NOT closed by this theorem.

## D. Independent rational witness with genuinely signed alpha

The file research/erdos149/test_s602_general_c5.py contains a full physical 21-vertex, 24-edge H with root masses x=y=7/10, a=b=1/20, and cycle masses

    (m0,m1,m2,m3,m4)
       = (5001/10000, 4997/10000, 4998/10000,
          4997/10000, 4997/10000).

In particular m0=0.5001>1/2, so alpha_0<0 and the S601 nonnegative lemma does NOT apply. Both bad DD and bad DS edges have positive demand 1/400000000, and there is a nonzero GOOD annulus edge. All weighted rows and ALL physical strong conflicts are checked.

The signed C22 implementation reconstructs a full exact K-palette of 37 positive classes and J=133/200>D=33/400. Its empty-color remainder is 169981/200000000. The test also checks C21 backward compatibility for balanced cycle masses.

The signed polynomial cancellation is verified by Certo's independent real-arithmetic spec examples/erdos149_s602_signed_horn_budget.py. The graph-theoretic DD/DS counting and the greedy insertion are proved above, not claimed to be encoded in a single symbolic formula.

## E. Remaining single universal gate G1

The S599 necessary slack window Q_H>K−3ab/5 and the S600 separation/clique-prime reduction still do NOT imply existence of a physical C5 with W5>=K−ab. Even when such a cycle exists, the rest of H outside the root and cycle two-step collar may be large and coupled by conflicts. G1 continues to require a global palette/dual argument for these remote demands.

The arc of three edges is therefore **OPEN** in its full generality, and Erdős–Nešetřil #149 remains **OPEN**.
