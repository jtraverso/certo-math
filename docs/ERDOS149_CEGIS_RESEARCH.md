# Erdős #149: Certo / CEGIS, sesion 594 (scope-limited)

This is a **research exercise, not a proof of the open conjecture**.
The user-supplied document, sessions 591–593, reduces a 3-edge arc to
finding a palettisation of measure K=5/4 with reserve J>=D.

**Question here:** Can the exact scalar bound of session 593 (593.degree)
be extended from roots of old degree three to old degree four without any
new physical constraint?

In the symmetric slice x=y, a=b=1/200 and p=q=1-a, with
13/20 <= x <= 7/10, put L=5/4-x and m0=L/(d*x).
The bound asks whether

(1-x)*(p-m0) + x*a*a/m0 <= 1/4.

All denominators d*x*L are positive; the implementation checks the
equivalent numerator

G(d,x) = ((1-x)*(1-a)-1/4)*d*x*L - (1-x)*L**2
         + x*a*a*(d*x)**2.

- `certo synth examples/erdos149_arco3_cegis_degree.py --prove-candidate`
  synthesizes the largest integer d in [1,6] passing the finite instances
  x=13/20, 7/10 and *separately* attempts to prove the chosen d for **all**
  real x in [13/20,7/10]. Distinguish the two certificate statuses.
- `certo prove examples/erdos149_arco3_degree4_counterexample.py`
  finds that d=4 is not established by this bound at x=13/20.

Exact independent test:
x=y=13/20, a=b=1/200, p=q=199/200 yields
D = 1741/40000 >0.
At d=3 the original inequality has margin
-390603/41600000 < 0; at d=4 it has margin
547597/31200000 > 0.

**Mathematical status:** the 3-edge arc universal and Erdos #149 are
OPEN. A positive G only invalidates the *sufficient scalar test*, not
the claim itself. The next needed step is to encode physical graph
incidences and exact palette LP as a domain verifier for CEGIS.


## Physical stress family: why scalar filters alone do not close arc-3

For each rational `0<eps<1/100000`, run `python research/erdos149_s594_stress.py 1/1000000 > H.json` (use a rational smaller than the displayed upper bound). The generator produces a **connected** graph with 400 vertices and 400 edges. It is a tree with eight layered branches attached to heavy roots `x=y=13/20`, plus a remotely attached `C5`. It has articulations, so it is *not* an eligible minimal counterexample.

Set `a=b=1/200` and `c=(1-eps)/2` for the cycle masses. The weighted clique-separator lemma and the bipartite bound imply

`Q_H=5c^2=5(1-eps)^2/4`, which lies strictly between `K-ab` and `K`. Indeed, the 5 cycle edges are pairwise conflicting; the pendant edge can share the cycle color for the opposite edge.

At eps=1/1000000, exact fractions:

- `Q_H=999998000001/800000000000`
- `K-Q_H=1999999/800000000000`
- `D=1741/40000`
- S592 global flow: `2587/2000 > 3/5` (no proof).
- Every S593 directed flow: `2443/4000 > 3/5` (no proof).
- Both root hard-neighbor masses: `199/200` (no proof).
- Old root degree 4 (scalar gate no proof); no A-B cross edges.

Yet in the **full graph F with arc s-u-v-t**, the tree side stays bipartite (its cycle has length 14) and gluing at the articulation again yields `Q_F=5c²<K`. Therefore this is a falsification of the hoped-for SUFFICIENCY of the scalar filters, **not** a falsification of Erdős #149.

The proper next CEGIS search must enforce *2-connectivity / absence of clique separators* in addition to the physical rows, exact reserve LP and the already proved short-arc reduction constraints. Without a universal finite reduction, bounded graph exploration cannot close Erdős #149.
