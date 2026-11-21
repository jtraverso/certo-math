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
