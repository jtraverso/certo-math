"""induct: a TRUE statement that is not inductive, and the strengthening found.

    a(0) = 0,  a(k+1) = a(k) + 1
    b(0) = 0,  b(k+1) = b(k) + a(k)          claim: b(k) >= 0 for every k

b(k) >= 0 alone does not carry over: the step's hypothesis admits a state with
b(k) = 0 and a(k) = -5, which no run reaches, and from there b(k+1) < 0. The
repair is to prove something stronger. `StrengthenSpec` searches a template
Q_c(k) = c0 a(k) + c1 >= 0 by CEGIS over the integer coefficients -- each
failed candidate leaves a point (an index and the values there) the next one
must respect -- finds a(k) >= 0, and proves b(k) >= 0 AND a(k) >= 0 by
`induct`. The certificate records the strengthening; `verify` re-checks every
case and that what was proved implies b(k) >= 0.

The recurrences are the theorem's hypotheses (`facts`, `initial`): the step
is linked with them as premises, and every verification says so.

    certo induct examples/induct_strengthen.py --cert out/strengthen.json
    certo verify out/strengthen.json
"""
import z3

from certo import StrengthenSpec

k = z3.Int("k")
a = z3.Function("a", z3.IntSort(), z3.IntSort())
b = z3.Function("b", z3.IntSort(), z3.IntSort())


def spec():
    return StrengthenSpec(
        title="b(k) >= 0, where b sums a and a counts",
        k=k, k0=0, base_upto=1,
        prop=lambda k: b(k) >= 0,
        facts=lambda k: [a(k + 1) == a(k) + 1, b(k + 1) == b(k) + a(k)],
        initial=[a(0) == 0, b(0) == 0],
        template=lambda c, k: c[0] * a(k) + c[1] >= 0,
        coefficients=2, bounds=(-3, 3),
    )
