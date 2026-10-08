"""prove --drat: a Boolean Hall argument refuted without a solver.

Five items, two owners with capacity two: every item needs an owner, and no
owner takes more than two -- impossible, by Hall. The incidences are Booleans
and the capacities counts of them (`Sum(If(x, 1, 0)) <= 2`). With `--drat`
the core is encoded by certo (a sequential counter for each count) and
refuted by a DRUP proof; `verify` encodes the core again and checks the
proof by unit propagation. No solver is trusted.

    certo prove examples/hall_drat.py --drat
"""
import z3

from certo import Spec


def spec():
    owners, items = range(2), range(5)
    x = {(i, o): z3.Bool("x_%d_%d" % (i, o)) for i in items for o in owners}
    s = Spec()
    for i in items:
        s.assume("item%d_has_an_owner" % i, z3.Or([x[i, o] for o in owners]))
    for o in owners:
        s.assume("owner%d_takes_at_most_2" % o,
                 z3.Sum([z3.If(x[i, o], 1, 0) for i in items]) <= 2)
    s.claim(z3.BoolVal(False))
    return s
