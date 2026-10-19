"""synth for `construction_split.json`: how many releases must a host give?

    find the least integer r in [0, 5] such that for every load x in [0, 1]:
        3 r >= 5 + x

CEGIS answers r = 2 -- a NUMBER. Whether two releases exist is a different
question, about bases and spokes, and the construction answers it in another
step: its `cegis` contract checks that r is backed by the placements the
`hosting` step certified. A scalar that pays is not yet a resource that does.

    certo synth examples/construction_releases.py --cert out/construction_releases.json
"""
import z3

from certo import SynthSpec


def spec():
    r, x = z3.Ints("r x")
    return SynthSpec(
        title="the least number of releases that pays every load",
        impl_vars=[r],
        input_vars=[x],
        impl_constraints=z3.And(r >= 0, r <= 5),
        behavior=z3.And(x >= 0, x <= 1),
        correctness={"pays": 3 * r >= 5 + x},
        minimize=r,
    )
