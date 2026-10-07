"""synth (CEGIS): no implementation exists, and the certificate says why.

Shape of the problem:  THERE EXISTS k in [0, 2]  FOR ALL x in [0, 3] :  x >= k + 2

No k works -- x = 0 needs k <= -2 -- and the search says so after one
counterexample. The NEGATIVE carries a certificate (`cegis_none`): the
implementation's constraints, with the contract instantiated at each
counterexample, are unsatisfiable. Each instance only specialises the
contract, so the refutation is about the whole domain, not the search.

    certo synth examples/synth_none.py
    certo verify out/synth_none.json
"""
import z3

from certo import SynthSpec


def spec():
    k = z3.Int("k")
    x = z3.Int("x")
    return SynthSpec(
        title="k with x >= k + 2 on [0, 3]: none exists",
        impl_vars=[k],
        input_vars=[x],
        helper_vars=[],
        impl_constraints=z3.And(k >= 0, k <= 2),
        behavior=z3.And(x >= 0, x <= 3),
        correctness=(x >= k + 2),
    )
