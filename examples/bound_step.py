"""step: a step between bounds, checked -- the one a user got wrong.

From  D <= B / (1 + B/n)  and  B <= y B1, what follows for D? The bound is
increasing in B, so substituting gives  D <= y B1 / (1 + y B1/n). Writing
y B1 / (1 + B1/n) instead -- the step a user took -- is REFUTED wherever
y < 1 (`conclude` below with that bound comes back with the point). This
spec states the right one; certo proves each rule as a sign on the box:

    d/dB [B / (1 + B/n)] >= 0     the substitution is allowed
    0 <= y B1 <= 10               the substitute stays in B's interval
    conclude - bound >= 0         the conclusion is above what follows

    certo step examples/bound_step.py
    certo verify out/bound_step.json
"""
import z3

from certo import StepSpec


def spec():
    B, y, B1, n = z3.Reals("B y B1 n")
    return StepSpec(
        title="a rational bound, with B <= y B1 substituted",
        box={"B": (0, 10), "y": (0, 1), "B1": (1, 10), "n": (1, 100)},
        bound=B / (1 + B / n),
        substitute=[("B", y * B1)],
        conclude=y * B1 / (1 + y * B1 / n),
    )
