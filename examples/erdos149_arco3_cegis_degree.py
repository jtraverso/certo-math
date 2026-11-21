"""Erdos #149, session 594: CEGIS for the *scalar* degree gate of arc-3.

This does NOT prove the universal arc-3 recoloring lemma.  The previous
necessary inequality (session 593) leads to a sufficient scalar degree test.
Here Certo finds the largest d surviving TWO rational training regimes,
then --prove-candidate checks the chosen d on a whole real interval.

Run:
  certo lint examples/erdos149_arco3_cegis_degree.py
  certo synth examples/erdos149_arco3_cegis_degree.py --prove-candidate --trace
  certo verify out/erdos149_arco3_cegis_degree.json
"""
import z3

from certo import Spec, SynthSpec


K = z3.RealVal("5/4")
A = z3.RealVal("1/200")


def gap_numerator(d, x):
    """Positive-denominator clearing of the session-593 degree criterion.

    m0 = (K-x)/(d*x); p=1-a; x=y; a=b=A.
    The criterion succeeds exactly when gap_numerator(d,x) <= 0.
    Valid only when d>0, x>0, K-x>0.
    """
    L = K - x
    dx = d * x
    return ((1 - x) * (1 - A) - z3.RealVal("1/4")) * dx * L - (1 - x) * L * L + x * A * A * dx * dx


def universal(values):
    x = z3.Real("x_universal")
    d = z3.IntVal(int(values["d"]))
    s = Spec(title="Arc-3 scalar gate for all x=y in [13/20,7/10], a=b=1/200")
    s.assume("x_lower", x >= z3.RealVal("13/20"))
    s.assume("x_upper", x <= z3.RealVal("7/10"))
    s.claim(gap_numerator(d, x) <= 0)
    s.role("consumer")
    s.pending("arc3", "Scalar criterion only; the actual universal palette and all other graphs remain OPEN")
    return s


def spec():
    d, t = z3.Ints("d t")
    x = z3.ToReal(t) / 20
    return SynthSpec(
        title="Erdos149: largest d certified by the session-593 scalar test",
        impl_vars=[d],
        input_vars=[t],
        impl_constraints=z3.And(d >= 1, d <= 6),
        behavior=z3.And(t >= 13, t <= 14),
        correctness=gap_numerator(d, x) <= 0,
        minimize=-d,
        universal=universal,
    )
