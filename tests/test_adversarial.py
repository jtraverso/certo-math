"""Feed every verifier certificates the producer never made.

Two certificates shipped in 0.6.0 that `verify` rejects, and 339 tests could
not have caught either. The reason is structural: every test feeds
verification something the producer built, so a contract misread in BOTH
places passes, and both were misread in the same place.

This suite does the opposite. It takes a valid certificate of every kind,
mutates one payload field at a time, and asserts the mutation is caught.

The interesting failure is not a crash. It is a mutation that flips NO check:

    a field nothing looks at is a field the certificate does not really carry

Either the field is decoration and should not be in a payload that claims to
be checkable, or it matters and nothing is checking it. Both are worth
knowing, and neither shows up any other way. Fields that are genuinely
descriptive -- a title, a note -- are listed and excused by name rather than
by a rule, so excusing one is a decision somebody made on purpose.

`python tests/test_adversarial.py`, or with pytest.
"""
from __future__ import annotations
# A test that leaves a question unsettled would otherwise append it to the
# coverage log of whoever runs the suite -- which is how two test runs ended
# up counted as real use in the first reading of one. Callers that chose a
# file keep it.
import os as _os  # noqa: E402
import tempfile as _tempfile  # noqa: E402
_os.environ.setdefault("CERTO_COVERAGE_FILE", _os.path.join(
    _tempfile.mkdtemp(prefix="certo_test_coverage_"), "coverage.jsonl"))

import json
from fractions import Fraction

from certo import Limits, verify
from certo.certificate import Certificate

LIM = Limits(timeout_ms=20_000)

#: The lists and the mutator now live in the PACKAGE, not beside it. A user
#: asked for this battery as a tool, so it became `certo.tamper`; importing it
#: here rather than keeping a second copy is the whole point -- two
#: implementations of one rule is how the rule drifts.
from certo.tamper import DESCRIPTIVE, WEAKENING, mutate as _mutate  # noqa: E402
from certo.tamper import probe as _probe                            # noqa: E402


def probe(cert, skip=()):
    """Mutate each payload field in turn. Returns {field: caught}.

    The suite wants a flat verdict per field; `certo.tamper.probe` reports
    lists so a person can read it. Same run, different shape.
    """
    out = _probe(cert, LIM, skip=skip)
    assert out["original_ok"], "the original must pass"
    return dict([(f, True) for f in out["caught"]]
                + [(f, False) for f in out["uncaught"]])


def _report(kind, results):
    missed = sorted(f for f, caught in results.items() if not caught)
    assert not missed, (
        "{}: mutating {} changed no check. Either the field carries no claim "
        "-- and does not belong in a checkable payload -- or something is not "
        "being checked.".format(kind, ", ".join(missed)))


# ---------------------------------------------------------------------------
# one valid certificate per kind, then every field of it attacked
# ---------------------------------------------------------------------------


def test_unsat_core_and_model():
    import z3

    from certo import Spec
    from certo.engines import smt

    x, y = z3.Reals("x y")
    s = Spec()
    s.assume("x_ge_1", x >= 1)
    s.assume("y_ge_1", y >= 1)
    s.claim(x + y >= 2)
    _report("unsat_core", probe(smt.prove(s, LIM).certificate))

    s2 = Spec()
    s2.assume("pos", x > 0)
    s2.claim(x < 0)
    _report("model", probe(smt.prove(s2, LIM).certificate))


def test_farkas():
    import z3

    from certo import Spec
    from certo.engines import farkas

    x, y = z3.Reals("x y")
    s = Spec()
    s.assume("x_ge_1", x >= 1)
    s.assume("y_ge_1", y >= 1)
    s.claim(x + y >= 2)
    _report("farkas", probe(farkas.farkas(s, LIM).certificate))


def test_lp_dual():
    from certo import LPSpec
    from certo.engines import lp

    s = LPSpec(sense="max")
    s.variable("x")
    s.variable("y")
    s.objective({"x": 1, "y": 1})
    s.constraint({"x": 1, "y": 1}, "<=", 3, name="cap")
    _report("lp_dual", probe(lp.opt(s, LIM).certificate))


def test_mixed_design():
    from certo import LPSpec
    from certo.engines import mixed

    s = LPSpec(sense="max")
    s.variable("a", 0, 1, kind="binary")
    s.variable("w", 0, None)
    s.objective({"a": 3, "w": 1})
    s.constraint({"w": 6}, "<=", 1, name="cap")
    s.constraint({"a": 1}, "<=", 1, name="one")
    _report("mixed_design", probe(mixed.mixed(s, LIM).certificate))


def test_exact_cover():
    import itertools

    from certo import CoverSpec
    from certo.engines import algebra

    fano = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6),
            (4, 5, 0), (5, 6, 1), (6, 0, 2)]
    spec = CoverSpec(universe=list(itertools.combinations(range(7), 2)),
                     parts=fano, cliques=True, max_size=3)
    _report("exact_cover", probe(algebra.cover(spec, LIM).certificate))


def test_resultant():
    import z3

    from certo import EliminateSpec
    from certo.engines import algebra

    s, t = z3.Reals("s t")
    spec = EliminateSpec(variables=["s", "t"],
                         equations=[t ** 3 + s * t + 1, t * t - s],
                         eliminate="t")
    _report("resultant", probe(algebra.eliminate(spec, LIM).certificate))


def test_branch_bound():
    """The kind that was missing from this suite, and had a hole.

    A node's dual used to be a whole nested certificate, checked on its own
    terms -- so a dual for an easy subtree closed a hard one and the tree
    verified. The node's problem is derived from the root system now, and this
    exists so that stays true.
    """
    from certo import LPSpec
    from certo.engines import bb

    W, V = [7, 8, 9, 5, 6, 11, 4, 13], [9, 11, 13, 6, 8, 16, 5, 19]
    lp = LPSpec(sense="max", title="knapsack")
    for i in range(len(W)):
        lp.variable("x%d" % i, 0, 1, kind="integer")
    lp.objective({"x%d" % i: V[i] for i in range(len(W))})
    lp.constraint({"x%d" % i: W[i] for i in range(len(W))}, "<=", 30, name="cap")
    lp.constraint({"x%d" % i: 1 for i in range(len(W))}, "<=", 4, name="count")

    cert = bb.prove_optimal(lp, LIM, max_nodes=20_000).certificate
    assert cert.solver_free is True
    _report("branch_bound", probe(cert))


def test_first_entry():
    from certo import EntrySpec
    from certo.engines import algebra

    got = algebra.entry(EntrySpec(
        values=[Fraction(n, 10) for n in range(8)],
        threshold=Fraction(1, 2), step_bound=Fraction(1, 10)), LIM).certificate
    _report("first_entry", probe(got))


def test_first_moment():
    from certo import MomentSpec
    from certo.engines import algebra

    got = algebra.moment(MomentSpec(
        events=[("a", Fraction(1, 4)), ("b", Fraction(1, 8))],
        counts=True), LIM).certificate
    _report("first_moment", probe(got))

    tails = algebra.moment(MomentSpec(
        tails=[Fraction(1, 2), Fraction(1, 8)], counts=True), LIM).certificate
    _report("first_moment_tails", probe(tails))


def test_ratio_bound():
    from certo.engines import algebra
    from certo.polynomials import Poly
    from certo.spec import RatioSpec

    ring = ("n",)
    n = Poly.var(ring, "n")
    K = lambda c: Poly.const(ring, c)                       # noqa: E731
    got = algebra.ratio(RatioSpec(parameters={"n": 2},
                                  left=(n - K(2), n * n),
                                  right=(K(1), n)), LIM).certificate
    _report("ratio_bound", probe(got))


def test_integer_peak():
    from certo.engines import algebra
    from certo.polynomials import Poly
    from certo.spec import PeakSpec

    ring = ("m", "x")
    m, x = Poly.var(ring, "m"), Poly.var(ring, "x")
    K = lambda c: Poly.const(ring, c)                       # noqa: E731
    spec = PeakSpec(
        parameters={"m": 0}, variable="x",
        objective=x * (m * K(6) + K(1) - x * K(3)) * K(Fraction(1, 2)),
        argmax=Poly.var(("m",), "m"))
    got = algebra.peak(spec, LIM).certificate
    assert got.payload["value"] == {"2": "3/2", "1": "1/2"}
    _report("integer_peak", probe(got))


def test_parametric_bound():
    from certo import ParametricSpec
    from certo.engines import algebra
    from certo.polynomials import Poly

    ring = ("p",)
    P = Poly.var(ring, "p")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731
    spec = ParametricSpec(
        parameters={"p": 10}, sense="max",
        objective={"a": K(1), "b": K(1)},
        constraints=[("big", {"a": K(2), "b": K(1)}, "<=", P * P),
                     ("small", {"b": K(3)}, "<=", P - K(5))],
        dual={"big": Fraction(1, 2), "small": Fraction(1, 3)})
    _report("parametric_bound", probe(algebra.parametric(spec, LIM).certificate))

    # The cover shape, whose dual is a polynomial rather than a rational. Two
    # payload fields exist only here -- `sense` and `dual_poly` -- and the
    # second is a second copy of the first field, which is exactly the kind of
    # thing this suite exists to find unchecked.
    ring = ("p", "s")
    P = Poly.var(ring, "p")
    K = lambda c: Poly.const(ring, c)                       # noqa: E731
    half = P * (P - K(1)) * Poly.const(ring, Fraction(1, 2))
    cover = ParametricSpec(
        parameters={"p": 3, "s": 0}, sense="min",
        objective={"x": half, "y": P * (P - K(1) + Poly.var(ring, "s"))},
        constraints=[("clique", {"x": K(3)}, ">=", K(1)),
                     ("mixed", {"x": K(1), "y": K(2)}, ">=", K(1))],
        dual={"clique": K(0), "mixed": half})
    got = algebra.parametric(cover, LIM).certificate
    assert got.payload["sense"] == "min"
    assert "dual_poly" in got.payload
    _report("parametric_bound_min", probe(got))

    # A declared region. This one is SCOPE: dropping a condition widens what
    # the certificate claims, which is the direction that has to be caught.
    ring = ("q", "k", "r")
    q, k, rr = (Poly.var(ring, v) for v in ring)
    one, two = Poly.const(ring, 1), Poly.const(ring, 2)
    half, third = (Poly.const(ring, Fraction(1, n)) for n in (2, 3))
    d = q + one + k
    cd, cr = d * (d - one) * half, rr * (rr - one) * half
    crossing = d * rr * half - cr
    cols = ["a", "b", "c", "e"]
    shape = [("NNI", [1, 2, 0, 0]), ("NNN", [3, 0, 0, 0]),
             ("NNR", [1, 0, 2, 0]), ("NRR", [0, 0, 2, 1]),
             ("RRR", [0, 0, 0, 3])]
    scoped = ParametricSpec(
        parameters={"q": 1, "k": 0, "r": 4}, sense="min",
        objective={"a": cd, "b": q * d, "c": d * rr, "e": cr},
        constraints=[(n, {cols[i]: Poly.const(ring, row[i])
                          for i in range(4) if row[i]}, ">=", one)
                     for n, row in shape],
        dual={"NNI": q * d * half,
              "NNN": (cd - q * d * half - crossing) * third,
              "NNR": crossing, "NRR": cr, "RRR": Poly.const(ring, 0)},
        region=[("r_within", d + one - rr),
                ("uniform_wins", cd * two + cr * two - q * d - d * rr)])
    got = algebra.parametric(scoped, LIM).certificate
    assert sorted(got.payload["region"]) == ["r_within", "uniform_wins"]
    _report("parametric_bound_region", probe(got))


def test_ideal_and_sos():
    import z3

    from certo import IdealSpec, SOSSpec
    from certo.engines import algebra

    x, y = z3.Reals("x y")
    _report("ideal", probe(algebra.ideal(
        IdealSpec(variables=["x", "y"], equations=[x - 2, x - 3]),
        LIM).certificate))

    try:
        import numpy  # noqa: F401
    except ImportError:
        return
    res = algebra.sos(SOSSpec(variables=["x"], poly=x * x), LIM)
    if res.certificate is not None:
        _report("sos", probe(res.certificate))


def test_number():
    from certo import NumberSpec
    from certo.engines import algebra

    _report("number", probe(algebra.number(
        NumberSpec(n=2 ** 31 - 1, question="prime"), LIM).certificate))


def test_asymptotic():
    import z3

    from certo import OrderSpec
    from certo.engines import order as od

    d, C = z3.Reals("d C")
    spec = OrderSpec(expression=C * C / d, orders={"C": 1, "d": 2})
    _report("asymptotic", probe(od.order(spec, LIM).certificate))


def test_ball():
    from certo import BoundSpec
    from certo.engines import bounds
    from certo.numerics import NoBackend, backend_name

    try:
        backend_name()
    except NoBackend:
        return
    spec = BoundSpec(value=lambda m: m.exp(1) / m.pi, claim=("<", "0.866"))
    _report("ball", probe(bounds.bounds(spec, LIM).certificate))


def test_sweep_and_domain_sweep():
    from certo import DomainSpec, Outcome, SweepSpec
    from certo.engines import domain, graphsearch

    dom = DomainSpec(items=[(a, b) for a in range(4) for b in range(4)],
                     predicate=lambda p: Outcome(p[0] + p[1] >= 0),
                     key=lambda p: "{},{}".format(*p))
    _report("domain_sweep", probe(domain.sweep_domain(dom, LIM).certificate))

    sw = SweepSpec(n=4, predicate=lambda g: True)
    _report("sweep", probe(graphsearch.sweep(sw, LIM).certificate))


def test_drat_and_cnf_model():
    from certo.cnf import CNF, CNFSpec
    from certo.engines import sat

    cnf = CNF(title="unsat")
    a = cnf.var("a")
    cnf.add(a)
    cnf.add(-a)
    _report("drat", probe(sat.cases(CNFSpec(cnf=cnf), LIM).certificate))

    ok = CNF(title="sat")
    b = ok.var("b")
    ok.add(b)
    _report("cnf_model", probe(sat.cases(CNFSpec(cnf=ok), LIM).certificate))


def test_symmetric_inertia():
    """A congruence and its inverse: the counts, the PSD summary and the
    witness are all conclusions, so each has to be recomputed from D and the
    matrix, not agree with itself."""
    from certo.engines import algebra
    from certo.spec import MatrixSpec

    for q, M in (("inertia", [[0, 1, 2], [1, 0, 3], [2, 3, 5]]),
                 ("psd", [["1/2", 1], [1, "1/2"]])):
        cert = algebra.integer_matrix(MatrixSpec(matrix=M, question=q),
                                      LIM).certificate
        _report("symmetric_inertia", probe(cert))


def test_clique_lp():
    """The claim about the columns NOT listed is the pricing search; every
    field it depends on -- the dual, the graph, the weight, the size -- has
    to make the rerun disagree."""
    from certo import CliqueLPSpec
    from certo.engines import algebra

    for problem, weight, m in (("partition", {"constant": 1}, 2),
                               ("packing", {"edges": 1, "constant": -1}, 3)):
        spec = CliqueLPSpec(
            edges=[(0, 1), (1, 2), (0, 2), (0, 3), (1, 3), (1, 4), (2, 4),
                   (0, 5), (2, 5), (3, 4)],
            problem=problem, weight=weight, min_size=m)
        cert = algebra.clique_lp(spec, LIM).certificate
        _report("clique_lp", probe(cert))


def test_affine_semigroup():
    """The kind whose negatives are the expensive half.

    A membership claim is checked by one multiplication. A NON-membership
    claim is checked by redoing the bounded search, so a payload that quietly
    widens the search bound, or drops a generator, or relabels a point, has to
    be caught by that redoing and not by a stored number agreeing with itself.
    """
    from certo import SemigroupSpec
    from certo.engines import algebra

    spec = SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        points={"w": (1, 2), "reachable": (2, 1), "outside": (1, -1)},
        # The proposed set goes in so the generic mutation harness sees the
        # field at all: a payload entry that is None when probed is a field
        # nothing here is testing.
        hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3), "extra": (2, 1)},
        title="not normal, and the witness says so",
    )
    cert = algebra.affine_semigroup(spec, LIM).certificate
    _report("affine_semigroup", probe(cert))


def test_a_semigroup_cannot_claim_a_point_it_never_reaches():
    """The forgery this kind exists to refuse: a witness that is not one."""
    from certo import SemigroupSpec, verify
    from certo.certificate import Certificate
    from certo.engines import algebra

    spec = SemigroupSpec(generators={"e1": (1, 0), "e2": (0, 1)},
                         points={"v": (3, 4)})
    cert = algebra.affine_semigroup(spec, LIM).certificate
    assert verify(cert, LIM).ok

    # (3,4) IS in the semigroup. Claiming it is not -- and that this refutes
    # normality -- is exactly the lie that would discard a live route.
    d = json.loads(json.dumps(cert.to_dict()))
    d["payload"]["points"]["v"]["in_semigroup"] = False
    d["payload"]["points"]["v"]["semigroup_coefficients"] = None
    d["payload"]["points"]["v"]["refutes_normality"] = True
    d["payload"]["not_normal"] = True
    d["payload"]["normality_witnesses"] = ["v"]
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_a_semigroup_certificate_may_never_assert_normality():
    """`normal` is null by construction, and a payload that fills it in is
    refused rather than read."""
    from certo import SemigroupSpec, verify
    from certo.certificate import Certificate
    from certo.engines import algebra

    spec = SemigroupSpec(generators={"e1": (1, 0), "e2": (0, 1)})
    cert = algebra.affine_semigroup(spec, LIM).certificate
    d = json.loads(json.dumps(cert.to_dict()))
    d["payload"]["normal"] = True
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_a_proposed_minimal_generating_set_cannot_be_talked_into_passing():
    """The verdict is recomputed, so flipping it is caught -- and so is
    flipping the per-element answers it is built from."""
    from certo import SemigroupSpec, verify
    from certo.certificate import Certificate
    from certo.engines import algebra

    spec = SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3), "extra": (2, 1)})
    cert = algebra.affine_semigroup(spec, LIM).certificate
    assert verify(cert, LIM).ok
    assert cert.payload["hilbert"]["is_minimal_generating_set"] is False

    for edit in (
        lambda d: d["payload"]["hilbert"].update(
            {"is_minimal_generating_set": True, "why_not": []}),
        lambda d: d["payload"]["hilbert"]["elements"]["extra"].update(
            {"irreducible": True}),
        lambda d: d["payload"]["hilbert"].update({"generates": False}),
    ):
        d = json.loads(json.dumps(cert.to_dict()))
        edit(d)
        assert not verify(Certificate.from_dict(d), LIM).ok


def test_a_hilbert_claim_cannot_be_smuggled_in_by_dropping_an_element():
    """Removing the element that fails leaves a set that really is minimal --
    for a DIFFERENT proposal. The verdict must move with the elements."""
    from certo import SemigroupSpec, verify
    from certo.certificate import Certificate
    from certo.engines import algebra

    spec = SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3), "extra": (2, 1)})
    cert = algebra.affine_semigroup(spec, LIM).certificate
    d = json.loads(json.dumps(cert.to_dict()))
    del d["payload"]["hilbert"]["elements"]["extra"]
    # The remaining three ARE the minimal set, so the recomputed verdict is
    # True while the payload still says False: caught either way round.
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_capacity_profile():
    """A certificate whose subject is a FUNCTION. Every field of it -- a dual
    price, a source mass, a breakpoint, a segment end -- moves the claim, so
    every one has to be caught."""
    import importlib.util
    import pathlib as _p

    from certo.engines import algebra

    path = _p.Path(__file__).resolve().parent.parent / "examples" / "capacity_profile.py"
    spec = importlib.util.spec_from_file_location("_adv_profile", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    cert = algebra.capacity_profile(mod.spec(), LIM).certificate
    # `capacity` is skipped HERE and not excused globally, because the reason
    # is about this instance: the harness mutates the first row alphabetically
    # and in this profile that row is priced ZERO by every dual. Relaxing such
    # a row cannot change the profile -- the bound never mentions it, and
    # loosening a constraint cannot drop an optimum already attained -- so the
    # certificate stays true. Every capacity the duals DO price is caught, and
    # the test below pins that rather than leaving it to this comment.
    _report("capacity_profile", probe(cert, skip={"capacity"}))


def test_a_capacity_the_dual_prices_cannot_be_edited():
    """The other half of the skip above. `02` is priced zero and is inert;
    everything the dual actually pays for moves the profile and is refused."""
    import importlib.util
    import pathlib as _p

    from certo import verify
    from certo.certificate import Certificate
    from certo.engines import algebra

    path = _p.Path(__file__).resolve().parent.parent / "examples" / "capacity_profile.py"
    spec = importlib.util.spec_from_file_location("_adv_profile3", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    base = json.loads(json.dumps(
        algebra.capacity_profile(mod.spec(), LIM).certificate.to_dict()))

    for row in ("23", "45", "13"):
        priced = [s["dual"].get(row, "0") for s in base["payload"]["segments"]]
        assert any(p != "0" for p in priced), row
        d = json.loads(json.dumps(base))
        d["payload"]["capacity"][row] = "2"
        assert not verify(Certificate.from_dict(d), LIM).ok, row


def test_a_profile_cannot_be_widened_by_editing_its_domain():
    """Claiming the same two segments decide a LARGER interval is the forgery
    this kind is most exposed to: the numbers all still check out locally."""
    import importlib.util
    import pathlib as _p

    from certo import verify
    from certo.certificate import Certificate
    from certo.engines import algebra

    path = _p.Path(__file__).resolve().parent.parent / "examples" / "capacity_profile.py"
    spec = importlib.util.spec_from_file_location("_adv_profile2", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    cert = algebra.capacity_profile(mod.spec(), LIM).certificate
    assert verify(cert, LIM).ok

    d = json.loads(json.dumps(cert.to_dict()))
    d["payload"]["domain"]["hi"] = "2"
    assert not verify(Certificate.from_dict(d), LIM).ok


if __name__ == "__main__":
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    fails = 0
    for fn in fns:
        try:
            fn()
            print("[ok] " + fn.__name__)
        except Exception as e:  # noqa: BLE001
            fails += 1
            print("[XX] {}: {}".format(fn.__name__, e))
    print("\n{}/{} passed".format(len(fns) - fails, len(fns)))
    raise SystemExit(1 if fails else 0)
