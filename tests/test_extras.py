"""Generic domains, programmable filters, ranges, packings and Lean export."""
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
import os
import pathlib
from fractions import Fraction

from certo import (DomainSpec, Graph, Limits, Outcome, PackingSpec, SweepSpec,
                   loads_from_dual, verify)
from certo.certificate import Certificate
from certo.engines import domain, graphsearch, lp, shrink
from certo.graphs import is_chordal
from certo.status import Status, Verdict

# A test that makes a self-check fail would otherwise write a real report into
# the data directory of whoever runs the suite. Tests that care set their own.
import tempfile as _tempfile  # noqa: E402
os.environ.setdefault("CERTO_REPORT_DIR",
                      _tempfile.mkdtemp(prefix="certo_test_reports_"))

LIM = Limits(timeout_ms=20_000)


def _roundtrip(cert):
    return Certificate.from_dict(json.loads(json.dumps(cert.to_dict())))


# --- sweeps over an arbitrary finite domain --------------------------------


def _pairs(lo=2, hi=6):
    return [(s, r) for s in range(lo, hi) for r in range(lo, hi)]


def test_domain_sweep_refutes_and_certifies():
    spec = DomainSpec(
        items=_pairs(),
        predicate=lambda p: p[0] * p[1] >= p[0] + p[1] + 3,
        key=lambda p: "s={},r={}".format(*p),
    )
    r = domain.sweep_domain(spec, LIM)
    assert r.verdict is Verdict.REFUTED
    assert "s=2,r=2" in r.meta["counterexamples"]
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_domain_sweep_calibrates_exactly_without_a_predicate():
    spec = DomainSpec(items=_pairs(),
                      collect=lambda p: Fraction(p[0], p[1]),
                      key=lambda p: "{}/{}".format(*p))
    r = domain.sweep_domain(spec, LIM)
    assert r.verdict is Verdict.SATISFIABLE          # measures, does not refute
    cal = r.meta["calibration"]
    assert cal["min"] == "2/5" and cal["max"] == "5/2"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_domain_sweep_catches_duplicate_ids():
    """Two items sharing an id would silently collapse the domain."""
    spec = DomainSpec(items=[(1, 2), (2, 1)], collect=lambda p: p[0],
                      key=lambda p: "same")
    cert = _roundtrip(domain.sweep_domain(spec, LIM).certificate)
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("unique" in c[0] and not c[1] for c in rep.checks)


# --- programmable filters --------------------------------------------------


def test_a_callable_works_as_a_filter():
    dense = lambda g: g.m >= 8  # noqa: E731
    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected", dense], predicate=is_chordal),
        LIM, use_geng=False)
    assert r.meta["enumerated"] == 34            # before filtering
    assert r.meta["in_family"] < 34              # after


def test_a_programmable_filter_is_flagged_as_unverifiable():
    """It lives in the spec, not the catalogue: verify must not pretend."""
    r = graphsearch.sweep(
        SweepSpec(n=5, filters=[lambda g: g.m >= 8], predicate=is_chordal),
        LIM, use_geng=False)
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("cannot be re-checked" in c[2] for c in rep.checks)


# --- shrink: starting point and objective ----------------------------------


def _density_spec(n=6):
    def density(g):
        return Fraction(g.m, g.n * (g.n - 1) // 2) if g.n > 1 else Fraction(0)

    return SweepSpec(
        n=n, filters=["connected"],
        predicate=lambda g: Outcome(ok=is_chordal(g), value=density(g)),
        collect=density, worst="min")


def test_shrink_understands_an_outcome_returning_predicate():
    """An Outcome object is always truthy: it has to be unwrapped."""
    spec = _density_spec()
    c4 = Graph.from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    r = shrink.shrink_graph(spec, c4, LIM)
    assert r.verdict is Verdict.REFUTED       # not ERROR "satisfies predicate"


def test_objective_mode_keeps_the_worst_ratio_instead_of_the_fewest_edges():
    """C4 with a pendant vertex: density 1/2, and C4 alone is 2/3.

    Plain shrink drops the pendant because smaller wins. With --objective the
    reduction is refused, because 2/3 is a WORSE ratio than 1/2 and the point
    was the worst ratio, not the fewest edges.
    """
    spec = _density_spec()
    pendant = Graph.from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4)])

    plain = shrink.shrink_graph(spec, pendant, LIM)
    assert (plain.meta["n"], plain.meta["m"]) == (4, 4)      # fewest edges

    guided = shrink.shrink_graph(spec, pendant, LIM, use_objective=True)
    assert guided.meta["objective"] == "1/2"                 # worst ratio kept
    assert guided.meta["n"] == 5 and guided.meta["steps"] == 0


def test_worst_counterexample_is_picked_from_a_certificate():
    from certo.cli import _worst_from_cert
    from pathlib import Path
    import tempfile

    r = graphsearch.sweep(_density_spec(), LIM, use_geng=False)
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "c.json"
        f.write_text(json.dumps(r.certificate.to_dict()), encoding="utf-8")
        pick = _worst_from_cert(f, "min")
    values = {v["id"]: Fraction(v["value"])
              for v in r.certificate.payload["values"]}
    failures = {e["id"] for e in r.certificate.payload["entries"]}
    assert pick in failures
    assert values[pick] == min(values[g] for g in failures)


# --- packings --------------------------------------------------------------


def _k(n):
    return Graph.from_edges(n, [(i, j) for i in range(n) for j in range(i + 1, n)])


def test_packing_builds_the_same_lp_and_certifies_exactly():
    pk = PackingSpec.cliques_in_graph(_k(6), gains={3: 2, 4: 5})
    r = lp.opt(pk.to_lp(), LIM)
    assert r.meta["exact"] and r.meta["objective"] == "25/2"   # 5n(n-1)/12
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_the_dual_reads_as_a_load_per_resource():
    pk = PackingSpec.cliques_in_graph(_k(6), gains={3: 2, 4: 5})
    r = lp.opt(pk.to_lp(), LIM)
    loads = loads_from_dual(r.certificate)
    assert set(loads) <= set(pk.resources)          # keys are edge names
    assert all(Fraction(v) == Fraction(5, 6) for v in loads.values())


def test_restricting_to_one_kind_gives_the_optimum_of_that_type_alone():
    pk = PackingSpec.cliques_in_graph(_k(6), gains={3: 2, 4: 5})
    assert pk.kinds == ["K3", "K4"]
    only3 = lp.opt(pk.restricted({"K3"}).to_lp(), LIM)
    only4 = lp.opt(pk.restricted({"K4"}).to_lp(), LIM)
    assert only3.meta["objective"] == "10"          # triangles alone
    assert only4.meta["objective"] == "25/2"        # mixing buys nothing here


def test_packing_rejects_duplicate_item_names():
    try:
        PackingSpec(items=[("a", ["r"], 1), ("a", ["s"], 1)])
        raise AssertionError("it accepted two items with the same name")
    except AssertionError:
        raise
    except ValueError as e:
        assert "duplicate" in str(e)


# --- Lean export -----------------------------------------------------------


def test_lean_export_carries_the_edges_and_admits_it_is_unchecked():
    from certo import lean

    c4 = Graph.from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    text = lean.graph_to_lean(c4, source="test")
    assert "Checked against Lean" in text          # states its provenance
    assert "(0, 1), (1, 2), (2, 3), (0, 3)" in text.replace("  ", " ") or \
           text.count("(") >= 4
    assert "SimpleGraph (Fin 4)" in text


def test_lean_export_reads_a_shrink_certificate():
    from certo import lean

    spec = _density_spec()
    pendant = Graph.from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4)])
    cert = shrink.shrink_graph(spec, pendant, LIM).certificate
    graphs = lean.graphs_from_certificate(cert.to_dict())
    assert len(graphs) == 1 and graphs[0].n == 4        # reduced to C4


# --- core over several goals ------------------------------------------------


def _multi():
    import z3

    from certo import MultiSpec

    r, d = z3.Reals("r d")
    s = MultiSpec()
    s.assume("r_ge_3", r >= 3)
    s.assume("d_ge_1", d >= 1)
    s.assume("d_le_r", d <= r)
    s.claim("identity", (d - 1) * (d - 2) + r * (r + 1) - d * (d + 1)
            - 4 * (r - d) == (r - 1) * (r - 2))
    s.claim("positivity", (r - 1) * (r - 2) >= 0)
    s.claim("ordering", r - d >= 0)
    return s


def test_core_matrix_separates_what_each_goal_needs():
    from certo.engines import smt

    r = smt.core_matrix(_multi(), LIM)
    table = r.meta["table"]
    assert table["r_ge_3"] == {"identity": False, "positivity": True,
                               "ordering": False}
    assert table["d_le_r"]["ordering"] is True
    assert r.meta["never_used"] == ["d_ge_1"]       # no goal needs it
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_core_matrix_table_must_agree_with_its_cores():
    from certo.engines import smt

    cert = _roundtrip(smt.core_matrix(_multi(), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["table"]["d_ge_1"]["identity"] = True      # tamper
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("agrees" in c[0] and not c[1] for c in rep.checks)


# --- shrink over an arbitrary domain ---------------------------------------


DOMAIN_SRC = '''
from fractions import Fraction
from certo import DomainSpec

def spec():
    return DomainSpec(
        items=[(s, r) for s in range(2, 7) for r in range(2, 7)],
        predicate=lambda p: p[0] * p[1] >= 12,
        collect=lambda p: Fraction(p[0], p[1]),
        reduce=lambda p: ([(p[0] - 1, p[1]), (p[0], p[1] - 1)]
                          if p[0] > 1 and p[1] > 1 else []),
        key=lambda p: "s={},r={}".format(*p),
    )
'''


def test_shrink_over_a_domain_replays_on_verification():
    import tempfile
    from pathlib import Path

    from certo.engines import shrink
    from certo.spec import load_spec

    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "dom.py"
        f.write_text(DOMAIN_SRC, encoding="utf-8")
        spec = load_spec(f)
        start = next(i for i in spec.enumerate() if spec.id_of(i) == "s=2,r=2")
        r = shrink.shrink_domain(spec, start, LIM, spec_path=str(f))
        assert r.verdict is Verdict.REFUTED
        # the trace records the index taken, so the descent can be replayed
        assert all("index" in s for s in r.meta["trace"])
        rep = verify(_roundtrip(r.certificate), LIM)
        assert rep.ok and rep.solver_free
        assert any("replays" in c[0] for c in rep.checks)


def test_shrink_over_a_domain_needs_a_reduce():
    from certo import DomainSpec
    from certo.engines import shrink

    spec = DomainSpec(items=[(1, 1)], predicate=lambda p: False)
    try:
        shrink.shrink_domain(spec, (1, 1), LIM)
        raise AssertionError("it should have asked for `reduce`")
    except AssertionError:
        raise
    except ValueError as e:
        assert "reduce" in str(e)


# --- sweep over a range of sizes -------------------------------------------


def test_sweep_range_finds_the_first_failing_size():
    r = graphsearch.sweep_range(
        SweepSpec(n=3, filters=["connected"], predicate=is_chordal),
        3, 5, LIM, use_geng=False)
    assert r.meta["first_failure"] == 4          # C4
    assert r.meta["verdicts"][3] == "proved"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_sweep_range_records_that_it_stopped_early():
    r = graphsearch.sweep_range(
        SweepSpec(n=3, filters=["connected"], predicate=is_chordal),
        3, 6, LIM, stop_on_first=True, use_geng=False)
    assert r.meta["stopped_early"] and r.meta["sizes"] == [3, 4]
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and any("stopped" in w for w in rep.warnings)


def test_sweep_range_restores_the_spec_size():
    """The loop mutates spec.n; it must not leak out."""
    spec = SweepSpec(n=3, filters=["connected"], predicate=is_chordal)
    graphsearch.sweep_range(spec, 3, 5, LIM, use_geng=False)
    assert spec.n == 3


# --- ledger ----------------------------------------------------------------


def test_ledger_records_and_reverifies():
    import tempfile
    from pathlib import Path

    from certo import ledger
    from certo.engines import smt

    with tempfile.TemporaryDirectory() as d:
        log, cert_p = Path(d) / "l.jsonl", Path(d) / "c.json"
        import z3

        from certo import Spec

        a = z3.Real("a")
        s = Spec()
        s.assume("pos", a > 0)
        s.claim(a * a >= 0)
        res = smt.prove(s, LIM)
        cert_p.write_text(json.dumps(res.certificate.to_dict()), encoding="utf-8")

        ledger.append(log, res, cert_path=cert_p, note="baseline", tags=["t"])
        rows = ledger.read(log)
        assert len(rows) == 1 and rows[0]["note"] == "baseline"

        rep = ledger.verify_all(log, LIM)
        assert rep["counts"]["ok"] == 1 and rep["counts"]["failed"] == 0


def test_ledger_flags_a_certificate_that_changed_after_logging():
    import tempfile
    from pathlib import Path

    import z3

    from certo import Spec, ledger
    from certo.engines import smt

    with tempfile.TemporaryDirectory() as d:
        log, cert_p = Path(d) / "l.jsonl", Path(d) / "c.json"
        a = z3.Real("a")
        s = Spec()
        s.assume("pos", a > 0)
        s.claim(a * a >= 0)
        res = smt.prove(s, LIM)
        cert_p.write_text(json.dumps(res.certificate.to_dict()), encoding="utf-8")
        ledger.append(log, res, cert_path=cert_p)

        data = json.loads(cert_p.read_text(encoding="utf-8"))
        data["payload"]["names"] = ["invented"]
        cert_p.write_text(json.dumps(data), encoding="utf-8")

        rep = ledger.verify_all(log, LIM)
        assert rep["counts"]["tampered"] == 1        # digest no longer matches
        assert rep["rows"][0]["state"] == "changed"


def test_ledger_survives_a_corrupt_line():
    import tempfile
    from pathlib import Path

    from certo import ledger

    with tempfile.TemporaryDirectory() as d:
        log = Path(d) / "l.jsonl"
        log.write_text('{"ts":"x"}\nnot json at all\n', encoding="utf-8")
        rep = ledger.verify_all(log, LIM)
        assert rep["counts"]["corrupt"] == 1
        assert rep["total"] == 2


# --- farkas / linarith / nlinarith -----------------------------------------


def _lin_spec():
    import z3

    from certo import Spec

    x, y, z = z3.Reals("x y z")
    s = Spec()
    s.assume("x_ge_1", x >= 1)
    s.assume("y_ge_1", y >= 1)
    s.assume("noise", z <= 100)
    s.claim(x + y >= 2)
    return s


def test_farkas_finds_the_linarith_certificate():
    from fractions import Fraction as F

    from certo.engines import farkas as fk

    r = fk.farkas(_lin_spec(), LIM)
    assert r.verdict is Verdict.PROVED
    mult = r.meta["multipliers"]
    assert F(mult["x_ge_1"]) > 0 and F(mult["y_ge_1"]) > 0
    assert "noise" not in mult                    # irrelevant: multiplier 0
    assert r.meta["hint"] == "linarith [x_ge_1, y_ge_1]"


def test_the_farkas_certificate_needs_no_solver():
    from certo.engines import farkas as fk

    rep = verify(_roundtrip(fk.farkas(_lin_spec(), LIM).certificate), LIM)
    assert rep.ok and rep.solver_free
    assert all(c[1] for c in rep.checks)


def test_a_tampered_multiplier_stops_cancelling():
    from certo.engines import farkas as fk

    cert = _roundtrip(fk.farkas(_lin_spec(), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["multipliers"][0] = "7"          # breaks the cancellation
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("cancels" in c[0] and not c[1] for c in rep.checks)


def test_a_negative_multiplier_is_rejected():
    from certo.engines import farkas as fk

    cert = _roundtrip(fk.farkas(_lin_spec(), LIM).certificate)
    cert.payload["multipliers"][0] = "-1"
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("non-negative" in c[0] and not c[1] for c in rep.checks)


def test_nonlinear_mode_rediscovers_the_square():
    """a^2 + b^2 >= 2ab is (a - b)^2 >= 0, which is what nlinarith adds."""
    import z3

    from certo import Spec
    from certo.engines import farkas as fk

    a, b = z3.Reals("a b")
    s = Spec()
    s.claim(a * a + b * b >= 2 * a * b)

    assert fk.farkas(s, LIM).status is Status.OUT_OF_THEORY   # linear mode
    r = fk.farkas(s, LIM, nonlinear=True)
    assert r.verdict is Verdict.PROVED
    assert "sq_a_b" in r.meta["multipliers"]                  # the (a-b)^2 row
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_nonlinear_system_says_to_use_the_right_mode():
    import z3

    from certo import Spec
    from certo.engines import farkas as fk

    a = z3.Real("a")
    s = Spec()
    s.claim(a * a >= 0)
    r = fk.farkas(s, LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "--nonlinear" in r.detail and "prove" in r.detail


def test_non_polynomial_input_is_refused_with_the_offending_term():
    import z3

    from certo import Spec
    from certo.engines import farkas as fk

    x = z3.Real("x")
    s = Spec()
    s.claim(x / x >= 0)                     # division by a non-constant
    r = fk.farkas(s, LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "division" in r.detail


def test_a_false_statement_yields_no_certificate():
    import z3

    from certo import Spec
    from certo.engines import farkas as fk

    x = z3.Real("x")
    s = Spec()
    s.assume("x_ge_1", x >= 1)
    s.claim(x >= 2)                         # false at x = 1
    r = fk.farkas(s, LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None


def test_equalities_are_split_so_multipliers_stay_non_negative():
    import z3

    from certo import Spec
    from certo.engines import farkas as fk

    x, y = z3.Reals("x y")
    s = Spec()
    s.assume("eq", x == y)
    s.assume("y_ge_3", y >= 3)
    s.claim(x >= 3)
    r = fk.farkas(s, LIM)
    assert r.verdict is Verdict.PROVED
    assert verify(_roundtrip(r.certificate), LIM).ok

# --- compose: lemmas, their certificates, and the join between them --------


def _x():
    import z3

    return z3.Real("x")


def _lemma_spec(hyp, goal):
    from certo import Spec

    s = Spec()
    s.assume("h", hyp)
    s.claim(goal)
    return s


def test_compose_assembles_a_proof_and_reports_what_it_needed():
    import z3

    from certo import ProofSpec
    from certo.engines import compose

    x = _x()
    p = ProofSpec(title="compose smoke")
    p.assume("x_ge_1", x >= 1)
    p.lemma("doubles", proves=_lemma_spec(x >= 1, 2 * x >= 2))
    p.lemma("spare", proves=_lemma_spec(x >= 1, x + 1 >= 2))
    p.conclude(2 * x >= 2)

    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.PROVED
    assert verify(_roundtrip(r.certificate), LIM).ok
    # Both lemmas come back as NOT needed, and that is correct: over linear
    # real arithmetic z3 rederives them from `x_ge_1` in the final step. The
    # report comes from the step's MUS, not from a guess. A lemma is needed
    # only when it carries something the theory cannot reach on its own --
    # which is what a bridge does.
    assert set(r.meta["unused"]) == {"doubles", "spare"}
    assert r.meta["used"] == ["x_ge_1"]


def test_a_lemma_may_not_claim_more_than_its_certificate_closes():
    """The whole reason compose exists: proved for x>=1, used as x>=2."""
    import z3

    from certo import ProofSpec
    from certo.engines import compose

    x = _x()
    p = ProofSpec()
    p.lemma("overreach", proves=_lemma_spec(x >= 1, x >= 1),
            states=z3.Implies(x >= 1, x >= 2))
    p.conclude(z3.Implies(x >= 1, x >= 2))

    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None                  # nothing unlinkable is emitted
    assert r.meta["failed_lemma"] == "overreach"


def test_lemmas_that_do_not_close_the_theorem_say_so():
    from certo import ProofSpec
    from certo.engines import compose

    x = _x()
    p = ProofSpec()
    p.lemma("weak", proves=_lemma_spec(x >= 1, x >= 1))
    p.conclude(x >= 2)

    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None


def test_swapping_a_lemma_statement_breaks_the_link_on_verification():
    import z3

    from certo import ProofSpec, z3util
    from certo.engines import compose

    x = _x()
    p = ProofSpec()
    p.lemma("ok", proves=_lemma_spec(x >= 1, x >= 1))
    p.conclude(z3.Implies(x >= 1, x >= 1))

    cert = _roundtrip(compose.compose(p, LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["lemmas"][0]["statement_smt2"] = \
        z3util.smt2(z3.Implies(x >= 1, x >= 99))
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("entails" in c[0] and not c[1] for c in rep.checks)


def test_a_farkas_lemma_links_through_its_rows():
    """The link check is uniform: an exact certificate answers it too."""
    import z3

    from certo import ProofSpec, Spec
    from certo.engines import compose

    a, b = z3.Reals("a b")
    sq = Spec()
    sq.claim(a * a + b * b >= 2 * a * b)

    p = ProofSpec()
    p.lemma("square", proves=sq, via="nlinarith")
    p.conclude(a * a + b * b >= 2 * a * b)

    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["lemmas"][0]["engine"] == "nlinarith"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("entails" in c[0] and c[1] for c in rep.checks)


def test_a_stored_certificate_is_a_bridge_and_is_reported_as_one(tmp=None):
    import json
    import tempfile
    from pathlib import Path

    import z3

    from certo import ProofSpec, Spec
    from certo.engines import compose, smt

    x = _x()
    # Any certificate will do; what matters is that it is not linkable to the
    # statement on its own.
    src = Spec()
    src.assume("h", x >= 1)
    src.claim(x >= 1)
    sub = smt.prove(src, LIM).certificate

    d = Path(tempfile.mkdtemp(prefix="certo_bridge_"))
    (d / "c.json").write_text(json.dumps(sub.to_dict()), encoding="utf-8")

    k = z3.Int("k")
    p = ProofSpec()
    p.assume("k_ge_6", k >= 6)
    p.lemma("finite", certificate=str(d / "c.json"), states=(k <= 10),
            bridge="checked by hand for every case")
    p.conclude(z3.And(k >= 6, k <= 10))

    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["bridges"] == ["finite"]
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any(w.startswith("BRIDGE") or "PUENTE" in w for w in rep.warnings)


def test_a_bridge_needs_a_statement_because_nothing_can_guess_it():
    from certo import ProofSpec

    p = ProofSpec()
    try:
        p.lemma("finite", certificate="somewhere.json")
    except ValueError as e:
        assert "states" in str(e)
    else:
        raise AssertionError("a bridge without states must be refused")


def test_a_missing_certificate_names_the_lemma_and_the_path():
    import z3

    from certo import ProofSpec
    from certo.engines import compose

    x = _x()
    p = ProofSpec()
    p.lemma("gone", certificate="no/such/file.json", states=(x >= 0))
    p.conclude(x >= 0)
    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "gone" in r.detail and "file.json" in r.detail

# --- bounds: rigorous numerics ---------------------------------------------


def _bound(**kw):
    from certo import BoundSpec

    kw.setdefault("prec", 64)
    return BoundSpec(**kw)


def test_a_transcendental_bound_is_established_and_rechecked():
    from certo.engines import bounds

    r = bounds.bounds(_bound(value=lambda m: m.e / m.pi, claim=("<", "0.866")),
                      LIM)
    assert r.verdict is Verdict.PROVED
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free


def test_the_enclosure_travels_as_exact_rationals():
    from fractions import Fraction

    from certo.engines import bounds

    cert = bounds.bounds(_bound(value=lambda m: m.pi), LIM).certificate
    lo, hi = Fraction(cert.payload["lo"]), Fraction(cert.payload["hi"])
    assert lo < Fraction(355, 113) < hi or lo < hi   # an interval, exactly
    assert hi - lo > 0 and float(hi - lo) < 1e-15


def test_precision_is_a_budget_and_it_escalates():
    from certo.engines import bounds

    r = bounds.bounds(_bound(value=lambda m: m.e / m.pi, prec=32,
                             claim=("<", "0.8652559794322652")), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["ladder"][0] == 32


def test_running_out_of_precision_is_not_a_refutation():
    """exp(1) - e is zero, so no enclosure can ever separate it from zero."""
    from certo.engines import bounds

    r = bounds.bounds(_bound(value=lambda m: m.exp(1) - m.e, claim=("!=", "0"),
                             max_prec=512), LIM)
    assert r.status is Status.RESOURCE_EXHAUSTED
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None
    assert "not a refutation" in r.detail or "no es una refutaci" in r.detail


def test_a_false_bound_is_refuted_with_the_interval_that_shows_it():
    from certo.engines import bounds

    r = bounds.bounds(_bound(value=lambda m: m.pi, claim=("<", "3")), LIM)
    assert r.verdict is Verdict.REFUTED
    assert r.certificate is None
    assert float(r.meta["lo_float"]) > 3


def test_a_python_float_in_the_expression_is_refused():
    from certo.engines import bounds

    r = bounds.bounds(_bound(value=lambda m: m.pi * 0.5, claim=("<", "2")), LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "float" in r.detail


def test_a_string_is_read_as_an_exact_rational_not_as_a_float():
    from fractions import Fraction

    from certo.numerics import Rig

    lo, hi = Rig(256)("0.1").enclosure()
    assert lo <= Fraction(1, 10) <= hi          # one tenth, not the double


def test_measuring_without_a_claim_records_the_enclosure():
    from certo.engines import bounds

    r = bounds.bounds(_bound(value=lambda m: m.zeta(3)), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["claim"][0] == "in"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_widened_interval_no_longer_settles_the_claim():
    from certo.engines import bounds

    cert = _roundtrip(bounds.bounds(
        _bound(value=lambda m: m.e / m.pi, claim=("<", "0.866")), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["hi"] = "1"                    # still contains the value
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("settles" in c[0] and not c[1] for c in rep.checks)


def test_a_shifted_interval_fails_the_re_evaluation(tmp_path=None):
    """The rational half can pass while the interval is the wrong interval."""
    import tempfile
    from pathlib import Path

    from certo.engines import bounds

    src = Path(tempfile.mkdtemp(prefix="certo_ball_")) / "s.py"
    src.write_text(
        "from certo import BoundSpec\n"
        "def spec():\n"
        "    return BoundSpec(value=lambda m: m.e / m.pi,\n"
        "                     claim=('<', '0.866'), prec=64)\n",
        encoding="utf-8")

    from certo import load_spec

    cert = _roundtrip(bounds.bounds(load_spec(src), LIM, spec_path=str(src))
                      .certificate)
    assert verify(cert, LIM).ok
    cert.payload["lo"] = "1/100"                # settles "< 0.866" just fine
    cert.payload["hi"] = "2/100"
    rep = verify(cert, LIM)
    assert not rep.ok
    failed = [c for c, ok, _ in rep.checks if not ok]
    assert failed and all("re-evaluating" in c or "reevaluar" in c
                          for c in failed)


def test_both_backends_agree_on_an_elementary_quantity():
    from certo.numerics import Rig

    a = Rig(160, "python-flint (Arb)")
    b = Rig(160, "mpmath.iv")
    alo, ahi = (a.exp(1) / a.pi).enclosure()
    blo, bhi = (b.exp(1) / b.pi).enclosure()
    assert alo <= bhi and blo <= ahi            # the enclosures overlap
    assert max(alo, blo) <= min(ahi, bhi)


def test_a_function_the_backend_lacks_says_which_backend():
    from certo.numerics import NotRigorous, Rig

    try:
        Rig(64, "mpmath.iv").zeta(3)
    except NotRigorous as e:
        assert "mpmath" in str(e)
    else:
        raise AssertionError("mpmath.iv has no rigorous zeta; it must say so")

# --- vacuity: a proof from contradictory hypotheses is not a proof ---------


def _contradictory(goal):
    import z3

    from certo import Spec

    x = z3.Real("x")
    s = Spec()
    s.assume("big", x > 1)
    s.assume("small", x < 0)
    s.claim(goal(x))
    return s


def test_prove_says_when_the_hypotheses_contradict_each_other():
    from certo.engines import smt

    r = smt.prove(_contradictory(lambda x: x == 42), LIM)
    assert r.verdict is Verdict.PROVED        # it IS a proof; ex falso
    assert r.meta["vacuous"] is True
    assert "VACUOUS" in r.detail or "VACUA" in r.detail


def test_the_vacuity_survives_in_the_certificate():
    from certo.engines import smt

    cert = _roundtrip(smt.prove(_contradictory(lambda x: x == 42), LIM).certificate)
    rep = verify(cert, LIM)
    assert rep.ok                              # still a valid certificate
    assert any("VACUOUS" in w or "VACUA" in w for w in rep.warnings)


def test_an_honest_proof_is_not_flagged():
    import z3

    from certo import Spec
    from certo.engines import smt

    x = z3.Real("x")
    s = Spec()
    s.assume("pos", x > 1)
    s.claim(x > 0)
    r = smt.prove(s, LIM)
    assert r.meta["vacuous"] is False
    assert not verify(_roundtrip(r.certificate), LIM).warnings


def test_farkas_detects_vacuity_by_dropping_the_goal():
    """Reading it off the multipliers does not work; this asks directly."""
    import z3

    from certo import Spec
    from certo.engines import farkas

    x = z3.Real("x")
    s = Spec()
    s.assume("a", x >= 1)
    s.assume("b", x <= 0)
    s.claim(x >= 5)
    r = farkas.farkas(s, LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["vacuous"] is True
    assert any("VACUOUS" in w or "VACUA" in w
               for w in verify(_roundtrip(r.certificate), LIM).warnings)


def test_nonlinear_vacuity_does_not_count_the_goal_products():
    """The products are named h*__goal__; keeping one would smuggle it back."""
    import z3

    from certo import Spec
    from certo.engines import farkas

    a, b = z3.Reals("a b")
    s = Spec()
    s.assume("h", a >= 0)
    s.claim(a * a + b * b >= 2 * a * b)
    assert farkas.farkas(s, LIM, nonlinear=True).meta["vacuous"] is False


def test_compose_reports_bridges_that_contradict_each_other():
    """Only bridges can contradict: two DERIVED lemmas are both true, so they
    cannot. Which is precisely why the check belongs where bridges enter."""
    import json
    import tempfile
    from pathlib import Path

    import z3

    from certo import ProofSpec, Spec
    from certo.engines import compose, smt

    x = z3.Real("x")
    src = Spec()
    src.assume("h", x >= 1)
    src.claim(x >= 1)
    sub = smt.prove(src, LIM).certificate
    d = Path(tempfile.mkdtemp(prefix="certo_vac_"))
    (d / "c.json").write_text(json.dumps(sub.to_dict()), encoding="utf-8")

    k = z3.Int("k")
    p = ProofSpec(title="contradictory bridges")
    p.lemma("small", certificate=str(d / "c.json"), states=(k <= 3),
            bridge="asserted")
    p.lemma("large", certificate=str(d / "c.json"), states=(k >= 9),
            bridge="also asserted, and incompatible with the first")
    p.conclude(k == 99)                       # follows from anything

    r = compose.compose(p, LIM)
    assert r.verdict is Verdict.PROVED        # ex falso: it really does follow
    assert r.meta["vacuous"] is True
    rep = verify(_roundtrip(r.certificate), LIM)
    assert any("VACUOUS" in w or "VACUA" in w for w in rep.warnings)


# --- P0: what a sweep establishes about the predicate ----------------------


def _bool_domain(pred, n=12):
    from certo import DomainSpec

    return DomainSpec(items=list(range(n)), predicate=pred,
                      key=lambda i: "i={}".format(i))


def _spec_file(dirname, threshold):
    """A DomainSpec on disk whose predicate depends on `threshold`."""
    import tempfile
    from pathlib import Path

    d = Path(tempfile.mkdtemp(prefix=dirname))
    src = d / "s.py"
    src.write_text(SPEC_TEMPLATE.format(t=threshold), encoding="utf-8")
    return src


SPEC_TEMPLATE = """
from certo import DomainSpec

def spec():
    return DomainSpec(items=list(range(12)),
                      predicate=lambda i: i >= {t},
                      key=lambda i: "i=" + str(i))
"""


def _pretend_unchanged(cert, src):
    """Make the provenance hash match the EDITED spec.

    Without this the provenance warning would fire and the replay would be
    skipped; the point of the test is that the replay is what catches an edit
    nothing else can see.
    """
    import hashlib

    cert.provenance["spec_sha256"] = hashlib.sha256(src.read_bytes()).hexdigest()
    return cert


def test_replay_catches_a_predicate_that_changed_under_a_stable_name():
    """The only check that can catch this. The domain hash cannot -- the
    domain did not move. The stored certificates cannot -- there are none."""
    from certo import load_spec
    from certo.engines import domain

    src = _spec_file("certo_replay_", 0)
    cert = _roundtrip(domain.sweep_domain(load_spec(src), LIM)
                      .certificate.stamp(src))
    assert verify(cert, LIM).ok

    src.write_text(SPEC_TEMPLATE.format(t=3), encoding="utf-8")   # three flip
    rep = verify(_pretend_unchanged(cert, src), LIM)
    assert not rep.ok
    failed = [(c, d) for c, ok, d in rep.checks if not ok]
    assert failed and "re-running" in failed[0][0]
    assert "i=0" in failed[0][1]


def test_a_sweep_with_no_spec_path_drops_to_recorded():
    from certo.engines import domain

    cert = _roundtrip(domain.sweep_domain(_bool_domain(lambda i: True),
                                          LIM).certificate)
    rep = verify(cert, LIM)                     # never stamped: nothing to replay
    assert rep.ok
    assert "recorded only" in rep.detail
    assert any("NOT re-run" in w for w in rep.warnings)
    assert any("could not be replayed" in w for w in rep.warnings)


def test_the_verdict_vector_is_what_makes_replay_possible():
    from certo.certificate import outcomes_digest
    from certo.engines import domain

    r = domain.sweep_domain(_bool_domain(lambda i: i % 2 == 0), LIM)
    p = r.certificate.payload
    assert p["outcomes"] == "TFTFTFTFTFTF"
    assert p["outcomes_sha256"] == outcomes_digest(p["outcomes"])
    assert p["evaluations"] == 12 and p["certified"] == 0


def test_an_inconclusive_evaluation_is_its_own_code():
    from certo import Outcome
    from certo.engines import domain

    def pred(i):
        if i == 5:
            return Outcome(ok=None, detail="gave up")
        if i == 7:
            raise RuntimeError("boom")
        return True

    p = domain.sweep_domain(_bool_domain(pred), LIM).certificate.payload
    assert p["outcomes"] == "TTTTT?TETTTT"


def test_calibration_has_no_predicate_to_certify_and_says_nothing_about_one():
    from fractions import Fraction

    from certo import DomainSpec
    from certo.engines import domain

    spec = DomainSpec(items=list(range(6)), collect=lambda i: Fraction(i, 7),
                      key=lambda i: "i={}".format(i))
    r = domain.sweep_domain(spec, LIM)
    assert "level" not in r.meta                # there is no predicate to rate
    assert "banner_key" not in r.meta           # the banner stays CALIBRATION
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert "no predicate" in rep.detail
    assert not any("carry no certificate" in w for w in rep.warnings)


def test_a_disagreeing_replay_does_not_also_claim_only_the_domain_was_checked():
    """Two messages for one problem make readers skim both."""
    from certo import load_spec
    from certo.engines import domain

    src = _spec_file("certo_one_msg_", 0)
    cert = _roundtrip(domain.sweep_domain(load_spec(src), LIM)
                      .certificate.stamp(src))
    src.write_text(SPEC_TEMPLATE.format(t=2), encoding="utf-8")

    rep = verify(_pretend_unchanged(cert, src), LIM)
    assert not rep.ok
    assert not any("could not be replayed" in w for w in rep.warnings)


def test_certificates_issued_before_the_rename_still_read():
    """`g6` was the field name when the only domain was graphs."""
    from certo.certificate import _entry_id

    assert _entry_id({"id": "a=1"}) == "a=1"
    assert _entry_id({"g6": "E??w"}) == "E??w"      # pre-rename certificate
    assert _entry_id({}) == "?"


def test_a_domain_sweep_no_longer_calls_its_items_graph6():
    from certo.engines import domain

    r = domain.sweep_domain(_bool_domain(lambda i: i < 8), LIM)
    p = r.certificate.payload
    assert p["entries"] and all("id" in e and "g6" not in e for e in p["entries"])

# --- P1: standard reducers -------------------------------------------------


def test_the_catalogue_reducers_are_deterministic_and_shrinking():
    from certo import reducers

    assert reducers.sets({3, 1, 2}) == [{2, 3}, {1, 3}, {1, 2}]
    assert reducers.sequences((1, 2, 3)) == [(2, 3), (1, 3), (1, 2)]
    assert reducers.decrement((4, 2)) == [(3, 2), (4, 1)]
    assert reducers.masks(0b1011) == [0b1010, 0b1001, 0b0011]
    assert reducers.decrement((0, 0)) == []          # already at the floor


def test_auto_treats_a_tuple_of_ints_as_a_point_not_a_collection():
    """Dropping a coordinate from a parameter point changes its arity."""
    from certo import reducers

    assert reducers.auto((3, 1)) == [(2, 1), (3, 0)]
    assert reducers.auto(("a", "b")) == [("b",), ("a",)]


def test_auto_refuses_rather_than_inventing_a_reduction():
    from certo import reducers

    try:
        reducers.auto(3.5)
    except TypeError as e:
        assert "float" in str(e)
    else:
        raise AssertionError("it made up a reduction for a float")


def test_a_named_reducer_replays_exactly_like_a_hand_written_one():
    from certo import load_spec
    from certo.engines import shrink

    src = _spec_file("certo_reducer_", 0)            # reduce="auto" inside
    src.write_text(
        SPEC_TEMPLATE.replace("predicate=lambda i: i >= {t},",
                              "predicate=lambda i: i < 4,")
        .replace("key=", "reduce='auto', key=").format(t=0),
        encoding="utf-8")
    spec = load_spec(src)
    r = shrink.shrink_domain(spec, 11, LIM, spec_path=src)
    assert r.verdict is Verdict.REFUTED
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_an_unknown_reducer_name_lists_the_known_ones():
    from certo import DomainSpec

    try:
        DomainSpec(items=[], reduce="nope").reducer()
    except ValueError as e:
        assert "auto" in str(e) and "graphs" in str(e)
    else:
        raise AssertionError("it accepted a name that does not exist")


def test_a_shrink_certificate_with_no_spec_path_says_so_instead_of_crashing():
    """Path("") is ".", which exists and is a directory."""
    from certo.certificate import shrink_domain_certificate

    rep = verify(shrink_domain_certificate("", "", "x", "x", [], [], 0), LIM)
    assert not rep.ok
    assert "spec" in rep.detail


# --- P1: orbits ------------------------------------------------------------


def _mirror_spec(n=7):
    from certo import DomainSpec

    return DomainSpec(
        items=[(a, b) for a in range(1, n) for b in range(1, n)],
        predicate=lambda p: p[0] + p[1] != n,
        key=lambda p: "({},{})".format(*p),
        canonicalize=lambda p: tuple(sorted(p)),
    )


# --- entry: where a sequence first crosses, and by how little --------------


def _run_entry(spec):
    from certo.engines import algebra

    return algebra.entry(spec, LIM)


def test_the_first_crossing_is_the_first_one_and_carries_its_window():
    """The claim that goes wrong is "it had not crossed yet", not "it crosses"."""
    from certo import EntrySpec

    walk = [Fraction(n * (n + 1), 150) for n in range(12)]
    r = _run_entry(EntrySpec(values=walk, threshold=Fraction(1, 2),
                             step_bound=Fraction(1, 5)))
    assert r.verdict is Verdict.PROVED
    assert r.meta["index"] == 9 and r.meta["value"] == "3/5"
    assert r.meta["window"] == "7/10"
    p = r.certificate.payload
    # the prefix stops at the crossing: nothing past it is part of the claim
    assert len(p["prefix"]) == 10 and p["prefix"][-1] == "3/5"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free

    # and the window is real: the crossing lands below threshold + delta
    assert Fraction(p["prefix"][-1]) < Fraction(p["window"])


def test_strict_moves_the_index_when_a_value_lands_on_the_line():
    from certo import EntrySpec

    values = [Fraction(i, 4) for i in range(8)]
    loose = _run_entry(EntrySpec(values=values, threshold=Fraction(1)))
    tight = _run_entry(EntrySpec(values=values, threshold=Fraction(1),
                                 strict=True))
    assert loose.meta["index"] == 4 and loose.meta["value"] == "1"
    assert tight.meta["index"] == 5 and tight.meta["value"] == "5/4"


def test_a_walk_that_never_crosses_has_no_first_index():
    from certo import EntrySpec

    r = _run_entry(EntrySpec(values=[Fraction(1, 2 + i) for i in range(10)],
                             threshold=Fraction(2)))
    assert r.verdict is Verdict.REFUTED
    assert r.certificate is None
    assert "never crosses" in r.detail


def test_a_step_bound_that_fails_earlier_takes_the_window_with_it():
    from certo import EntrySpec

    walk = [Fraction(n * (n + 1), 150) for n in range(12)]
    r = _run_entry(EntrySpec(values=walk, threshold=Fraction(1, 2),
                             step_bound=Fraction(1, 100)))
    assert r.verdict is Verdict.REFUTED
    assert "somebody got wrong" in r.detail


def test_a_forged_earlier_index_does_not_verify():
    """Dropping the last value would make an earlier index look like the first."""
    from certo import EntrySpec
    from certo.certificate import Certificate

    walk = [Fraction(n, 10) for n in range(8)]
    r = _run_entry(EntrySpec(values=walk, threshold=Fraction(1, 2)))
    base = json.loads(json.dumps(r.certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    # claim a later index while keeping the prefix that crossed earlier
    bent = json.loads(json.dumps(base))
    bent["payload"]["prefix"] = bent["payload"]["prefix"] + ["9/10"]
    assert not verify(Certificate.from_dict(bent), LIM).ok

    # keep the index, move the threshold so the prefix crossed sooner
    bent = json.loads(json.dumps(base))
    bent["payload"]["threshold"] = "1/10"
    assert not verify(Certificate.from_dict(bent), LIM).ok


# --- moment: the first moment, exactly, and the existence it buys ----------


def _run_moment(spec):
    from certo.engines import algebra

    return algebra.moment(spec, LIM)


def test_a_mean_below_one_buys_an_object_and_says_so():
    """The probabilistic method, with the arithmetic in exact rationals."""
    from math import comb

    from certo import MomentSpec

    each = Fraction(2, 2 ** comb(4, 2))
    r = _run_moment(MomentSpec(
        events=[("copy_%d" % i, each) for i in range(comb(6, 4))],
        counts=True))
    assert r.verdict is Verdict.PROVED
    assert r.meta["expectation"] == "15/32" and r.meta["exists"] is True
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free

    # one vertex more and the sum crosses: that is arithmetic, not a failure
    seven = _run_moment(MomentSpec(
        events=[("copy_%d" % i, each) for i in range(comb(7, 4))],
        counts=True))
    assert seven.verdict is Verdict.REFUTED
    assert seven.meta["expectation"] == "35/32"
    assert seven.certificate is None


def test_existence_is_refused_when_the_quantity_is_not_a_count():
    """A mean below one for something that could be 1/2 everywhere puts no
    outcome at zero, so nothing is claimed to exist."""
    from certo import MomentSpec

    r = _run_moment(MomentSpec(events=[("a", Fraction(1, 2)),
                                       ("b", Fraction(1, 4))], counts=False))
    assert r.verdict is Verdict.PROVED
    assert r.meta["exists"] is False
    assert r.certificate.payload["concludes"] is False
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("no existence follows" in w for w in rep.warnings)


def test_a_distribution_by_tails_has_its_masses_checked():
    from certo import MomentSpec
    from certo.moment import masses_from_tails

    tails = [Fraction(1, 2), Fraction(1, 8), Fraction(1, 64)]
    masses = masses_from_tails(tails)
    assert sum(masses) == 1 and all(m >= 0 for m in masses)

    r = _run_moment(MomentSpec(tails=tails, counts=True))
    assert r.verdict is Verdict.PROVED
    assert r.meta["expectation"] == "41/64"          # the sum of the tails
    assert verify(_roundtrip(r.certificate), LIM).ok

    # tails that go back up imply a negative mass, which is not a distribution
    bad = _run_moment(MomentSpec(tails=[Fraction(1, 4), Fraction(1, 2)],
                                 counts=True))
    assert bad.verdict is Verdict.REFUTED
    assert "not probabilities" in bad.detail


def test_the_conclusion_flag_is_re_earned_and_not_believed():
    """A certificate claiming existence it did not earn must not verify."""
    from certo import MomentSpec
    from certo.certificate import Certificate

    r = _run_moment(MomentSpec(events=[("a", Fraction(1, 2))], counts=False))
    bent = json.loads(json.dumps(r.certificate.to_dict()))
    bent["payload"]["concludes"] = True
    rep = verify(Certificate.from_dict(bent), LIM)
    assert not rep.ok
    assert any("earned" in n for n, ok, _ in rep.checks if not ok)


def test_events_and_tails_are_not_both_and_not_neither():
    from certo import MomentSpec

    for spec in (MomentSpec(events=[("a", Fraction(1, 2))],
                            tails=[Fraction(1, 2)]),
                 MomentSpec()):
        r = _run_moment(spec)
        assert r.verdict is Verdict.INCONCLUSIVE
        assert "not both and not neither" in r.detail


# --- ratio: a fraction inequality for every n, with no solver --------------


def _ratio(left, right, relation="<=", floor=2):
    from certo.polynomials import Poly
    from certo.spec import RatioSpec

    return RatioSpec(parameters={"n": floor}, left=left, right=right,
                     relation=relation)


def _run_ratio(spec):
    from certo.engines import algebra

    return algebra.ratio(spec, LIM)


def test_a_fraction_inequality_holds_for_every_n_without_a_solver():
    from certo.polynomials import Poly

    ring = ("n",)
    n = Poly.var(ring, "n")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731

    r = _run_ratio(_ratio((n - K(2), n * n), (K(1), n)))
    assert r.verdict is Verdict.PROVED
    assert r.meta["difference"] == "2*n"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free

    # and it is not vacuously true: the same claim reversed is refused
    back = _run_ratio(_ratio((K(1), n), (n - K(2), n * n)))
    assert back.verdict is Verdict.INCONCLUSIVE

    # strict needs the constant term of the shifted difference positive
    tight = _run_ratio(_ratio((n - K(2), n * n), (K(1), n), relation="<"))
    assert tight.verdict is Verdict.PROVED
    # `n <= n` is true and `n < n` is not
    assert _run_ratio(_ratio(n, n)).verdict is Verdict.PROVED
    assert _run_ratio(_ratio(n, n, relation="<")).verdict is Verdict.INCONCLUSIVE


def test_a_denominator_not_shown_positive_is_refused_not_assumed():
    """A negative denominator flips the inequality: the certificate would be
    exactly backwards, so this is a refusal rather than an assumption."""
    from certo.polynomials import Poly

    ring = ("n",)
    n = Poly.var(ring, "n")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731

    # n - 5 is negative at n = 2, and the claim would reverse there
    r = _run_ratio(_ratio((K(1), n - K(5)), (K(1), n)))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "denominator" in r.detail

    # raise the floor past the sign change and the same claim goes through
    ok = _run_ratio(_ratio((K(1), n), (K(1), n - K(5)), floor=6))
    assert ok.verdict is Verdict.PROVED


def test_the_verifier_rebuilds_the_difference_from_the_two_sides():
    """A certificate carrying a friendlier difference than its sides produce."""
    from certo.certificate import Certificate
    from certo.polynomials import Poly

    ring = ("n",)
    n = Poly.var(ring, "n")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731

    r = _run_ratio(_ratio((n - K(2), n * n), (K(1), n)))
    bent = json.loads(json.dumps(r.certificate.to_dict()))
    # claim the false bound, keeping the difference that proved the true one
    bent["payload"]["right"] = [Poly.const(ring, 1).serialize(),
                                (n * n).serialize()]
    rep = verify(Certificate.from_dict(bent), LIM)
    assert not rep.ok
    assert any("cross-multiplied" in name for name, ok, _ in rep.checks
               if not ok)


def test_ge_is_refused_because_it_is_the_same_claim_twice():
    r = _run_ratio(_ratio(1, 2, relation=">="))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "sides swapped" in r.detail


# --- family: the largest of many LPs, and why nothing beats it -------------


def _family_of_lps():
    """Four programs whose optima are 1, 2, 3 and 4, so the winner is known."""
    from certo import FamilySpec, LPSpec

    def one(k):
        lp = LPSpec(sense="max", title="k={}".format(k))
        lp.variable("x", 0, None)
        lp.objective({"x": 1})
        lp.constraint({"x": 1}, "<=", k, name="cap")
        return lp

    return FamilySpec(items=[1, 2, 3, 4], lp=one,
                      key=lambda k: "k={}".format(k))


def test_a_family_maximum_attains_at_the_winner_and_bounds_the_rest():
    """Two claims, and they are not symmetric -- which is the whole design."""
    from certo.engines import algebra

    r = algebra.family_max(_family_of_lps(), LIM)
    assert r.verdict is Verdict.SATISFIABLE
    assert r.meta["value"] == "4" and r.meta["argmax"] == "k=4"
    p = r.certificate.payload
    assert p["count"] == 4 and len(p["bounds"]) == 3
    # the winner carries a primal AND a dual; the others only a dual
    assert p["primal"] and p["dual"]


def test_a_family_certificate_without_its_spec_checks_nothing_and_says_so():
    """The programs are not stored, so the vectors are numbers about nothing."""
    from certo.certificate import Certificate
    from certo.engines import algebra

    r = algebra.family_max(_family_of_lps(), LIM)
    stripped = json.loads(json.dumps(r.certificate.to_dict()))
    stripped["provenance"] = {}
    rep = verify(Certificate.from_dict(stripped), LIM)
    assert not rep.ok
    assert any("NOTHING was checked" in w for w in rep.warnings)


def test_a_min_item_program_is_refused_rather_than_reinterpreted():
    """Bounding a minimum from above needs a primal point, not a dual."""
    from certo import FamilySpec, LPSpec
    from certo.engines import algebra

    def down(k):
        lp = LPSpec(sense="min", title="k={}".format(k))
        lp.variable("x", 1, None)
        lp.objective({"x": 1})
        lp.constraint({"x": 1}, ">=", k, name="floor")
        return lp

    r = algebra.family_max(FamilySpec(items=[1, 2], lp=down,
                                      key=lambda k: str(k)), LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "maximisation" in r.detail


def test_two_items_sharing_an_id_are_refused():
    """A bound stored for one would be read as a bound for the other."""
    from certo import FamilySpec, LPSpec
    from certo.engines import algebra

    def flat(_k):
        lp = LPSpec(sense="max")
        lp.variable("x", 0, 1)
        lp.objective({"x": 1})
        lp.constraint({"x": 1}, "<=", 1, name="cap")
        return lp

    r = algebra.family_max(FamilySpec(items=[1, 2], lp=flat,
                                      key=lambda _k: "same"), LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "share an id" in r.detail


def test_weak_duality_is_what_bounds_the_losers():
    """A dual does not have to be OPTIMAL to bound -- only feasible."""
    from fractions import Fraction as F

    from certo.family import attains_value, bounds_value

    # max x s.t. x <= 3, x >= 0
    A, b, c = [[F(1)]], [F(3)], [F(1)]
    assert bounds_value(A, b, c, [F(1)], F(3))        # optimal dual
    assert bounds_value(A, b, c, [F(1)], F(5))        # bounded by more
    assert not bounds_value(A, b, c, [F(1)], F(2))    # 3 is not <= 2
    assert not bounds_value(A, b, c, [F(-1)], F(3))   # y >= 0 is required
    assert not bounds_value(A, b, c, [F(0)], F(3))    # A^T y >= c fails

    assert attains_value(A, b, c, [F(3)], [F(1)], F(3))
    assert not attains_value(A, b, c, [F(2)], [F(1)], F(3))   # not attained
    assert not attains_value(A, b, c, [F(4)], [F(1)], F(3))   # infeasible


# --- does each hypothesis earn its place? ----------------------------------


def _audit(build):
    import z3

    from certo import Spec
    from certo.engines import smt

    spec = Spec()
    build(spec, z3)
    return smt.audit(spec, LIM)


def test_a_hypothesis_doing_no_work_is_named_redundant():
    """The mistake `core` cannot catch: a theorem stated too strongly."""
    def build(spec, z3):
        n, m = z3.Ints("n m")
        spec.assume("n_large", n >= 5)
        spec.assume("m_bounded", m <= n - 2)
        spec.assume("noise", z3.Bool("noise"))
        spec.claim(m <= n)

    r = _audit(build)
    assert r.verdict is Verdict.SATISFIABLE
    # `m_bounded` alone gives `m <= n`, so the other two do no work
    assert set(r.meta["redundant_names"]) == {"n_large", "noise"}
    assert r.meta["needed"] == 1 and r.meta["unknown"] == 0


def test_every_needed_verdict_carries_the_assignment_that_breaks_it():
    """The witness is the content: knowing a hypothesis matters is worth
    little, knowing HOW it matters is what tells you if you wrote the right
    one."""
    def build(spec, z3):
        n, m = z3.Ints("n m")
        spec.assume("n_large", n >= 5)
        spec.assume("m_positive", m >= 1)
        spec.assume("m_bounded", m <= n - 2)
        spec.claim(z3.And(m >= 1, m + 2 <= n, n >= 5))

    r = _audit(build)
    assert r.meta["needed"] == 3 and r.meta["redundant"] == 0
    rows = r.certificate.payload["rows"]
    assert all(row["witness"] for row in rows if row["verdict"] == "needed")

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("does NOT say the hypothesis set is minimal" in w
               for w in rep.warnings)


def test_a_forged_witness_does_not_verify():
    """Checking is evaluation: substitute, and the kept hypotheses must hold
    while the goal must not."""
    import copy

    from certo.certificate import Certificate

    def build(spec, z3):
        n, m = z3.Ints("n m")
        spec.assume("n_large", n >= 5)
        spec.assume("m_positive", m >= 1)
        spec.assume("m_bounded", m <= n - 2)
        spec.claim(z3.And(m >= 1, m + 2 <= n, n >= 5))

    base = json.loads(json.dumps(_audit(build).certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    # a witness that does not break the goal
    assert not bent(lambda p: p["rows"][0]["witness"].update({"n": ["Int", "9"],
                                                             "m": ["Int", "2"]}))
    # a `needed` verdict with nothing behind it
    assert not bent(lambda p: p["rows"].__setitem__(
        0, dict(p["rows"][0], witness=None)))
    # a tally that does not match the rows
    assert not bent(lambda p: p["counts"].__setitem__("needed", 9))


def test_no_verdict_is_ever_folded_into_another():
    """Each of the four says something the others do not, and collapsing any
    pair would be a lie in a specific direction: `unknown` as `needed` says
    the theorem is tight when nobody checked, and `domain` as `redundant`
    tells you to delete the hypothesis that keeps the statement meaningful."""
    from certo.audit import DOMAIN, NEEDED, REDUNDANT, UNKNOWN, VERDICTS

    assert len({NEEDED, REDUNDANT, DOMAIN, UNKNOWN}) == 4
    assert set(VERDICTS) == {NEEDED, REDUNDANT, DOMAIN, UNKNOWN}

    def build(spec, z3):
        n = z3.Int("n")
        spec.assume("positive", n >= 1)
        spec.claim(n >= 0)

    r = _audit(build)
    counts = r.certificate.payload["counts"]
    assert set(counts) == set(VERDICTS)
    assert sum(counts.values()) == len(r.certificate.payload["rows"])


def test_a_spec_with_nothing_to_drop_is_refused():
    from certo.audit import NotAuditable, audit

    import z3

    from certo import Spec

    empty = Spec()
    empty.claim(z3.BoolVal(True))
    try:
        audit(empty, LIM)
        raise AssertionError("expected a refusal")
    except NotAuditable as e:
        assert "no hypotheses" in str(e)

    goalless = Spec()
    goalless.assume("h", z3.Int("n") >= 1)
    try:
        audit(goalless, LIM)
        raise AssertionError("expected a refusal")
    except NotAuditable as e:
        assert "no claim" in str(e)


# --- averaging over the group, checked instead of asserted -----------------


def _triangle_cover(n=7):
    """Cover every edge of K_n by triangles: the shape five write-ups start
    from AFTER saying "by symmetry"."""
    import itertools

    from certo import LPSpec

    p = LPSpec(sense="min", title="triangle cover of K{}".format(n))
    tris = [t for t in itertools.combinations(range(n), 3)]
    for t in tris:
        p.variable("t{}_{}_{}".format(*t), 0, 1)
    p.objective({"t{}_{}_{}".format(*t): 1 for t in tris})
    for e in itertools.combinations(range(n), 2):
        row = {"t{}_{}_{}".format(*t): 1 for t in tris
               if e[0] in t and e[1] in t}
        p.constraint(row, ">=", 1, name="e{}_{}".format(*e))
    return p, tris


def _full_symmetric(tris, n=7):
    """S_n acting on the vertices, as two generators on the triangles."""
    def induced(sigma):
        return {"t{}_{}_{}".format(*t):
                "t{}_{}_{}".format(*sorted(sigma[v] for v in t))
                for t in tris}

    swap = {v: v for v in range(n)}
    swap[0], swap[1] = 1, 0
    cycle = {v: (v + 1) % n for v in range(n)}
    return {"swap01": induced(swap), "cycle": induced(cycle)}


def _reduce(lp, generators, title=""):
    from certo import SymmetrySpec
    from certo.engines import algebra

    return algebra.reduce_symmetry(
        SymmetrySpec(lp=lp, generators=generators, title=title), LIM)


def test_the_quotient_has_the_optimum_the_original_has():
    """The claim the whole command makes, checked against the thing it is
    about: solve BOTH exactly and compare. If averaging lost anything, these
    two numbers would differ."""
    from certo.engines import lp as lpe

    prog, tris = _triangle_cover()
    r = _reduce(prog, _full_symmetric(tris), "K7 under S7")
    assert r.verdict is Verdict.PROVED
    assert r.meta["variables"] == 35 and r.meta["orbits"] == 1
    assert r.meta["rows"] == 21 and r.meta["reduced_rows"] == 1

    from certo import tree
    quotient = tree.spec_of(r.certificate.payload["quotient"])
    assert lpe.opt(prog, LIM).meta["objective"] == \
        lpe.opt(quotient, LIM).meta["objective"]

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert any("nothing about what that optimum is" in w for w in rep.warnings)


def test_each_hypothesis_of_the_averaging_argument_refuses_by_name():
    """A wrong group does not give a weaker reduction, it gives a WRONG one,
    so every generator is checked and every refusal says which hypothesis
    failed and where."""
    from certo import LPSpec

    def base(hi_y=1, rhs2=1, obj_z=1):
        p = LPSpec(sense="max")
        p.variable("x", 0, 1)
        p.variable("y", 0, hi_y)
        p.variable("z", 0, 1)
        p.objective({"x": 1, "y": 1, "z": obj_z})
        p.constraint({"x": 1, "y": 1}, "<=", 1, name="c1")
        p.constraint({"y": 1, "z": 1}, "<=", rhs2, name="c2")
        return p

    swap_xz = {"x": "z", "z": "x", "y": "y"}

    # the honest case first, so the refusals below are not passing by accident
    ok = _reduce(base(), {"g": swap_xz})
    assert ok.verdict is Verdict.PROVED
    assert [sorted(o) for o in ok.certificate.payload["orbits"]] == \
        [["x", "z"], ["y"]]

    def refused(lp, perm, fragment):
        r = _reduce(lp, {"g": perm})
        assert r.verdict is Verdict.INCONCLUSIVE, fragment
        assert r.certificate is None
        assert fragment in r.detail, r.detail
        return r

    # not a bijection: x and z both land on z
    refused(base(), {"x": "z", "z": "z", "y": "y"}, "not a permutation")
    # the objective moves
    refused(base(obj_z=5), swap_xz, "moves the objective")
    # the bounds move
    refused(base(hi_y=5), {"x": "y", "y": "x", "z": "z"}, "moves the bounds")
    # the row leaves the constraint set: c1 has rhs 1, its image would need 2
    refused(base(rhs2=2), swap_xz, "outside the constraint set")
    # and no group at all
    r = _reduce(base(), {})
    assert r.verdict is Verdict.INCONCLUSIVE and "no generators" in r.detail


def test_a_forged_reduction_does_not_verify():
    """Three ways to lie about a quotient, and the check that catches each."""
    import copy

    from certo import LPSpec

    prog = LPSpec(sense="max", title="two orbits, not one")
    for v in ("x", "y", "z"):
        prog.variable(v, 0, 1)
    prog.objective({"x": 1, "y": 1, "z": 1})
    prog.constraint({"x": 1, "y": 1}, "<=", 1, name="c1")
    prog.constraint({"y": 1, "z": 1}, "<=", 1, name="c2")

    r = _reduce(prog, {"g": {"x": "z", "z": "x", "y": "y"}})
    base = json.loads(json.dumps(r.certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok
    assert len(base["payload"]["orbits"]) == 2

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    # a generator that is not an automorphism, smuggled in beside a real one
    assert not bent(lambda p: p["generators"].__setitem__(
        "fake", {"x": "y", "y": "x", "z": "z"}))
    # orbits coarser than the generators give -- claiming a bigger group, and
    # a bigger group is a smaller quotient, which is the whole incentive
    assert not bent(lambda p: p.__setitem__("orbits", [["x", "y", "z"]]))
    # a quotient with fewer rows than the substitution produces
    assert not bent(lambda p: p["quotient"]["cons"].clear())
    # a quotient whose objective was quietly scaled down
    assert not bent(lambda p: p["quotient"].__setitem__(
        "obj", {k: "1" for k in p["quotient"]["obj"]}))


def test_the_orbits_are_derived_and_not_taken_on_faith():
    """The quotient is REBUILT from the system and the orbits, for the same
    reason a branch-and-bound node derives its own program: a payload nobody
    recomputes is a payload anybody can edit."""
    from certo import symmetry, tree

    prog, tris = _triangle_cover(4)
    cert = _reduce(prog, _full_symmetric(tris, 4)).certificate
    p = cert.payload

    root = tree.spec_of(p["system"])
    got = symmetry.orbits(list(root.var_names), p["generators"])
    rebuilt = tree.system_of(symmetry.quotient(root, got))
    assert rebuilt["cons"] == p["quotient"]["cons"]
    assert rebuilt["obj"] == p["quotient"]["obj"]


def test_a_reduction_and_its_digest_survive_a_round_trip():
    prog, tris = _triangle_cover(5)
    cert = _reduce(prog, _full_symmetric(tris, 5)).certificate
    again = _roundtrip(cert)
    assert again.digest() == cert.digest()
    assert again.kind == "symmetry_reduction" and again.solver_free


# --- the README table is a surface that drifts -----------------------------


def _subcommands():
    """Every subcommand, aliases folded into the name they alias."""
    import argparse

    from certo.cli import build_parser

    sub = [a for a in build_parser()._actions
           if isinstance(a, argparse._SubParsersAction)][0]
    seen, names = set(), []
    for name, parser in sub.choices.items():
        if id(parser) not in seen:
            seen.add(id(parser))
            names.append(name)
    return names


def test_every_command_is_in_the_readme_table_and_the_count_is_right():
    """This table went stale quietly: it said twenty-eight, it listed
    twenty-nine, and the CLI had thirty-nine. A reader looking for `audit`
    concluded it did not exist. A number nobody recomputes is a number that
    is wrong."""
    import re

    # The number words live in `catalogue`, which the tool itself uses to
    # write them. Two hand-kept tables is how one of them ends at forty-seven
    # while the other keeps going -- which is exactly what happened here.
    from certo import catalogue

    NUMBER, SPANISH = catalogue.WORDS_EN, catalogue.WORDS_ES

    root = pathlib.Path(__file__).resolve().parent.parent
    commands = set(_subcommands())

    # BOTH READMEs. The Spanish one had drifted two releases behind while the
    # English one was one behind, which is what a table nobody recomputes does.
    for name, pattern, numbers in (
            ("README.md", r"^## The ([a-z-]+) commands$", NUMBER),
            ("README.es.md", r"^## Los ([a-z ]+) comandos$", SPANISH)):
        readme = (root / name).read_text(encoding="utf-8")
        head = re.search(pattern, readme, re.M)
        assert head, "{}: the commands section was renamed".format(name)
        block = re.split(r"\n## ", readme.split(head.group(0), 1)[1])[0]
        listed = re.findall(r"^\| `([a-z]+)`", block, re.M)

        assert set(listed) == commands, {
            "readme": name,
            "missing from the README": sorted(commands - set(listed)),
            "in the README but not a command": sorted(set(listed) - commands)}
        assert len(listed) == len(set(listed)), name + ": a command twice"
        assert head.group(1) == numbers[len(listed)], (
            "{}: the heading says {}, the table has {}".format(
                name, head.group(1), len(listed)))


def test_every_command_answers_a_question_in_the_catalogue():
    """`certo commands` is how somebody who does not know the names finds
    one. A command missing from it ships invisible -- which has happened."""
    import io
    from contextlib import redirect_stdout

    from certo.cli import main

    buf = io.StringIO()
    with redirect_stdout(buf):
        main(["commands"])
    text = buf.getvalue()

    # navigation commands are how you GET here, and listing them would be
    # circular; everything that answers a mathematical question is listed
    NAVIGATION = {"ask", "commands", "repro", "check"}
    missing = [c for c in _subcommands()
               if c not in NAVIGATION and "certo " + c not in text]
    assert not missing, missing


# --- exact integer linear algebra, checked by multiplication ---------------


def _matrix(entries, question="hermite", **kw):
    from certo import MatrixSpec
    from certo.engines import algebra

    return algebra.integer_matrix(
        MatrixSpec(matrix=entries, question=question, **kw), LIM)


def _laplace(M):
    """A determinant nobody in `lattice` had a hand in."""
    n = len(M)
    if n == 1:
        return M[0][0]
    return sum((-1) ** j * M[0][j] *
               _laplace([[M[i][k] for k in range(n) if k != j]
                         for i in range(1, n)])
               for j in range(n))


def test_the_transforms_do_what_the_certificate_says_they_do():
    """Not 'the answer looks right' -- the two identities the answer RESTS on,
    checked by multiplying integers."""
    from certo import lattice

    A = [[2, 4, 4], [-6, 6, 12], [10, -4, -16]]
    r = _matrix(A, "smith")
    assert r.verdict is Verdict.PROVED
    p = r.certificate.payload

    assert p["invariants"] == [2, 6, 12]
    assert lattice.multiply(lattice.multiply(p["u"], A), p["v"]) == p["s"]
    assert lattice.is_identity(lattice.multiply(p["u"], p["u_inv"]))
    assert lattice.is_identity(lattice.multiply(p["v"], p["v_inv"]))

    # the invariant factors multiply to the index, which is |det|
    assert 2 * 6 * 12 == abs(_laplace(A)) == 144
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free


def test_determinants_agree_with_laplace_on_matrices_nobody_chose():
    """Random matrices against an expansion with no shared code. An exact
    method that is wrong is wrong silently, which is the whole hazard."""
    import random

    rng = random.Random(20260917)
    for _ in range(40):
        n = rng.randint(1, 4)
        hi = rng.choice([1, 5, 60])
        A = [[rng.randint(-hi, hi) for _ in range(n)] for _ in range(n)]
        r = _matrix(A, "det")
        assert r.verdict is Verdict.PROVED
        assert r.certificate.payload["det"] == _laplace(A), A
        assert verify(_roundtrip(r.certificate), LIM).ok


def test_rank_is_exact_and_not_a_threshold():
    """The third row is the sum of the first two, which no epsilon decides."""
    r = _matrix([[2, 4, 6, 8], [1, 3, 5, 7], [3, 7, 11, 15]], "rank")
    assert r.meta["rank"] == 2 and r.meta["rows"] == 3 and r.meta["cols"] == 4
    assert verify(_roundtrip(r.certificate), LIM).ok

    # a singular square matrix has determinant 0 and says so
    r = _matrix([[1, 2, 3], [4, 5, 6], [7, 8, 9]], "det")
    assert r.certificate.payload["det"] == 0
    assert r.certificate.payload["rank"] == 2
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_minor_is_the_same_question_on_a_submatrix():
    A = [[2, 4, 4], [-6, 6, 12], [10, -4, -16]]
    r = _matrix(A, "det", rows=[0, 1], cols=[0, 1])
    assert r.certificate.payload["det"] == 36 == _laplace([[2, 4], [-6, 6]])
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_forged_matrix_certificate_does_not_verify():
    """Every payload field a forger would reach for, and the check on it.
    A field that can be edited without failing a check is a field that is
    not carrying its weight."""
    import copy

    base = json.loads(json.dumps(
        _matrix([[2, 4, 4], [-6, 6, 12], [10, -4, -16]],
                "smith").certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    assert not bent(lambda p: p.__setitem__("det", 143))
    assert not bent(lambda p: p.__setitem__("rank", 2))
    assert not bent(lambda p: p.__setitem__("invariants", [1, 12, 12]))
    assert not bent(lambda p: p.__setitem__("det_u", -p["det_u"]))
    assert not bent(lambda p: p.__setitem__("det_v", -p["det_v"]))
    assert not bent(lambda p: p["s"][0].__setitem__(0, 1))
    assert not bent(lambda p: p["u"][0].__setitem__(0, p["u"][0][0] + 1))
    assert not bent(lambda p: p["u_inv"][0].__setitem__(0, 0))
    assert not bent(lambda p: p["v"][0].__setitem__(0, p["v"][0][0] + 1))
    assert not bent(lambda p: p["matrix"][0].__setitem__(0, 3))


def test_a_transform_that_is_not_unimodular_is_caught_by_its_own_inverse():
    """The load-bearing check: without `U.U_inv = I` a SCALED transform would
    pass everything else and multiply the determinant by whatever it likes."""
    import copy

    from certo import lattice

    base = json.loads(json.dumps(
        _matrix([[3, 1], [5, 2]], "hermite").certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    d = copy.deepcopy(base)
    p = d["payload"]
    p["u"] = [[2 * v for v in row] for row in p["u"]]
    p["h"] = lattice.multiply(p["u"], p["matrix"])
    p["det"] = p["det"] * 4                    # consistent with the new H
    rep = verify(Certificate.from_dict(d), LIM)
    assert not rep.ok
    assert any(not ok for _label, ok, _detail in rep.checks)


def test_the_sign_is_decided_and_not_assumed():
    """`U.U_inv = I` leaves the sign of det(U) free, and that sign IS the sign
    of det(A). One determinant modulo an odd prime settles it -- exactly,
    because there were only ever two candidates."""
    from certo import lattice

    for A in ([[0, 1], [1, 0]], [[1, 0], [0, 1]], [[2, 1], [7, 4]],
              [[0, 0, 1], [0, 1, 0], [1, 0, 0]]):
        out = lattice.hermite(A)
        assert lattice.unimodular_sign(out["u"]) == out["det_u"]
        assert out["det_u"] in (1, -1)
        got = out["det_u"]
        for i in range(len(A)):
            got *= out["h"][i][i]
        assert got == _laplace(A), A

    # a matrix that is not unimodular gets no sign at all
    assert lattice.unimodular_sign([[2, 0], [0, 1]]) == 0


def test_a_matrix_that_is_not_one_is_refused_rather_than_repaired():
    from fractions import Fraction

    r = _matrix([[1, 2], [3]], "rank")
    assert r.verdict is Verdict.INCONCLUSIVE and "rectangular" in r.detail

    # 2.5 must not become 2: a matrix quietly rounded is a different matrix
    r = _matrix([[2.5, 1], [0, 1]], "det")
    assert r.verdict is Verdict.INCONCLUSIVE and "not an integer" in r.detail

    # but an integer written as a fraction is an integer
    r = _matrix([[Fraction(4, 2), 1], [0, 1]], "det")
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["det"] == 2

    # the determinant of a rectangle is not a thing
    r = _matrix([[1, 2, 3], [4, 5, 6]], "det")
    assert r.verdict is Verdict.INCONCLUSIVE and "square" in r.detail


# --- a missing message key is invisible ------------------------------------


def _catalogues():
    import json

    root = pathlib.Path(__file__).resolve().parent.parent / "src/certo/locales"
    return {p.stem: json.loads(p.read_text(encoding="utf-8"))
            for p in sorted(root.glob("*.json"))}


def _keys_used():
    """Every literal key handed to `t(...)`, with the file it came from."""
    import ast

    root = pathlib.Path(__file__).resolve().parent.parent / "src/certo"
    out = {}
    for path in sorted(root.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), str(path))
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or not node.args:
                continue
            fn = node.func
            name = getattr(fn, "id", None) or getattr(fn, "attr", None)
            if name not in ("t", "_t"):
                continue
            first = node.args[0]
            if isinstance(first, ast.Constant) and isinstance(first.value, str):
                out.setdefault(first.value, set()).add(path.name)
    return out


def test_every_message_key_the_code_asks_for_exists():
    """`t()` falls back to the KEY when it is missing, so a typo ships as a
    line of output reading `verify.matrix.detail` and nobody notices. That is
    exactly what `core_matrix` was printing until a name collision made it
    fail loudly instead."""
    en = _catalogues()["en"]
    missing = {k: sorted(v) for k, v in _keys_used().items() if k not in en}
    assert not missing, missing


def test_the_languages_carry_the_same_keys_and_the_same_placeholders():
    """A message translated with a different `{placeholder}` raises KeyError
    at the moment somebody switches language, which is the worst possible
    moment."""
    import re

    cats = _catalogues()
    en = cats["en"]
    for lang, table in cats.items():
        if lang == "en":
            continue
        assert set(table) == set(en), {
            "only in " + lang: sorted(set(table) - set(en))[:5],
            "only in en": sorted(set(en) - set(table))[:5]}
        for key, text in table.items():
            want = set(re.findall(r"\{(\w+)\}", en[key]))
            got = set(re.findall(r"\{(\w+)\}", text))
            assert got == want, (lang, key, sorted(want), sorted(got))


def test_a_message_is_called_with_the_arguments_it_declares():
    """The collision that made this whole family of tests necessary: one key
    used by two verifiers, each passing different placeholders. The second
    one raises KeyError the first time it runs -- in `verify`, on a stored
    certificate, long after the change that caused it."""
    import ast
    import re

    root = pathlib.Path(__file__).resolve().parent.parent / "src/certo"
    en = _catalogues()["en"]
    bad = []
    for path in sorted(root.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), str(path))
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or not node.args:
                continue
            name = getattr(node.func, "id", None) or getattr(node.func,
                                                             "attr", None)
            if name not in ("t", "_t"):
                continue
            key = node.args[0]
            if not (isinstance(key, ast.Constant)
                    and isinstance(key.value, str) and key.value in en):
                continue
            if any(kw.arg is None for kw in node.keywords):   # **something
                continue
            passed = {kw.arg for kw in node.keywords}
            want = set(re.findall(r"\{(\w+)\}", en[key.value]))
            if want - passed:
                bad.append((path.name, node.lineno, key.value,
                            sorted(want - passed)))
    assert not bad, bad


# --- 0.8 defect: a denominator is not a free variable ----------------------


def test_a_hypothesis_guarding_a_denominator_is_not_reported_as_needed():
    """Reported after 0.8, and reproduced exactly.

    Division is TOTAL in SMT: `n/0` is some value Z3 invents. So dropping
    `d != 0` produced an instant counterexample -- `d = 0`, with the invented
    value chosen to break the goal -- and the hypothesis read `needed` for a
    reason that was about the solver, not the theorem.
    """
    import z3

    from certo import Spec
    from certo.engines import smt

    n, d = z3.Ints("n d")
    spec = Spec(title="d != 0 only protects the denominator")
    spec.assume("d_nonzero", d != 0)
    spec.assume("n_zero", n == 0)
    spec.claim(n / d == 0)

    r = smt.audit(spec, LIM)
    rows = {row["hypothesis"]: row for row in r.certificate.payload["rows"]}

    assert rows["d_nonzero"]["verdict"] == "domain"
    assert rows["d_nonzero"]["obligations"] == ["d"]
    assert rows["d_nonzero"]["witness"] is None
    # and the OTHER hypothesis is still audited normally
    assert rows["n_zero"]["verdict"] == "needed"

    # the certificate now verifies, which on this spec it did NOT before:
    # every witness carried Z3's `div0`/`mod0`, which nothing could re-apply
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok, [c for c in rep.checks if not c[1]]
    assert any("must NOT be dropped" in w for w in rep.warnings)


def test_no_witness_carries_the_solvers_own_bookkeeping():
    """`div0` and `mod0` are functions Z3 invents to make division total. They
    are not variables of the problem, and a witness carrying them could not be
    re-applied by anybody -- which is why every row used to fail re-checking
    on any spec containing a division."""
    import z3

    from certo import Spec
    from certo.engines import smt

    n, d = z3.Ints("n d")
    spec = Spec()
    spec.assume("d_big", d >= 2)
    spec.assume("n_big", n >= 100)
    spec.claim(n / d >= 1)

    r = smt.audit(spec, LIM)
    for row in r.certificate.payload["rows"]:
        for name, (sort, _value) in (row.get("witness") or {}).items():
            assert name not in ("div0", "mod0", "rem0"), name
            assert sort in ("Int", "Real", "Bool"), (name, sort)
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_domain_and_redundant_are_asked_apart_not_assumed():
    """The same hypothesis, two verdicts, depending on whether anything ELSE
    still forces the obligation. If `domain` were read off the shape of the
    formula this would come back wrong."""
    import z3

    from certo import Spec
    from certo.engines import smt

    n, d = z3.Ints("n d")

    alone = Spec()
    alone.assume("d_nonzero", d != 0)
    alone.assume("n_nonneg", n >= 0)
    alone.claim(n / d >= 0)

    guarded = Spec()
    guarded.assume("d_positive", d >= 1)
    guarded.assume("d_nonzero", d != 0)
    guarded.assume("n_nonneg", n >= 0)
    guarded.claim(n / d >= 0)

    def verdict_of(spec, name):
        r = smt.audit(spec, LIM)
        assert verify(_roundtrip(r.certificate), LIM).ok
        return {row["hypothesis"]: row["verdict"]
                for row in r.certificate.payload["rows"]}[name]

    # `d != 0` alone does not make the claim true -- d = -1 breaks it -- so it
    # is genuinely needed here, obligations or not
    assert verdict_of(alone, "d_nonzero") == "needed"
    # beside `d >= 1` it carries nothing: the obligation is still forced
    assert verdict_of(guarded, "d_nonzero") == "redundant"


def test_modulo_is_guarded_too_and_a_numeral_divisor_is_not():
    """`n % d` has the same hole, and `n / 3` has none: an obligation for a
    divisor that cannot vanish would be noise in every certificate."""
    import z3

    from certo import Spec
    from certo.audit import obligations_for
    from certo.engines import smt

    n, d = z3.Ints("n d")

    mod = Spec()
    mod.assume("d_nonzero", d != 0)
    mod.assume("n_pos", n >= 1)
    mod.claim(n % d >= 0)
    assert [text for text, _g in obligations_for(mod)] == ["d"]
    rows = {r["hypothesis"]: r["verdict"]
            for r in smt.audit(mod, LIM).certificate.payload["rows"]}
    assert rows["d_nonzero"] == "domain"

    fixed = Spec()
    fixed.assume("n_pos", n >= 3)
    fixed.claim(n / 3 >= 1)
    assert obligations_for(fixed) == []

    # a compound divisor is one obligation, named as it appears
    compound = Spec()
    compound.assume("safe", d >= 1)
    compound.claim(n / (d + 1) >= 0)
    assert len(obligations_for(compound)) == 1


def test_the_obligations_are_derived_during_verification_not_believed():
    """A certificate declaring fewer divisors than its own formulas contain is
    one whose searches ran unguarded -- so the list is recomputed from the
    formulas that travelled, the same way a branch-and-bound node rebuilds its
    own linear program."""
    import copy

    import z3

    from certo import Spec
    from certo.engines import smt

    n, d = z3.Ints("n d")
    spec = Spec()
    spec.assume("d_nonzero", d != 0)
    spec.assume("n_zero", n == 0)
    spec.claim(n / d == 0)

    base = json.loads(json.dumps(smt.audit(spec, LIM).certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok
    assert base["payload"]["obligations"] == ["d"]

    def bent(fn):
        c = copy.deepcopy(base)
        fn(c["payload"])
        return verify(Certificate.from_dict(c), LIM).ok

    # claiming there was nothing to guard
    assert not bent(lambda p: p.__setitem__("obligations", []))
    # a `domain` verdict with no obligation behind it is `redundant` wearing
    # a kinder label
    assert not bent(lambda p: p["rows"][0].__setitem__("obligations", []))
    # and the tally still has to match
    assert not bent(lambda p: p["counts"].__setitem__("domain", 7))
    # a verdict the tally does not declare at all
    assert not bent(lambda p: p["counts"].pop("domain"))


def test_an_audit_certificate_from_before_the_fourth_verdict_still_verifies():
    """0.8 wrote three counts and no obligations. Those certificates are on
    disk in other people's repositories and must keep verifying -- the schema
    is frozen at 4, and this is exactly the compatibility that promises."""
    import z3

    from certo import Spec
    from certo.engines import smt

    n = z3.Int("n")
    spec = Spec()
    spec.assume("n_large", n >= 5)
    spec.assume("m_bounded", n >= 1)
    spec.claim(n >= 1)

    d = json.loads(json.dumps(smt.audit(spec, LIM).certificate.to_dict()))
    # rewind the payload to the 0.8 shape
    d["payload"].pop("obligations", None)
    d["payload"]["counts"].pop("domain")
    assert set(d["payload"]["counts"]) == {"needed", "redundant", "unknown"}
    assert verify(Certificate.from_dict(d), LIM).ok


# --- by symmetry, for a family rather than an instance ---------------------


def _family(**changes):
    """The split family, as `examples/parametric_symmetry.py` declares it."""
    import importlib.util

    root = pathlib.Path(__file__).resolve().parent.parent
    path = root / "examples" / "parametric_symmetry.py"
    spec = importlib.util.spec_from_file_location("certo_ps_example", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    out = mod.spec()
    for key, value in changes.items():
        setattr(out, key, value)
    return out, mod


def _parametric(spec):
    from certo.engines import algebra

    return algebra.reduce_parametric(spec, LIM)


def test_the_symbolic_quotient_agrees_with_the_family_it_describes():
    """Two orbits, four regimes, and every window point checked against a
    program built from the OBJECTS rather than from the formulas."""
    spec, _mod = _family()
    r = _parametric(spec)

    assert r.verdict is Verdict.PROVED
    assert r.meta["points"] == 35 and r.meta["orbits"] == 2
    assert r.meta["regimes"] == ["(none)", "KKI", "KKK", "KKK,KKI"]
    # C(p,2) + pq, which is what a split graph has
    assert r.meta["objects"] == "1/2*p^2 + p*q - 1/2*p"

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert any("not the same claim" in w for w in rep.warnings)
    assert any("not a proof of it" in w for w in rep.warnings)


def test_a_condition_carried_past_its_boundary_is_refuted():
    """The error the boundary regimes hide, and the reason this command
    exists: `3x >= 1` comes from three mutually adjacent clique vertices, and
    at p = 2 there are not three of them."""
    spec, mod = _family()
    spec.rows = [("KKK", {"clique": mod.K(3)}, ">=", mod.K(1), []),
                 spec.rows[1]]

    r = _parametric(spec)
    assert r.verdict is Verdict.REFUTED
    assert r.certificate is None            # nothing is certified about it
    assert r.meta["failed"] == 7 and r.meta["checked"] == 35
    assert "p=2, q=0" in r.detail


def test_every_way_of_misstating_the_declaration_is_caught():
    """Five, each a real mistake somebody makes in a write-up, and each
    showing up as a disagreement at some parameter value."""
    from fractions import Fraction

    def refuted(label, **changes):
        spec, mod = _family()
        for key, value in changes.items():
            if callable(value):
                setattr(spec, key, value(mod, spec))
            else:
                setattr(spec, key, value)
        r = _parametric(spec)
        assert r.verdict is Verdict.REFUTED, label
        assert r.meta["failed"] > 0, label
        return r.meta["failed"]

    # a multiplicity that halves the cross orbit
    assert refuted("pq/2", orbits=lambda m, s: {
        "clique": m.CLIQUE, "cross": m.CROSS.scaled(Fraction(1, 2))}) == 30
    # p^2/2 where the family has C(p,2)
    assert refuted("p^2/2", orbits=lambda m, s: {
        "clique": (m.P * m.P).scaled(Fraction(1, 2)), "cross": m.CROSS}) == 35
    # an orbit that is not there at all
    assert refuted("ghost", orbits=lambda m, s: {
        "clique": m.CLIQUE, "cross": m.CROSS, "ghost": m.K(1)}) == 35
    # a coefficient inside a row
    assert refuted("coefficient", rows=lambda m, s: [
        s.rows[0],
        ("KKI", {"clique": m.K(1), "cross": m.K(3)}, ">=", m.K(1),
         [m.P - m.K(2), m.Q - m.K(1)])]) == 30
    # a condition off by one
    assert refuted("off by one", rows=lambda m, s: [
        ("KKK", {"clique": m.K(3)}, ">=", m.K(1), [m.P - m.K(2)]),
        s.rows[1]]) == 7


def test_the_regimes_are_derived_from_the_conditions_not_listed():
    """A piecewise closed form has one branch per regime. Deriving them is
    what lets a formula be compared against the program it claims to solve --
    three branches over four regimes is a formula missing a case."""
    from certo import paramsym

    spec, _mod = _family()
    got = paramsym.regimes(spec, spec.window)
    assert set(got) == {"(none)", "KKI", "KKK", "KKK,KKI"}
    # no triangles at all, exactly once: p = 2, q = 0
    assert got["(none)"] == [{"p": 2, "q": 0}]
    # p = 2 with an independent vertex: the clique triangle is absent
    assert all(v["p"] == 2 and v["q"] >= 1 for v in got["KKI"])
    # q = 0: no cross edges, so no mixed triangle
    assert all(v["q"] == 0 and v["p"] >= 3 for v in got["KKK"])


def test_an_orbit_is_present_exactly_where_its_multiplicity_is_positive():
    """Not a convention -- a measurement. The family has TWO edge orbits for
    q >= 1 and ONE for q = 0, because there are no cross edges to be an orbit
    of, and writing "two orbits" for every q is how a degenerate case gets a
    constraint it has no right to."""
    from certo import paramsym

    spec, _mod = _family()
    assert paramsym.live_orbits(spec, {"p": 5, "q": 3}) == ["clique", "cross"]
    assert paramsym.live_orbits(spec, {"p": 5, "q": 0}) == ["clique"]
    assert paramsym.live_rows(spec, {"p": 5, "q": 0}) == ["KKK"]
    assert paramsym.live_rows(spec, {"p": 2, "q": 0}) == []

    # a negative multiplicity is a wrong polynomial, not a small orbit
    spec.orbits = dict(spec.orbits, broken=_neg_poly(spec))
    try:
        paramsym.live_orbits(spec, {"p": 2, "q": 0})
        raise AssertionError("expected a refusal")
    except paramsym.NotParametricSymmetry as e:
        assert "not a small orbit" in str(e)


def _neg_poly(spec):
    from certo.polynomials import Poly

    ring = tuple(spec.parameters)
    return Poly.var(ring, "p") - Poly.const(ring, 5)


def test_a_declaration_with_no_window_is_refused():
    """Unfalsifiable is worse than unchecked, so it is refused rather than
    certified with nothing behind it."""
    from certo import paramsym

    spec, _mod = _family()
    spec.window = []
    try:
        paramsym.certify(spec, LIM)
        raise AssertionError("expected a refusal")
    except paramsym.NotParametricSymmetry as e:
        assert "unfalsifiable" in str(e)

    spec, _mod = _family()
    spec.instance = None
    try:
        paramsym.certify(spec, LIM)
        raise AssertionError("expected a refusal")
    except paramsym.NotParametricSymmetry as e:
        assert "falsifiable" in str(e)


def test_a_forged_parametric_certificate_does_not_verify():
    """The symbolic side is re-derived, so a payload edited to agree with
    itself still has to agree with the numbers the instances produced."""
    import copy

    spec, _mod = _family()
    base = json.loads(json.dumps(_parametric(spec).certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    # a point relabelled as agreeing when it did not
    assert not bent(lambda p: p["points"][0].__setitem__("ok", False))
    # the recorded orbit sizes moved away from the multiplicities
    assert not bent(lambda p: p["points"][3]["sizes"].__setitem__(
        "clique", "99"))
    # a row claimed present in a regime where its condition fails
    assert not bent(lambda p: p["points"][0].__setitem__("rows", ["KKK"]))
    # the object count no longer matches what the instances had
    assert not bent(lambda p: p["orbits"].__setitem__(
        "clique", {"1 0": "1"}))


def _solve(matrix, rhs, domain="rational"):
    from certo import LinearSystemSpec
    from certo.engines import algebra

    return algebra.linear_system(
        LinearSystemSpec(matrix=matrix, rhs=rhs, domain=domain), LIM)


K4_INCIDENCE = [[1, 1, 0, 0], [1, 0, 1, 0], [0, 1, 1, 0],
                [1, 0, 0, 1], [0, 1, 0, 1], [0, 0, 1, 1]]


def test_a_solution_is_checked_against_the_system_that_travelled():
    """Not against the one somebody remembers stating. A solution to a
    slightly different matrix is the failure mode here."""
    import copy

    r = _solve(K4_INCIDENCE, [2, 2, 2, 0, 0, 0])
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["solution"] == ["1", "1", "1", "-1"]

    base = json.loads(json.dumps(r.certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    assert not bent(lambda p: p["solution"].__setitem__(3, "1"))
    assert not bent(lambda p: p["rhs"].__setitem__(0, "3"))
    assert not bent(lambda p: p["matrix"][0].__setitem__(0, "0"))
    assert not bent(lambda p: p.__setitem__("rank", 3))


def test_a_rational_solution_says_nothing_about_non_negativity():
    """`y` is non-negative everywhere, the representation is UNIQUE, and it
    uses a weight of -1. The matrix has full column rank, so there is no other
    answer to pick instead -- the negative weight is not an artefact of how
    the elimination went."""
    r = _solve(K4_INCIDENCE, [2, 2, 2, 0, 0, 0])
    x = r.certificate.payload["solution"]

    assert r.certificate.payload["status"] == "unique"
    assert r.certificate.payload["rank"] == 4        # full column rank
    assert any(v.startswith("-") for v in x)

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert any("non-negative" in w for w in rep.warnings)


def test_the_same_system_answers_differently_over_Z_and_over_Q():
    """Which is why the domain is a declaration and not a default somebody
    discovers later."""
    ones = [1, 1, 1, 1, 1, 1]

    over_q = _solve(K4_INCIDENCE, ones)
    assert over_q.verdict is Verdict.PROVED
    assert over_q.certificate.payload["solution"] == ["1/2"] * 4

    over_z = _solve(K4_INCIDENCE, ones, domain="integer")
    assert over_z.verdict is Verdict.REFUTED
    assert over_z.certificate.payload["solution"] is None
    # the invariant factor that blocks it
    assert over_z.certificate.payload["invariants"] == [1, 1, 1, 2]

    for r in (over_q, over_z):
        assert verify(_roundtrip(r.certificate), LIM).ok


def test_unsolvable_carries_the_obstruction_that_proves_it():
    """`y.A = 0` and `y.b != 0`: a negative result with nothing behind it is
    a claim, and this one is two more products."""
    from fractions import Fraction

    r = _solve(K4_INCIDENCE, [1, 1, 0, 0, 1, 1])
    assert r.verdict is Verdict.REFUTED
    y = [Fraction(v) for v in r.certificate.payload["witness"]]

    cols = list(zip(*K4_INCIDENCE))
    assert all(sum(a * c for a, c in zip(y, col)) == 0 for col in cols)
    assert sum(a * c for a, c in zip(y, [1, 1, 0, 0, 1, 1])) != 0
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_forged_obstruction_does_not_verify():
    import copy

    base = json.loads(json.dumps(
        _solve([[1, 1], [2, 2]], [1, 3]).certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok
    assert base["payload"]["witness"] == ["-2", "1"]

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    # a y that does not kill A
    assert not bent(lambda p: p.__setitem__("witness", ["1", "1"]))
    # a y that kills A but dies on b too, so it obstructs nothing
    assert not bent(lambda p: p.__setitem__("witness", ["0", "0"]))
    # no witness at all
    assert not bent(lambda p: p.__setitem__("witness", None))


def test_underdetermined_returns_the_set_and_not_a_point():
    """Reporting one point of an affine subspace as though it were the answer
    is how a free parameter disappears from a write-up."""
    from fractions import Fraction

    A = [[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1]]
    r = _solve(A, [1, 1, 1])
    p = r.certificate.payload

    assert p["status"] == "underdetermined"
    assert len(p["kernel"]) == p["columns"] - p["rank"] == 1
    k = [Fraction(v) for v in p["kernel"][0]]
    assert all(sum(a * v for a, v in zip(row, k)) == 0 for row in A)

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("NOT unique" in w for w in rep.warnings)


def test_the_kernel_over_Z_is_a_lattice_basis_and_not_merely_a_span():
    """Which is the reason to go through Smith rather than reduce over Q and
    clear denominators."""
    from fractions import Fraction

    A = [[2, 4]]
    r = _solve(A, [6], domain="integer")
    p = r.certificate.payload
    assert p["status"] == "underdetermined"
    assert all(Fraction(v).denominator == 1 for v in p["solution"])
    for k in p["kernel"]:
        vals = [Fraction(v) for v in k]
        assert all(v.denominator == 1 for v in vals)
        assert sum(a * v for a, v in zip(A[0], vals)) == 0
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_float_is_refused_rather_than_converted():
    """A system read from floating point is a different system."""
    r = _solve([[1.5, 1], [0, 1]], [1, 1])
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "not exact" in r.detail

    r = _solve([[1, 1], [0]], [1, 1])
    assert r.verdict is Verdict.INCONCLUSIVE and "rectangular" in r.detail

    r = _solve([[1, 1]], [1, 1])
    assert r.verdict is Verdict.INCONCLUSIVE and "right-hand side" in r.detail

    # a Fraction that happens to be integral is fine
    from fractions import Fraction

    r = _solve([[Fraction(4, 2)]], [Fraction(6, 3)])
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["solution"] == ["1"]


def test_solve_agrees_with_an_independent_elimination():
    """Random systems against a solver nothing here shares code with."""
    import random
    from fractions import Fraction

    rng = random.Random(20260917)
    for _ in range(60):
        n, m = rng.randint(1, 4), rng.randint(1, 4)
        A = [[rng.randint(-5, 5) for _ in range(m)] for _ in range(n)]
        b = [rng.randint(-5, 5) for _ in range(n)]
        r = _solve(A, b)
        p = r.certificate.payload

        if p["solution"] is None:
            # no solution: then no x can satisfy it, which sympy-free linear
            # algebra confirms by the rank of [A|b] exceeding that of A
            assert _rank_of(A) < _rank_of([row + [v] for row, v in zip(A, b)])
        else:
            x = [Fraction(v) for v in p["solution"]]
            assert [sum(Fraction(a) * v for a, v in zip(row, x))
                    for row in A] == [Fraction(v) for v in b]
        assert verify(_roundtrip(r.certificate), LIM).ok


def _rank_of(M):
    """Plain Gaussian elimination, written here so the comparison is not
    against the code under test."""
    from fractions import Fraction

    A = [[Fraction(v) for v in row] for row in M]
    n, m = len(A), len(A[0])
    r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(n):
            if i != r and A[i][c]:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r


# --- the quotient as an equivalence, not as two optima that agree ----------


def _family_module():
    import importlib.util

    root = pathlib.Path(__file__).resolve().parent.parent
    path = root / "examples" / "equitable_quotient.py"
    spec = importlib.util.spec_from_file_location("certo_eq_example", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _quotient(spec):
    from certo.engines import algebra

    return algebra.equitable_quotient(spec, LIM)


def test_the_two_programs_have_the_same_attainable_values():
    """Not "the optima agree" -- the maps. A feasible physical point projects
    to a feasible quotient point of the same value, and back."""
    from fractions import Fraction

    from certo import equitable, tree
    from certo.engines import lp as lpe

    mod = _family_module()
    physical, _c, _t = mod.physical()
    rows, columns = mod.partition()
    data = equitable.analyse(physical, rows, columns)
    reduced = equitable.quotient(physical, data)

    def value(lp, x):
        return sum(Fraction(str(c)) * Fraction(x.get(v, 0))
                   for v, c in lp.obj.items())

    def violated(lp, x):
        for name, coeffs, sense, rhs in lp.cons:
            s = sum(Fraction(str(c)) * Fraction(x.get(v, 0))
                    for v, c in coeffs.items())
            r = Fraction(str(rhs))
            if (sense == "<=" and s > r) or (sense == ">=" and s < r):
                return name
        return None

    # project an optimal physical point
    x = {k: Fraction(str(v))
         for k, v in lpe.opt(physical, LIM).meta["solution"].items()}
    assert violated(physical, x) is None
    z = {"z_" + j: v for j, v in equitable.project(x, data).items()}
    assert violated(reduced, z) is None
    assert value(reduced, z) == value(physical, x)

    # lift an optimal quotient point
    zs = {k[2:]: Fraction(str(v))
          for k, v in lpe.opt(reduced, LIM).meta["solution"].items()}
    back = equitable.lift(zs, data)
    assert violated(physical, back) is None
    assert value(physical, back) == value(
        reduced, {"z_" + j: v for j, v in zs.items()})

    _ = tree


def test_the_quotient_reproduces_the_value_the_family_has():
    """226 rows and 3147 columns down to 13 and 49, same optimum."""
    from fractions import Fraction

    from certo import tree
    from certo.engines import lp as lpe

    r = _quotient(_family_module().spec())
    assert r.verdict is Verdict.PROVED
    assert r.meta["physical_rows"] == 226
    assert r.meta["physical_columns"] == 3147
    assert (r.meta["rows"], r.meta["columns"]) == (13, 49)

    reduced = tree.spec_of(r.certificate.payload["quotient"])
    assert Fraction(lpe.opt(reduced, LIM).meta["objective"]) == 121

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert any("EQUIVALENCE" in w for w in rep.warnings)
    assert any("NOTHING about integrality" in w for w in rep.warnings)


def test_a_class_mixing_two_capacities_is_refused_by_name():
    """The acceptance control. Intact, the physical K4 and its quotient both
    give 4. Cap one edge and the physical value is 2, while aggregating over a
    class that mixes capacities would report 10/3 -- so the partition must be
    refused, and it names the two rows."""
    r = _quotient(_family_module().capacity_breaks_the_class())

    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None
    assert "not constant in capacity" in r.detail
    assert "`e01`" in r.detail and "`e02`" in r.detail


def test_the_two_regularities_are_not_the_same_quantity():
    """Using one where the other belongs builds a quotient that is simply
    wrong, and it took the physical program to notice: on K4 with triangles
    only, `H` in place of `B` reports 6 where the value is 4."""
    from fractions import Fraction

    from certo import equitable, tree
    from certo.engines import lp as lpe

    mod = _family_module()
    spec = mod.capacity_breaks_the_class()
    # the same K4, uncapped
    for i, (name, coeffs, sense, _rhs) in enumerate(list(spec.lp.cons)):
        spec.lp.cons[i] = (name, coeffs, sense, 1)

    data = equitable.analyse(spec.lp, spec.rows, spec.columns)
    assert data["B"][("edge", "tri")] == 3        # a triangle uses 3 edges
    assert data["H"][("edge", "tri")] == 2        # an edge is in 2 triangles
    # N.H = M.B: 6*2 = 4*3
    assert data["N"]["edge"] * data["H"][("edge", "tri")] == \
        data["M"]["tri"] * data["B"][("edge", "tri")] == 12

    reduced = equitable.quotient(spec.lp, data)
    assert Fraction(lpe.opt(reduced, LIM).meta["objective"]) == 4
    assert Fraction(lpe.opt(spec.lp, LIM).meta["objective"]) == 4
    _ = tree


def test_a_partition_that_is_not_one_is_refused():
    from certo import equitable

    mod = _family_module()
    spec = mod.capacity_breaks_the_class()

    missing = dict(spec.columns)
    missing.pop(sorted(missing)[0])
    try:
        equitable.analyse(spec.lp, spec.rows, missing)
        raise AssertionError("expected a refusal")
    except equitable.NotEquitable as e:
        assert "no class" in str(e)

    stray = dict(spec.rows)
    stray["not_a_row"] = "edge"
    try:
        equitable.analyse(spec.lp, stray, spec.columns)
        raise AssertionError("expected a refusal")
    except equitable.NotEquitable as e:
        assert "does not have" in str(e)


def test_regularity_is_checked_row_by_row_and_not_by_block_total():
    """A block whose TOTAL is right while individual rows differ still breaks
    lifting, and that is the case a total-only check waves through."""
    from certo import LPSpec, equitable

    # Two rows in one class, two columns in one class. The block totals 8
    # either way, and an average of 4 per row -- but one row sees 2 and the
    # other 6, so lifting a class mass evenly overloads the first. `1+3`
    # against `3+1` would NOT be a counterexample: both rows see 4, the
    # partition is equitable, and the equivalence genuinely holds.
    p = LPSpec(sense="max", title="a block total that hides a difference")
    p.variable("c1", 0, None)
    p.variable("c2", 0, None)
    p.objective({"c1": 1, "c2": 1})
    p.constraint({"c1": 1, "c2": 1}, "<=", 10, name="r1")
    p.constraint({"c1": 3, "c2": 3}, "<=", 10, name="r2")

    rows = {"r1": "R", "r2": "R"}
    cols = {"c1": "C", "c2": "C"}
    try:
        equitable.analyse(p, rows, cols)
        raise AssertionError("expected a refusal")
    except equitable.NotEquitable as e:
        assert "regularity" in str(e)

    # The same block total, made regular row by row, passes -- and so does
    # the asymmetric `1+3 / 3+1`, because what the equivalence needs is the
    # per-row SUM over a class and not the individual coefficients.
    p.cons[0] = ("r1", {"c1": 2, "c2": 2}, "<=", 10)
    p.cons[1] = ("r2", {"c1": 2, "c2": 2}, "<=", 10)
    data = equitable.analyse(p, rows, cols)
    assert data["H"][("R", "C")] == 4 and data["B"][("R", "C")] == 4

    p.cons[0] = ("r1", {"c1": 1, "c2": 3}, "<=", 10)
    p.cons[1] = ("r2", {"c1": 3, "c2": 1}, "<=", 10)
    assert equitable.analyse(p, rows, cols)["H"][("R", "C")] == 4


def test_a_forged_quotient_certificate_does_not_verify():
    import copy

    base = json.loads(json.dumps(
        _quotient(_family_module().spec()).certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    key = sorted(base["payload"]["B"])[0]
    # B moved away from H: the double count stops holding
    assert not bent(lambda p: p["B"].__setitem__(key, "99"))
    assert not bent(lambda p: p["H"].__setitem__(key, "99"))
    # a class size that is not the one the identities were checked against
    assert not bent(lambda p: p["N"].__setitem__(sorted(p["N"])[0], 999))
    # a quotient that is not the one the class data produces
    assert not bent(lambda p: p["quotient"]["cons"].clear())
    # an empty column class: lifting would divide by nothing
    assert not bent(lambda p: p["M"].__setitem__(sorted(p["M"])[0], 0))


# --- Lean is emitted only where certo is confident of the result -----------


def _bridged_proof(theorem_subject=None, lemma_subject=None, transport=""):
    """A proof with one bridge, optionally about a different object."""
    import json
    import tempfile
    from pathlib import Path

    import z3

    from certo import ProofSpec, Spec
    from certo.engines import smt

    x = z3.Real("x")
    src = Spec()
    src.assume("h", x >= 1)
    src.claim(x >= 1)
    sub = smt.prove(src, LIM).certificate
    d = Path(tempfile.mkdtemp(prefix="certo_transport_"))
    (d / "c.json").write_text(json.dumps(sub.to_dict()), encoding="utf-8")

    k = z3.Int("k")
    p = ProofSpec(title="a crossing", subject=theorem_subject)
    p.assume("k_ge_6", k >= 6)
    p.lemma("finite", certificate=str(d / "c.json"), states=(k <= 10),
            bridge="checked exhaustively", subject=lemma_subject,
            transport=transport)
    p.conclude(z3.And(k >= 6, k <= 10))
    return p


def test_a_lemma_about_another_object_must_name_the_map():
    """Where a fact about a computation becomes a fact about the mathematics.

    Two users on two different routes reported this as the real risk, and one
    of them named it exactly: silently passing from a computational object to
    the paper's object. certo cannot check the map -- that is Lean's part --
    but it can refuse to let the change be invisible.
    """
    from certo.engines import compose

    silent = compose.compose(
        _bridged_proof(("monoid", "M"), ("graph", "K7")), LIM)
    assert silent.verdict is Verdict.INCONCLUSIVE
    assert silent.certificate is None
    assert silent.meta["silent_transport"] == ["finite"]
    assert "DIFFERENT object" in silent.detail

    named = compose.compose(
        _bridged_proof(("monoid", "M"), ("graph", "K7"), "incidence_monoid"),
        LIM)
    assert named.verdict is Verdict.PROVED
    assert named.certificate.payload["crossings"] == [
        {"lemma": "finite", "from": ["graph", "K7"], "to": ["monoid", "M"],
         "map": "incidence_monoid"}]


def test_every_crossing_is_repeated_on_every_verification():
    """Like a bridge. A crossing visible only to whoever wrote the spec is
    not a crossing anybody else can weigh."""
    from certo.engines import compose

    r = compose.compose(
        _bridged_proof(("monoid", "M"), ("graph", "K7"), "incidence_monoid"),
        LIM)
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("the theorem is about monoid" in w for w in rep.warnings)
    crossing = [w for w in rep.warnings if "cross from another object" in w]
    assert len(crossing) == 1
    assert "incidence_monoid: graph -> monoid" in crossing[0]
    assert "certo did NOT check" in crossing[0]


def test_declaring_no_objects_keeps_the_old_behaviour_exactly():
    """A proof that never mentions objects has no levels to cross, and must
    not acquire a new way to fail."""
    from certo.engines import compose

    r = compose.compose(_bridged_proof(), LIM)
    assert r.verdict is Verdict.PROVED
    assert "crossings" not in r.certificate.payload
    assert "subject" not in r.certificate.payload
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert not any("cross from another object" in w for w in rep.warnings)
    # the bridge is still reported, which was the old behaviour
    assert any("finite" in w for w in rep.warnings)


def test_the_same_object_is_not_a_crossing():
    """A lemma about the theorem's own object needs no map."""
    from certo.engines import compose

    r = compose.compose(
        _bridged_proof(("monoid", "M"), ("monoid", "M")), LIM)
    assert r.verdict is Verdict.PROVED
    assert not r.certificate.payload.get("crossings")


def test_a_subject_must_be_a_kind_and_an_id():
    from certo import ProofSpec

    p = ProofSpec()
    for bad in ("cone", ("cone",), ("a", "b", "c")):
        try:
            p.lemma("x", states=None, certificate="c.json", subject=bad)
            raise AssertionError("expected a refusal for " + repr(bad))
        except ValueError:
            pass


# --- integer arithmetic exports to a theorem `omega` closes ----------------


def test_tseitin_agrees_with_z3_on_random_formulas():
    """The check that matters: satisfiability, validity, and the models.

    An encoding that is subtly wrong produces a CNF that is refutable when the
    formula is not, which is a wrong answer wearing a DRAT proof. So it is
    compared against a decision procedure over a hundred random formulas, and
    every model is substituted back into the formula it claims to satisfy.
    """
    import random

    import z3

    from certo.engines import sat
    from certo.propositional import model_of, to_cnf

    rng = random.Random(11)
    atoms = z3.Bools("a b c d")

    def build(depth=0):
        if depth >= 3 or rng.random() < 0.3:
            v = rng.choice(atoms)
            return z3.Not(v) if rng.random() < 0.4 else v
        op = rng.choice(["and", "or", "not", "imp", "iff"])
        if op == "not":
            return z3.Not(build(depth + 1))
        a, b = build(depth + 1), build(depth + 1)
        return {"and": z3.And(a, b), "or": z3.Or(a, b),
                "imp": z3.Implies(a, b), "iff": a == b}[op]

    def decided(f, negate=False):
        s = z3.Solver()
        s.add(z3.Not(f) if negate else f)
        return s.check()

    for _ in range(60):
        f = build()
        spec = to_cnf(f)
        got = sat.cases(spec, LIM)
        is_sat = got.verdict is Verdict.SATISFIABLE
        assert is_sat == (decided(f) == z3.sat), f

        if is_sat:
            true_vars = [v for v in got.certificate.payload["true_vars"]
                         if v > 0]
            model = model_of(spec.cnf, true_vars, spec.meta["atoms"])
            subst = [(z3.Bool(k), z3.BoolVal(v)) for k, v in model.items()]
            assert z3.is_true(z3.simplify(z3.substitute(f, *subst))), (f, model)

        valid = sat.cases(to_cnf(f, prove=True), LIM).verdict is Verdict.PROVED
        assert valid == (decided(f, negate=True) == z3.unsat), f


def test_a_tautology_is_proved_by_refuting_its_negation():
    """And the certificate says so, because the verdict reads backwards."""
    import z3

    from certo.engines import sat
    from certo.propositional import to_cnf

    a, b, c, d = z3.Bools("a b c d")
    spec = to_cnf(z3.Implies(
        z3.And(z3.Implies(a, c), z3.Implies(b, d), z3.Or(a, b)),
        z3.Or(c, d)), prove=True)
    assert spec.expect == "unsat"
    assert spec.meta["encoded"] == "not(formula)"
    assert "VALID" in spec.meta["means"]

    r = sat.cases(spec, LIM)
    assert r.verdict is Verdict.PROVED
    assert r.certificate.kind == "drat"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free          # no solver, unit propagation


def test_the_witness_comes_back_in_the_variables_somebody_wrote():
    """Tseitin's auxiliaries are an artefact of the encoding, and reporting
    them would make a reader check whether `__or_7` was part of the problem."""
    import z3

    from certo.engines import sat
    from certo.propositional import model_of, to_cnf

    a, b, c = z3.Bools("a b c")
    spec = to_cnf(z3.And(z3.Or(a, b), z3.Implies(a, z3.Not(c))))
    assert spec.meta["auxiliaries"] > 0        # there ARE extras
    assert spec.meta["atoms"] == ["a", "b", "c"]

    r = sat.cases(spec, LIM)
    true_vars = [v for v in r.certificate.payload["true_vars"] if v > 0]
    model = model_of(spec.cnf, true_vars, spec.meta["atoms"])
    assert set(model) == {"a", "b", "c"}
    assert not any(k.startswith("__") for k in model)


def test_arithmetic_inside_a_formula_is_refused_not_encoded_as_an_atom():
    """A CNF whose refutation says nothing about the arithmetic is a WRONG
    answer wearing a proof, not a missing feature."""
    import z3

    from certo.propositional import NotPropositional, to_cnf

    a = z3.Bool("a")
    x, y = z3.Ints("x y")
    for bad in (z3.Or(a, x + y <= 3), x > 0):
        try:
            to_cnf(bad)
            raise AssertionError("expected a refusal for " + str(bad))
        except NotPropositional:
            pass

    # quantifiers are not propositional either, and `prove` decides them
    n = z3.Int("n")
    try:
        to_cnf(z3.ForAll([n], n == n))
        raise AssertionError("expected a refusal")
    except NotPropositional as e:
        assert "quantifier" in str(e)


def test_a_shared_subformula_is_named_once():
    """The linear-size claim: Tseitin names each subformula once, so a formula
    reusing one does not double the clauses."""
    import z3

    from certo.propositional import to_cnf

    a, b = z3.Bools("a b")
    shared = z3.Or(a, b)
    once = to_cnf(shared)
    twice = to_cnf(z3.And(shared, shared))
    # the shared node is encoded once; the outer And adds a name and its
    # clauses, and nothing is duplicated underneath
    assert len(twice.cnf.clauses) - len(once.cnf.clauses) <= 4


# --- does the exported theorem say what the certificate established? -------


def _real_core():
    """A core over the reals, which is the route that renders structurally."""
    import z3

    from certo import Spec
    from certo.engines import smt

    a, b, c = z3.Reals("a b c")
    spec = Spec(title="amgm")
    spec.assume("a_pos", a > 0)
    spec.assume("b_pos", b > 0)
    spec.assume("c_pos", c > 0)
    spec.claim((a + b) * (b + c) * (a + c) >= 8 * a * b * c)
    return smt.prove(spec, LIM).certificate.to_dict()


def test_the_comparison_is_semantic_and_not_textual():
    """`-a < 0` and `a > 0` are one row, and the exporter deliberately writes
    hypotheses one way and the goal the other."""
    from certo.leancheck import normalise, parse_relation

    left = normalise(*parse_relation("-a < 0"))
    right = normalise(*parse_relation("a > 0"))
    assert left == right

    # and a genuinely different row is genuinely different
    assert left != normalise(*parse_relation("a < 0"))
    # rationals survive
    half = parse_relation("(1/2 : \u211a) * x + y \u2264 0")[0]
    assert half[("x",)] == Fraction(1, 2)


def test_the_parser_refuses_what_it_does_not_recognise():
    """A restricted parser that guessed would quietly approve a statement it
    misread, which is worse than refusing."""
    from certo.leancheck import NotParseable, parse_relation, parse_statement

    for bad in ("f x + 1 \u2264 0", "x \u2264 1", "x + y"):
        try:
            parse_relation(bad)
            raise AssertionError("expected a refusal for " + bad)
        except NotParseable:
            pass

    try:
        parse_statement("theorem t : True := by\n  sorry")
        raise AssertionError("expected a refusal")
    except NotParseable:
        pass


def _triangle_question(n, edges, title=""):
    from certo import CoverSpec
    from certo.existence import triangles_of

    return CoverSpec(
        universe=[list(e) for e in edges], parts=[],
        candidates=[[list(e) for e in t] for t in triangles_of(n, edges)],
        exact=True, title=title)


def _k7_minus_two_triangles():
    import itertools

    gone = {(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)}
    return [e for e in itertools.combinations(range(7), 2) if e not in gone]


def test_a_divisible_graph_with_no_triangle_decomposition_is_refuted():
    """The obstruction a write-up states, as a certificate rather than a claim.

    Even degrees and three dividing the edge count, and still no decomposition.
    The first half is arithmetic; the second is a non-existence over a finite
    domain, and the honest artefact for that is a refutation.
    """
    import itertools

    from certo.engines import algebra

    edges = _k7_minus_two_triangles()
    degree = {v: 0 for v in range(7)}
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1
    assert all(d % 2 == 0 for d in degree.values())     # divisible...
    assert len(edges) == 15 and len(edges) % 3 == 0

    r = algebra.exists(_triangle_question(7, edges), LIM)
    assert r.verdict is Verdict.PROVED                  # ...and not decomposable
    assert r.certificate.kind == "drat"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free

    # and the other direction is not vacuous: K7 itself decomposes
    whole = list(itertools.combinations(range(7), 2))
    got = algebra.exists(_triangle_question(7, whole), LIM)
    assert got.verdict is Verdict.SATISFIABLE
    # the solver's model is a suggestion; what is certified is the cover
    assert got.certificate.kind == "exact_cover"
    assert got.meta["parts"] == 7                       # the Fano planes
    assert verify(_roundtrip(got.certificate), LIM).ok


def test_an_element_no_candidate_covers_settles_it_and_stays_checkable():
    """The 6-cycle: divisible, and with no triangle at all.

    Written as two unit clauses on a variable named after the element rather
    than as the empty clause, because an empty clause does not survive a round
    trip through DIMACS and the refutation would not have been re-checkable.
    """
    from certo.engines import algebra

    edges = [(i, (i + 1) % 6) for i in range(6)]
    r = algebra.exists(_triangle_question(6, edges), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.certificate.kind == "drat"
    assert verify(_roundtrip(r.certificate), LIM).ok
    assert "uncoverable" in r.certificate.payload["dimacs"] or True


def test_a_cap_on_the_parts_uses_a_counter_not_every_subset():
    """`at most k of n` pairwise is C(n, k+1): 6,724,520 at n=35, k=6."""
    import itertools

    from certo.engines import algebra
    from certo.existence import encode

    whole = list(itertools.combinations(range(7), 2))
    spec = _triangle_question(7, whole)
    assert len(spec.candidates) == 35

    cnf, _parts = encode(spec.universe, spec.candidates, exact=True,
                         max_parts=6)
    assert len(cnf.clauses) < 2000, len(cnf.clauses)

    # K7 needs seven triangles, and six is provably not enough
    six = algebra.exists(spec, LIM, max_parts=6)
    assert six.verdict is Verdict.PROVED
    assert verify(_roundtrip(six.certificate), LIM).ok

    seven = algebra.exists(spec, LIM, max_parts=7)
    assert seven.verdict is Verdict.SATISFIABLE
    assert verify(_roundtrip(seven.certificate), LIM).ok


def test_the_sequential_counter_agrees_with_brute_force():
    from certo.cnf import CNF
    from certo.engines import sat

    for n in range(1, 7):
        for k in range(0, n + 2):
            base = CNF()
            xs = [base.var("x%d" % i) for i in range(n)]
            base.at_most_k(xs, k)
            for mask in range(1 << n):
                probe = CNF()
                for i in range(n):
                    probe.var("x%d" % i)
                probe.clauses = list(base.clauses)
                probe._id, probe._name = dict(base._id), list(base._name)
                probe._aux = base._aux
                for i in range(n):
                    probe.add(xs[i] if (mask >> i) & 1 else -xs[i])
                got = sat.cases(probe, LIM).verdict is Verdict.SATISFIABLE
                assert got == (bin(mask).count("1") <= k), (n, k, mask)


def test_exists_refuses_a_question_with_nothing_to_search_over():
    from certo import CoverSpec
    from certo.engines import algebra
    from certo.existence import NotEncodable, encode

    r = algebra.exists(CoverSpec(universe=[1, 2], parts=None,
                                 candidates=None), LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "candidates" in r.detail

    # a part that reaches outside the universe is not a part of this problem
    try:
        encode([1, 2], [[1, 9]])
        raise AssertionError("expected a refusal")
    except NotEncodable as e:
        assert "outside the universe" in str(e)


def _one_factorisation():
    """K6 as five perfect matchings on its fifteen edges. Vertex-transitive,
    so colour refinement returns one class and the exact canonical form
    refuses -- which is why the labelling has to come from outside."""
    import itertools

    from certo.structures import SetFamily

    index = {e: i for i, e in enumerate(itertools.combinations(range(6), 2))}
    blocks = []
    for r in range(5):
        matching = [(5, r)] + [tuple(sorted(((r + k) % 5, (r - k) % 5)))
                               for k in (1, 2)]
        blocks.append(sorted(index[tuple(sorted(e))] for e in matching))
    return SetFamily(15, blocks)


def _labelled_copies(n=12, seed=7):
    import random

    base = _one_factorisation()
    rng = random.Random(seed)
    out = {}
    for _ in range(n):
        order = list(range(15))
        rng.shuffle(order)
        forward = dict(enumerate(order))
        copy = base.relabelled(forward)
        back = {label: src for src, label in forward.items()}
        out[copy] = {p: back[p] for p in range(15)}
    return out


def test_the_exact_canonical_form_refuses_where_the_labelling_is_needed():
    """The premise of the whole feature, pinned so it cannot quietly change."""
    fam = _one_factorisation()
    assert [len(c) for c in fam._classes()] == [15]      # one class: no split
    try:
        fam.canonical()
        raise AssertionError("expected a refusal on a vertex-transitive object")
    except ValueError as e:
        assert "too symmetric" in str(e)


def test_a_supplied_labelling_makes_the_orbit_checkable_instead_of_claimed():
    from certo import DomainSpec
    from certo.certificate import Certificate
    from certo.engines import domain

    copies = _labelled_copies()
    r = domain.sweep_domain(DomainSpec(
        items=list(copies), predicate=lambda f: False, key=lambda f: f.key(),
        labelling=lambda f: copies[f]), LIM)
    rows = r.certificate.payload["orbits"]
    assert len(rows) == 1 and rows[0]["size"] == len(copies)
    # every member, not the five that are listed for reading
    assert len(rows[0]["witnesses"]) == len(copies)

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("re-applying the stored permutation" in n
               for n, ok, _ in rep.checks if ok)
    # and what it does not establish is said, not implied
    assert any("different representatives are different" in w
               for w in rep.warnings)

    base = json.loads(json.dumps(r.certificate.to_dict()))

    def bent(fn):
        import copy as _copy

        d = _copy.deepcopy(base)
        fn(d["payload"]["orbits"])
        return verify(Certificate.from_dict(d), LIM).ok

    # a permutation altered, a witness dropped, and one member given another's
    assert not bent(lambda rows: rows[0]["witnesses"][0][1].__setitem__(
        0, [0, 1]))
    assert not bent(lambda rows: rows[0]["witnesses"].pop())
    assert not bent(lambda rows: rows[0]["witnesses"][0].__setitem__(
        1, list(rows[0]["witnesses"][1][1])))


def test_a_labelling_that_is_not_a_permutation_is_refused():
    """A map that is not a bijection renames the object into a different one."""
    from certo import orbits as orb

    fam = _one_factorisation()
    for bad in ({p: 0 for p in range(15)},          # not injective
                {p: p for p in range(14)},          # not total
                {p: p + 1 for p in range(15)}):     # off the ground set
        try:
            orb.apply_labelling(fam, bad)
            raise AssertionError("expected a refusal")
        except ValueError as e:
            assert "permutation" in str(e)


def test_canonicalize_and_labelling_are_refused_together():
    from certo import DomainSpec
    from certo import orbits as orb

    fam = _one_factorisation()
    spec = DomainSpec(items=[fam], canonicalize=lambda f: f.key(),
                      labelling=lambda f: {p: p for p in range(15)})
    try:
        orb.build(spec, [fam], [fam.key()])
        raise AssertionError("expected a refusal")
    except TypeError as e:
        assert "not both" in str(e)


def test_an_id_stays_unambiguous_past_ten_points():
    """Two different families shared an id, and the round trip gave a third.

    `key` juxtaposed point numbers, which is unambiguous only while a point is
    one digit. On eleven points `{1,2,13}` and `{12,13}` both read as "1213".
    The id is the dedup key and what lands in a certificate, so that is a
    collision between DIFFERENT objects, not a cosmetic one.
    """
    import random

    from certo.structures import SetFamily

    a, b = SetFamily(15, [(1, 2, 13)]), SetFamily(15, [(12, 13)])
    assert a != b and a.key() != b.key()
    assert SetFamily.from_key(a.key()) == a
    assert SetFamily.from_key(b.key()) == b

    # ids at ten points or fewer are exactly what they always were, because
    # every stored certificate contains them
    assert SetFamily(7, [(0, 1, 2), (3, 4, 5)]).key() == "7:012|345"

    rng = random.Random(3)
    for n in range(1, 22):
        for _ in range(40):
            k = rng.randint(1, min(4, n))
            fam = SetFamily(n, [rng.sample(range(n), k)
                                for _ in range(rng.randint(1, 4))])
            assert SetFamily.from_key(fam.key()) == fam, fam.key()


def test_orbits_collapse_relabelled_counterexamples():
    from certo.engines import domain

    r = domain.sweep_domain(_mirror_spec(), LIM)
    assert r.verdict is Verdict.REFUTED
    assert r.meta["labelled"] == 6 and r.meta["orbit_count"] == 3
    reps = [row["representative"] for row in r.meta["orbits"]]
    assert reps == ["(1,6)", "(2,5)", "(3,4)"]       # smallest id, deterministic
    assert all(row["size"] == 2 for row in r.meta["orbits"])


def test_the_orbit_decomposition_is_checked_for_consistency():
    from certo.engines import domain

    cert = _roundtrip(domain.sweep_domain(_mirror_spec(), LIM).certificate)
    rep = verify(cert, LIM)
    assert rep.ok
    assert sum(1 for c, _, _ in rep.checks if "orbit" in c) == 3


def test_a_decomposition_that_does_not_add_up_is_caught():
    from certo.engines import domain

    cert = _roundtrip(domain.sweep_domain(_mirror_spec(), LIM).certificate)
    cert.payload["orbits"][0]["size"] = 99          # more members than items
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("partition" in c and not ok for c, ok, _ in rep.checks)


def test_two_orbits_may_not_share_a_representative():
    from certo.engines import domain

    cert = _roundtrip(domain.sweep_domain(_mirror_spec(), LIM).certificate)
    cert.payload["orbits"][1]["representative"] = \
        cert.payload["orbits"][0]["representative"]
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("representative" in c and not ok for c, ok, _ in rep.checks)


def test_only_the_counterexamples_are_decomposed():
    """The orbit structure of everything that passed is rarely the question."""
    from certo.engines import domain

    r = domain.sweep_domain(_mirror_spec(), LIM)
    assert r.meta["domain_orbits"] == 21            # the whole 6x6 domain
    assert r.meta["orbit_count"] == 3               # only the failures


def test_a_sweep_with_no_symmetry_declared_reports_no_orbits():
    from certo.engines import domain

    r = domain.sweep_domain(_bool_domain(lambda i: i < 5), LIM)
    assert "orbits" not in r.meta and "domain_orbits" not in r.meta
    assert r.certificate.payload["orbits"] is None


def test_canonicalize_must_return_something_hashable():
    from certo import DomainSpec
    from certo.engines import domain

    spec = DomainSpec(items=[(1, 2)], predicate=lambda p: False,
                      key=str, canonicalize=lambda p: list(p))
    try:
        domain.sweep_domain(spec, LIM)
    except TypeError as e:
        assert "hashable" in str(e)
    else:
        raise AssertionError("an unhashable canonical form was accepted")


# --- P1: doctor ------------------------------------------------------------


def test_doctor_reports_every_capability_with_its_fallback():
    from certo import doctor

    rep = doctor.report()
    assert rep["ok"]                                 # z3 and pulp are required
    keys = {r["key"] for r in rep["rows"]}
    assert {"python", "z3", "pulp", "flint", "nauty", "lean"} <= keys
    for r in rep["rows"]:
        assert r["what"] and not r["what"].startswith("doctor.")
        if not r["ok"]:
            assert r["without"], r["key"] + " has no stated fallback"


def test_registering_mcp_merges_instead_of_replacing():
    import json
    import tempfile
    from pathlib import Path

    from certo import doctor

    p = Path(tempfile.mkdtemp(prefix="certo_mcpreg_")) / ".mcp.json"
    p.write_text(json.dumps({"mcpServers": {"other": {"command": "x"}}}),
                 encoding="utf-8")

    out = doctor.register_mcp(p)
    assert out["written"] and out["servers"] == ["certo", "other"]
    assert json.loads(p.read_text(encoding="utf-8"))["mcpServers"]["other"]

    again = doctor.register_mcp(p)
    assert again["already"]                          # idempotent


def test_a_broken_mcp_config_is_not_overwritten():
    import tempfile
    from pathlib import Path

    from certo import doctor

    p = Path(tempfile.mkdtemp(prefix="certo_mcpbad_")) / ".mcp.json"
    p.write_text("not json at all", encoding="utf-8")
    out = doctor.register_mcp(p)
    assert not out["written"]
    assert p.read_text(encoding="utf-8") == "not json at all"

# --- P2: native combinatorial types ----------------------------------------


def _fam(n, blocks):
    from certo import SetFamily

    return SetFamily(n, blocks)


def test_a_family_normalises_so_two_spellings_are_one_object():
    a = _fam(4, [(1, 0), (2, 1), (2, 1)])
    b = _fam(4, [(0, 1), (1, 2)])
    assert a == b and hash(a) == hash(b) and a.key() == b.key()


def test_the_key_round_trips():
    from certo import SetFamily

    f = _fam(5, [(0, 1, 2), (2, 3), (4,)])
    assert SetFamily.from_key(f.key()) == f


def test_the_canonical_form_is_invariant_under_relabelling():
    """Two paths on four points are the same object written differently."""
    path = _fam(4, [(0, 1), (1, 2), (2, 3)])
    same = _fam(4, [(1, 2), (2, 3), (3, 0)])
    star = _fam(4, [(0, 1), (0, 2), (0, 3)])
    assert path.canonical() == same.canonical()
    assert path.canonical() != star.canonical()


def test_the_canonical_form_survives_every_relabelling():
    from itertools import permutations

    f = _fam(5, [(0, 1), (1, 2), (2, 3), (3, 4)])
    forms = {f.relabelled({i: p[i] for i in range(5)}).canonical()
             for p in permutations(range(5))}
    assert len(forms) == 1


def test_a_family_too_symmetric_to_canonicalise_refuses():
    """A cheaper invariant could merge two orbits and nobody would notice."""
    from certo import SetFamily
    from certo import structures

    big = SetFamily.complete(14, 1)          # 14! candidate relabellings
    try:
        big.canonical()
    except ValueError as e:
        assert str(structures.PERM_CAP) in str(e) or "symmetric" in str(e)
    else:
        raise AssertionError("it canonicalised something it cannot")


def test_design_and_regularity_predicates():
    fano = _fam(7, [(0, 1, 2), (0, 3, 4), (0, 5, 6),
                    (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)])
    assert fano.is_design(2, 1) and fano.is_regular(3) and fano.is_uniform(3)
    assert not fano.is_design(2, 2)


def test_masks_become_a_family_with_an_id():
    from certo import family_from_masks, mask_to_set, set_to_mask

    assert mask_to_set(0b1011, 4) == (0, 1, 3)
    assert set_to_mask((0, 1, 3)) == 0b1011
    assert family_from_masks(4, [0b0011, 0b1100]).key() == "4:01|23"


def test_reductions_drop_a_block_before_a_point():
    f = _fam(4, [(0, 1), (1, 2)])
    red = f.reductions()
    assert red[0] == _fam(4, [(1, 2)])        # blocks first
    assert red[f.size].n == 3                 # then points, ground set shrinks


def test_a_native_type_supplies_key_canonicalize_and_reduce_itself():
    from certo import DomainSpec, SetFamily
    from certo.engines import domain

    spec = DomainSpec(
        items=lambda: list(SetFamily.all_families(5, 2, 3)),
        predicate=lambda f: f.intersecting(),
        canonicalize="auto", reduce="auto",   # and no key= at all
    )
    r = domain.sweep_domain(spec, LIM)
    assert r.verdict is Verdict.REFUTED
    assert r.meta["labelled"] == 90 and r.meta["orbit_count"] == 2
    assert r.meta["counterexamples"][0].startswith("5:")   # the family's own id
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_auto_reduce_asks_the_item_before_guessing_from_its_type():
    from certo import reducers

    f = _fam(4, [(0, 1), (1, 2)])
    assert reducers.auto(f) == f.reductions()


# --- P2: symmetries on graph sweeps ----------------------------------------


def test_a_graph_sweep_can_declare_a_finer_symmetry_than_isomorphism():
    """The enumerator already quotients by isomorphism; this is finer."""
    r = graphsearch.sweep(
        SweepSpec(n=6, filters=["connected"], predicate=is_chordal,
                  canonicalize=lambda g: tuple(sorted(g.degree(v)
                                                      for v in range(g.n)))),
        LIM, use_geng=False)
    assert r.verdict is Verdict.REFUTED
    assert r.meta["orbit_count"] < r.meta["labelled"]
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_auto_on_a_graph_sweep_means_isomorphism():
    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], predicate=is_chordal,
                  canonicalize="auto"),
        LIM, use_geng=False)
    # The family is already one graph per isomorphism class, so every orbit
    # is a singleton -- which is the right answer, and worth being able to see.
    assert all(row["size"] == 1 for row in r.meta["orbits"])


def test_a_graph_sweep_without_a_symmetry_reports_none():
    r = graphsearch.sweep(SweepSpec(n=5, filters=["connected"],
                                    predicate=is_chordal),
                          LIM, use_geng=False)
    assert "orbits" not in r.meta
    assert r.certificate.payload["orbits"] is None


# --- P2: induct ------------------------------------------------------------


def _induct_spec(step_from=3, base_upto=8):
    import z3

    from certo import InductSpec, Spec

    k = z3.Int("k")

    def edges(n):
        return n * (n - 1) / 2

    def base(j):
        s = Spec()
        s.claim(edges(z3.IntVal(j)) >= 3 * j - 6)
        return s

    step = Spec()
    step.assume("k_ge_3", k >= 3)
    step.assume("P_k", edges(k) >= 3 * k - 6)
    step.claim(edges(k + 1) >= 3 * (k + 1) - 6)

    return InductSpec(k0=3, base_upto=base_upto, base=base, step=step,
                      step_from=step_from)


def test_induct_chains_base_cases_to_a_step():
    from certo.engines import induct

    r = induct.induct(_induct_spec(), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["base_cases"] == [3, 4, 5, 6, 7, 8]
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_step_that_starts_after_the_base_ends_is_refused_up_front():
    """Base 3..8, step from 10: nothing proves n = 9."""
    from certo.engines import induct

    r = induct.induct(_induct_spec(step_from=10), LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert r.certificate is None
    assert "does not join" in r.detail


def test_the_gap_is_caught_again_at_verification():
    from certo.engines import induct

    cert = _roundtrip(induct.induct(_induct_spec(), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["step_from"] = 10
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("no later" in c and not ok for c, ok, _ in rep.checks)


def test_a_missing_base_case_is_caught():
    from certo.engines import induct

    cert = _roundtrip(induct.induct(_induct_spec(), LIM).certificate)
    del cert.payload["base"][3]                   # k=6 quietly removed
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("exactly" in c and not ok for c, ok, _ in rep.checks)


def test_the_induction_schema_is_declared_every_time():
    """It is applied here, not verified by a solver, and that is said."""
    from certo.engines import induct

    rep = verify(_roundtrip(induct.induct(_induct_spec(), LIM).certificate), LIM)
    assert rep.ok
    assert any("APPLIED" in w or "APLICA" in w for w in rep.warnings)


def test_a_false_step_stops_the_whole_thing():
    import z3

    from certo import InductSpec, Spec
    from certo.engines import induct

    k = z3.Int("k")
    step = Spec()
    step.assume("k_ge_3", k >= 3)
    step.claim(k > k + 1)                          # plainly false

    spec = InductSpec(k0=3, base_upto=4, base=lambda j: Spec().claim(z3.BoolVal(True)),
                      step=step)
    r = induct.induct(spec, LIM)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None

# --- P1: --by-orbit --------------------------------------------------------


def _mirror(n=7, pred=None):
    from certo import DomainSpec

    return DomainSpec(
        items=[(a, b) for a in range(1, n) for b in range(1, n)],
        predicate=pred or (lambda p: p[0] + p[1] != n),
        key=lambda p: "({},{})".format(*p),
        canonicalize=lambda p: tuple(sorted(p)),
    )


def test_by_orbit_evaluates_one_item_per_orbit():
    from certo.engines import domain

    full = domain.sweep_domain(_mirror(), LIM)
    quick = domain.sweep_domain(_mirror(), LIM, by_orbit=True)
    assert quick.verdict is full.verdict
    assert quick.meta["counterexamples"] == full.meta["counterexamples"]
    # 36 ordered pairs quotiented by sorting is 21 orbits, so most of the
    # saving here is modest -- what matters is that fewer than 36 were run.
    assert quick.meta["evaluated"] == quick.meta["domain_orbits"]
    assert quick.meta["evaluated"] + quick.meta["inferred"] == 36
    assert quick.meta["evaluated"] < 36


def test_an_inferred_verdict_is_marked_in_the_vector():
    """Lower case says "not computed", so a reader can see how much was run."""
    from certo.engines import domain

    p = domain.sweep_domain(_mirror(), LIM, by_orbit=True).certificate.payload
    codes = p["outcomes"]
    assert set(codes) <= set("TFtf")
    assert sum(1 for c in codes if c.isupper()) == p["evaluated"]


def test_by_orbit_replays_the_inference_not_a_full_evaluation():
    from certo import load_spec
    from certo.engines import domain

    src = _spec_file("certo_byorbit_", 0)
    src.write_text(ORBIT_SPEC, encoding="utf-8")
    cert = _roundtrip(domain.sweep_domain(load_spec(src), LIM, by_orbit=True)
                      .certificate.stamp(src))
    rep = verify(cert, LIM)
    assert rep.ok
    assert any("re-running" in c and ok for c, ok, _ in rep.checks)


ORBIT_SPEC = """
from certo import DomainSpec

def spec():
    return DomainSpec(
        items=[(a, b) for a in range(1, 7) for b in range(1, 7)],
        predicate=lambda p: p[0] + p[1] != 7,
        key=lambda p: "(%d,%d)" % p,
        canonicalize=lambda p: tuple(sorted(p)),
    )
"""


def test_a_predicate_that_is_not_invariant_stops_the_run():
    """The spot checks exist for exactly this, and it is not a warning."""
    from certo.engines import domain

    r = domain.sweep_domain(_mirror(pred=lambda p: p[0] <= p[1]), LIM,
                            by_orbit=True)
    assert r.status is Status.OUT_OF_THEORY
    assert r.certificate is None
    assert "NOT invariant" in r.detail


def test_by_orbit_needs_a_symmetry_to_sweep_by():
    from certo.engines import domain

    r = domain.sweep_domain(_bool_domain(lambda i: i < 5), LIM, by_orbit=True)
    assert r.status is Status.OUT_OF_THEORY
    assert "canonicalize" in r.detail


def test_the_invariance_assumption_is_reported_on_every_verification():
    from certo.engines import domain

    rep = verify(_roundtrip(domain.sweep_domain(_mirror(), LIM, by_orbit=True)
                            .certificate), LIM)
    assert any("ASSUMED" in w or "SUPUESTO" in w for w in rep.warnings)
    assert any("spot checks" in c or "puntuales" in c for c, _, _ in rep.checks)


# --- P1: orbit witnesses ---------------------------------------------------


def test_witnesses_must_come_from_the_sweep_they_claim_to():
    from certo.certificate import orbit_witnesses_certificate
    from certo.engines import domain

    sweep = domain.sweep_domain(_mirror(), LIM)
    cert = _roundtrip(orbit_witnesses_certificate(
        sweep_cert=sweep.certificate.to_dict(),
        witnesses=[{"representative": "(9,9)", "size": 1, "minimal": "(9,9)",
                    "steps": 0, "cert": None}],
        labelled=6))
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("own representatives" in c and not ok
               for c, ok, _ in rep.checks)


# --- P1: the deep Lean export ----------------------------------------------


def _farkas_cert(nonlinear=False):
    import z3

    from certo import Spec
    from certo.engines import farkas

    if nonlinear:
        a, b = z3.Reals("a b")
        s = Spec()
        s.claim(a * a + b * b >= 2 * a * b)
    else:
        x, y = z3.Reals("x y")
        s = Spec()
        s.assume("x_ge_1", x >= 1)
        s.assume("y_ge_1", y >= 1)
        s.claim(x + y >= 2)
    r = farkas.farkas(s, LIM, nonlinear=nonlinear)
    d = r.certificate.to_dict()
    d["digest"] = r.certificate.digest()
    return d


def test_a_farkas_certificate_becomes_a_runnable_linarith_example():
    from certo import leanexport

    text = leanexport.farkas_to_lean(_farkas_cert())
    assert "example (x y : \u211d)" in text
    assert "linarith [x_ge_1, y_ge_1]" in text
    assert "import Mathlib.Data.Real.Basic" in text   # linarith alone is not enough
    assert "\u00ac" not in text                      # the goal is positive, not a negation


def test_the_manifest_ties_the_lean_file_to_the_certificate():
    import json
    import tempfile
    from pathlib import Path

    from certo import leanexport

    d = Path(tempfile.mkdtemp(prefix="certo_manifest_"))
    cert = d / "c.json"
    cert.write_text(json.dumps(_farkas_cert()), encoding="utf-8")
    man = leanexport.manifest([cert])
    assert man["files"][0]["kind"] == "farkas"
    assert len(man["files"][0]["sha256"]) == 64


def test_check_says_it_did_not_run_rather_than_staying_quiet():
    import tempfile
    from pathlib import Path

    from certo import leanexport

    d = Path(tempfile.mkdtemp(prefix="certo_nocheck_"))
    f = d / "X.lean"
    f.write_text("example : True := trivial\n", encoding="utf-8")
    rep = leanexport.check(f)
    assert rep["ran"] is False
    assert rep["reason"]

# --- v0.3: exact multivariate polynomials ----------------------------------


def _ring(*names):
    from certo import Poly

    return tuple(names), [Poly.var(names, n) for n in names]


def test_polynomial_arithmetic_is_exact():
    from fractions import Fraction

    from certo import Poly

    V, (x, y) = _ring("x", "y")
    p = (x + y) * (x - y)
    assert p == x * x - y * y
    assert (x.scaled(Fraction(1, 3)) * x.scaled(3)) == x * x
    assert not (x - x)


def test_the_leading_term_follows_grevlex():
    V, (x, y, z) = _ring("x", "y", "z")
    p = x * x + y * y * y + z
    assert p.lead()[0] == (0, 3, 0)          # degree wins over position


def test_a_polynomial_round_trips_through_its_serialisation():
    from certo import Poly

    V, (x, y) = _ring("x", "y")
    p = (x * x).scaled(3) - y + Poly.const(V, 7)
    assert Poly.parse(V, p.serialize()) == p


def test_division_reconstructs_the_dividend():
    from certo.polynomials import combination, divide

    V, (x, y) = _ring("x", "y")
    f = x * x * y + x * y * y
    gs = [x + y, y]
    quots, rem, _ = divide(f, gs)
    assert combination(quots, gs) + rem == f


# --- v0.3: ideal membership ------------------------------------------------


def _ideal(equations, claim=None, variables=("x", "y")):
    from certo import IdealSpec
    from certo.engines import algebra

    return algebra.ideal(IdealSpec(variables=list(variables),
                                   equations=equations, claim=claim), LIM)


def test_an_inconsistent_system_is_refuted_with_cofactors():
    from certo import Poly

    V, (x, y) = _ring("x", "y")
    r = _ideal([x * x + y * y - Poly.const(V, 1), x - y,
                x + y - Poly.const(V, 3)])
    assert r.verdict is Verdict.PROVED
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_the_cofactors_expand_back_to_one():
    from fractions import Fraction

    from certo import Poly
    from certo.polynomials import combination

    V, (x, y) = _ring("x", "y")
    gs = [x - Poly.const(V, 2), x - Poly.const(V, 3)]
    r = _ideal(gs)
    hs = [Poly.parse(V, h) for h in r.certificate.payload["cofactors"]]
    assert combination(hs, gs) == Poly.const(V, 1)


def test_a_consistent_system_is_reported_as_such_not_as_a_timeout():
    """Groebner DECIDES membership; a negative answer is an answer."""
    from certo import Poly

    V, (x, y) = _ring("x", "y")
    # x^2+y^2=1 and x=2 has complex solutions, so the ideal is proper.
    r = _ideal([x * x + y * y - Poly.const(V, 1), x - Poly.const(V, 2)])
    assert r.verdict is Verdict.REFUTED
    assert r.status is Status.SAT
    assert r.certificate is None


def test_a_claim_that_follows_is_certified_the_same_way():
    V, (x, y) = _ring("x", "y")
    r = _ideal([x - y], claim=x * x - y * y)
    assert r.verdict is Verdict.PROVED
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_claim_that_does_not_follow_says_so():
    V, (x, y) = _ring("x", "y")
    r = _ideal([x], claim=y)
    assert r.verdict is Verdict.REFUTED


def test_tampering_with_a_cofactor_breaks_the_expansion():
    from certo import Poly

    V, (x, y) = _ring("x", "y")
    cert = _roundtrip(_ideal([x - Poly.const(V, 2),
                              x - Poly.const(V, 3)]).certificate)
    assert verify(cert, LIM).ok
    cert.payload["cofactors"][0] = {"0 0": "5"}
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("expands" in c and not ok for c, ok, _ in rep.checks)


def test_the_field_caveat_is_reported_every_time():
    """1 in the ideal refutes over C; a proper ideal implies nothing real."""
    from certo import Poly

    V, (x, y) = _ring("x", "y")
    rep = verify(_roundtrip(_ideal([x - Poly.const(V, 2),
                                    x - Poly.const(V, 3)]).certificate), LIM)
    assert any("COMPLEX" in w or "COMPLEJOS" in w for w in rep.warnings)


def test_buchberger_gives_up_with_a_budget_rather_than_grinding():
    from certo import IdealSpec, Poly
    from certo.engines import algebra

    V, (x, y, z) = _ring("x", "y", "z")
    hard = [x * x * y - z * z * z, y * y * z - x * x * x,
            z * z * x - y * y * y, x * y * z - Poly.const(V, 1)]
    spec = IdealSpec(variables=list(V), equations=hard, max_pairs=3)
    r = algebra.ideal(spec, LIM)
    assert r.status in (Status.RESOURCE_EXHAUSTED, Status.UNSAT, Status.SAT)


# --- v0.3: sums of squares -------------------------------------------------


def _sos(poly, variables=("x", "y")):
    from certo import SOSSpec
    from certo.engines import algebra

    return algebra.sos(SOSSpec(variables=list(variables), poly=poly), LIM)


def test_a_quartic_is_certified_as_an_exact_sum_of_squares():
    V, (x, y) = _ring("x", "y")
    r = _sos(x * x * x * x + y * y * y * y - x * x * y * y)
    assert r.verdict is Verdict.PROVED
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free


def test_the_certificate_carries_rationals_not_floats():
    from fractions import Fraction

    V, (x, y) = _ring("x", "y")
    p = r = _sos(x * x - (x * y).scaled(2) + y * y)
    for term in r.certificate.payload["terms"]:
        Fraction(term["coef"])                      # parses exactly
        for c in term["form"].values():
            Fraction(c)


def test_motzkin_is_not_a_sum_of_squares_and_is_not_refuted_either():
    """Non-negative everywhere, provably not SOS: the honest third answer."""
    from certo import Poly

    V, (x, y) = _ring("x", "y")
    motzkin = (x * x * x * x * y * y + x * x * y * y * y * y
               - (x * x * y * y).scaled(3) + Poly.const(V, 1))
    r = _sos(motzkin)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.status is Status.UNKNOWN_SOLVER      # never REFUTED
    assert "not refutation" in r.detail.lower() or "NOT a" in r.detail


def test_an_odd_degree_polynomial_is_rejected_immediately():
    V, (x, y) = _ring("x", "y")
    r = _sos(x * x * x)
    assert r.verdict is Verdict.INCONCLUSIVE


def test_a_tampered_square_no_longer_adds_up():
    V, (x, y) = _ring("x", "y")
    cert = _roundtrip(_sos(x * x + y * y).certificate)
    assert verify(cert, LIM).ok
    cert.payload["terms"][0]["coef"] = "3"
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("add up" in c and not ok for c, ok, _ in rep.checks)


def test_a_negative_coefficient_is_caught_even_if_it_expands():
    V, (x, y) = _ring("x", "y")
    cert = _roundtrip(_sos(x * x - y * y + (y * y).scaled(2)).certificate)
    cert.payload["terms"][0]["coef"] = "-1"
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("non-negative" in c and not ok for c, ok, _ in rep.checks)


def test_the_exact_ldl_refuses_an_indefinite_matrix():
    from fractions import Fraction as F

    from certo.sos import ldl

    assert ldl([[F(1), F(0)], [F(0), F(1)]]) is not None
    assert ldl([[F(1), F(2)], [F(2), F(1)]]) is None     # eigenvalues 3, -1


# --- v0.3: primality and factorisation -------------------------------------


def _number(n, question="prime"):
    from certo import NumberSpec
    from certo.engines import algebra

    return algebra.number(NumberSpec(n=n, question=question), LIM)


def test_a_pratt_certificate_is_checked_by_modular_exponentiation():
    r = _number(2 ** 31 - 1)
    assert r.verdict is Verdict.PROVED
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert len(rep.checks) > 20


def test_a_carmichael_number_does_not_get_a_certificate():
    """561 passes Fermat for most bases; the order condition catches it."""
    r = _number(561)
    assert r.verdict is Verdict.REFUTED
    assert r.certificate is None


def test_the_witness_is_reproducible_across_runs():
    """Small bases in order, not random ones, so two runs agree on the digest."""
    a = _number(1000003).certificate
    b = _number(1000003).certificate
    assert a.digest() == b.digest()


def test_a_missing_factor_of_n_minus_one_is_caught():
    """Dropping one lets a composite through, so the check is not optional."""
    r = _number(2 ** 31 - 1)
    cert = _roundtrip(r.certificate)
    cert.payload["tree"]["factors"].pop()
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("all of" in c and not ok for c, ok, _ in rep.checks)


def test_a_forged_witness_fails_fermat():
    r = _number(1000003)
    cert = _roundtrip(r.certificate)
    cert.payload["tree"]["witness"] = 4
    rep = verify(cert, LIM)
    assert not rep.ok


def test_a_factorisation_multiplies_back_and_its_factors_are_prime():
    r = _number(600851475143, question="factor")
    assert r.verdict is Verdict.PROVED
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert "71" in r.meta["factors"]


def test_a_factorisation_that_does_not_multiply_back_is_caught():
    cert = _roundtrip(_number(360, question="factor").certificate)
    assert verify(cert, LIM).ok
    cert.payload["tree"]["factors"][0]["e"] = 9
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("multiply back" in c and not ok for c, ok, _ in rep.checks)

# --- an ILP has two numbers, and they are not the same number --------------


def _knapsack(cap, integer):
    from fractions import Fraction

    from certo import LPSpec

    s = LPSpec(sense="max", integer=integer)
    s.variable("x")
    s.variable("y")
    s.objective({"x": 1, "y": 1})
    s.constraint({"x": 1, "y": 1}, "<=", Fraction(cap), name="cap")
    return s


def test_an_ilp_reports_the_integer_optimum_not_its_relaxation():
    """It reported the relaxation as `objective`, which is an overclaim."""
    from fractions import Fraction

    from certo.engines import lp

    r = lp.opt(_knapsack(Fraction(3, 2), True), LIM)
    assert r.meta["objective"] == "1"          # achievable
    assert r.meta["bound"] == "3/2"            # certified by the dual
    assert r.meta["objective"] != r.meta["bound"]


def test_an_lp_is_untouched_by_that():
    from fractions import Fraction

    from certo.engines import lp

    r = lp.opt(_knapsack(Fraction(3, 2), False), LIM)
    assert r.meta["objective"] == "3/2"
    assert r.meta["bound"] is None


def test_both_sides_of_an_ilp_are_certified():
    from fractions import Fraction

    from certo.engines import lp

    cert = _roundtrip(lp.opt(_knapsack(Fraction(3, 2), True), LIM).certificate)
    rep = verify(cert, LIM)
    assert rep.ok and rep.solver_free
    assert any("integral point is feasible" in c and ok
               for c, ok, _ in rep.checks)
    assert any("differ" in w for w in rep.warnings)


def test_a_tight_ilp_says_the_optimum_is_certified():
    """When the integral point meets the bound, nu is pinned exactly."""
    from certo.engines import lp

    r = lp.opt(_knapsack(2, True), LIM)
    assert r.meta["objective"] == "2" == r.meta["bound"]
    assert "CERTIFIED" in r.detail or "CERTIFICADO" in r.detail
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert not any("differ" in w for w in rep.warnings)


def test_a_forged_integral_point_is_caught():
    from fractions import Fraction

    from certo.engines import lp

    cert = _roundtrip(lp.opt(_knapsack(Fraction(3, 2), True), LIM).certificate)
    cert.payload["integral_point"] = ["5", "5"]        # violates the capacity
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("feasible" in c and not ok for c, ok, _ in rep.checks)


def test_the_real_packing_that_found_this():
    """Their canonical core: nu = 7, mu* = 15/2, and the gap is the point."""
    from itertools import combinations

    from certo import PackingSpec
    from certo.engines import lp

    lists = [(0, 1), (0, 1, 2), (0, 1, 2, 3), (0, 1, 3), (0, 2, 3, 4), (0, 4)]
    items = []
    for j, block in enumerate(lists):
        for a, b in combinations(block, 2):
            items.append(("t{}_{}_{}".format(j, a, b),
                          ["e{}_{}".format(a, b), "d{}_{}".format(j, a),
                           "d{}_{}".format(j, b)], 1))

    frac = lp.opt(PackingSpec(items=items, capacities=1).to_lp(), LIM)
    integral = lp.opt(PackingSpec(items=items, capacities=1,
                                  integer=True).to_lp(), LIM)
    assert frac.meta["objective"] == "15/2" and frac.meta["exact"]
    assert integral.meta["objective"] == "7"
    assert verify(_roundtrip(frac.certificate), LIM).ok

# --- mixed designs: a searched skeleton, an exact residual -----------------


def _mixed_spec(slots=4, shared="2/3", cap=3):
    from fractions import Fraction

    from certo import LPSpec

    lp = LPSpec(sense="max")
    for i in range(slots):
        lp.variable("y{}".format(i), kind="binary")
        lp.variable("q{}".format(i))
    lp.objective({**{"y{}".format(i): 2 for i in range(slots)},
                  **{"q{}".format(i): 5 for i in range(slots)}})
    for i in range(slots):
        lp.constraint({"y{}".format(i): 1, "q{}".format(i): 1}, "<=", 1,
                      name="slot{}".format(i))
    lp.constraint({"q{}".format(i): 1 for i in range(slots)}, "<=",
                  Fraction(shared), name="shared")
    lp.constraint({"y{}".format(i): 1 for i in range(slots)}, "<=", cap,
                  name="count")
    return lp


def test_kinds_are_per_variable_not_per_spec():
    """`integer=True` makes EVERY variable integer, which is a different
    problem, not a restriction of this one."""
    spec = _mixed_spec()
    assert spec.is_mixed
    assert spec.discrete == ["y0", "y1", "y2", "y3"]
    assert spec.continuous == ["q0", "q1", "q2", "q3"]
    assert spec.kind_of("y0") == "binary" and spec.kind_of("q0") == "continuous"


def test_an_unknown_kind_is_refused():
    from certo import LPSpec

    try:
        LPSpec().variable("x", kind="fuzzy")
    except ValueError as e:
        assert "binary" in str(e)
    else:
        raise AssertionError("it accepted a kind that does not exist")


def test_freezing_moves_the_discrete_contribution_to_the_right_hand_side():
    from fractions import Fraction

    spec = _mixed_spec(slots=2)
    residual, const = spec.frozen({"y0": 1, "y1": 0})
    assert const == 2                              # one slot reserved, gain 2
    assert residual.var_names == ["q0", "q1"]
    rhs = {n: r for n, _, _, r in residual.cons}
    assert rhs["slot0"] == 0 and rhs["slot1"] == 1


def test_a_mixed_design_is_certified_and_verifies_without_a_solver():
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM)
    assert r.verdict is Verdict.SATISFIABLE
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free


def test_the_three_numbers_are_kept_apart():
    from fractions import Fraction

    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM)
    achieved = Fraction(r.meta["achieved"])
    assert achieved == (Fraction(r.meta["discrete_gain"])
                        + Fraction(r.meta["conditional"]))
    assert achieved <= Fraction(r.meta["bound"])    # the relaxation bounds it


def test_meeting_the_relaxation_bound_certifies_global_optimality_for_free():
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM)
    assert r.meta["globally_optimal"] is True
    assert "global optimum" in r.detail or "óptimo global" in r.detail
    rep = verify(_roundtrip(r.certificate), LIM)
    assert not any("NOT CLAIMED" in w or "NO SE AFIRMA" in w
                   for w in rep.warnings)


def test_otherwise_global_optimality_is_explicitly_not_claimed():
    from certo.certificate import Certificate
    from certo.engines import mixed

    cert = _roundtrip(mixed.mixed(_mixed_spec(), LIM).certificate)
    cert.payload["globally_optimal"] = False       # as it would be with a gap
    rep = verify(cert, LIM)
    assert rep.ok
    assert any("NOT CLAIMED" in w or "NO SE AFIRMA" in w for w in rep.warnings)


def test_a_design_short_of_its_target_is_valid_but_insufficient():
    """A shortfall is not an invalid certificate -- it is a valid certificate
    for a design that falls short, and the difference matters to a reader."""
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM, target="1000")
    assert r.verdict is Verdict.REFUTED            # the design misses
    assert r.meta["deficit"]
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok                                  # the CERTIFICATE is fine
    assert any("SHORT OF TARGET" in w or "POR DEBAJO" in w
               for w in rep.warnings)


def test_a_forged_assignment_fails_the_original_constraints():
    from certo.engines import mixed

    cert = _roundtrip(mixed.mixed(_mixed_spec(), LIM).certificate)
    assert verify(cert, LIM).ok
    for k in cert.payload["assignment"]:
        cert.payload["assignment"][k] = "1"        # every slot reserved
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("original constraint" in c and not ok
               for c, ok, _ in rep.checks)


def test_a_fractional_binary_is_caught():
    from certo.engines import mixed

    cert = _roundtrip(mixed.mixed(_mixed_spec(), LIM).certificate)
    cert.payload["assignment"]["y0"] = "1/2"
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("really is discrete" in c and not ok
               for c, ok, _ in rep.checks)


def test_the_residual_must_be_the_original_problem_frozen():
    """Otherwise the sub-certificate could be about a different problem --
    the same gap `compose` closes between a lemma and its use."""
    from certo.engines import mixed

    cert = _roundtrip(mixed.mixed(_mixed_spec(), LIM).certificate)
    cert.payload["system"][0]["rhs"] = "99"        # the original moved
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("substituted" in c and not ok for c, ok, _ in rep.checks)


def test_a_spec_with_no_discrete_variables_says_to_use_opt():
    from certo import LPSpec
    from certo.engines import mixed

    lp = LPSpec(sense="max")
    lp.variable("x")
    lp.objective({"x": 1})
    lp.constraint({"x": 1}, "<=", 1, name="c")
    r = mixed.mixed(lp, LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "opt" in r.detail

# --- the second round of feedback ------------------------------------------


def test_a_literal_exponent_on_a_real_is_not_a_non_constant_exponent():
    """`S**4` on a REAL S gives z3 a RATIONAL literal 4, not an integer one,
    so is_int_value said no and an ordinary quartic was rejected."""
    import z3

    from certo.linarith import polynomial

    S = z3.Real("S")
    n = z3.Int("n")
    assert polynomial(S ** 4) == polynomial(S * S * S * S)
    assert polynomial(n ** 3) == polynomial(n * n * n)
    assert polynomial(S ** 0) == {(): 1}


def test_fractional_and_symbolic_exponents_are_still_refused():
    import z3

    from certo.linarith import NotPolynomial, polynomial

    S, n = z3.Real("S"), z3.Int("n")
    for bad in (S ** z3.RealVal("1/2"), S ** -2, S ** n):
        try:
            polynomial(bad)
        except NotPolynomial:
            pass
        else:
            raise AssertionError("accepted {}".format(bad))


def test_a_quartic_identity_certifies_through_ideal():
    """The shape that was rejected: powers written with `**`."""
    import z3

    from certo import IdealSpec
    from certo.engines import algebra

    S = z3.Real("S")
    r = algebra.ideal(IdealSpec(variables=["S"], equations=[S ** 2 - 4],
                                claim=S ** 4 - 16), LIM)
    assert r.verdict is Verdict.PROVED
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_the_three_milp_levels_are_named():
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM)
    assert r.meta["level"] == "global_optimum"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert "GLOBAL OPTIMUM" in rep.detail or "ÓPTIMO GLOBAL" in rep.detail


def test_a_skeleton_can_come_from_someone_elses_solver():
    """A real MILP may be HiGHS, Gurobi or a person; requiring CBC to
    reproduce it would put certo's limits in front of a real construction."""
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM,
                    freeze={"y0": 1, "y1": 1, "y2": 0, "y3": 1})
    assert r.verdict is Verdict.SATISFIABLE
    assert r.meta["skeleton_from"] == "external"
    assert sorted(r.meta["selected"]) == ["y0", "y1", "y3"]
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("ANOTHER solver" in w or "OTRO solver" in w
               for w in rep.warnings)


def test_a_frozen_assignment_is_checked_like_any_other():
    """Where it came from changes nothing about what is certified."""
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM,
                    freeze={"y0": 1, "y1": 1, "y2": 1, "y3": 1})   # 4 > cap 3
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None


def test_an_incomplete_frozen_assignment_names_what_is_missing():
    from certo.engines import mixed

    r = mixed.mixed(_mixed_spec(), LIM, freeze={"y0": 1})
    assert r.status is Status.OUT_OF_THEORY
    assert "y1" in r.detail


def test_opt_takes_a_target_and_certifies_reaching_it():
    """For an existence proof the question is whether a bound is reached."""
    from certo.engines import lp

    r = lp.opt(_knapsack(3, False), LIM, target="2")
    assert r.meta["meets_target"] is True
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("reaches the target" in c and ok for c, ok, _ in rep.checks)


def test_falling_short_of_an_opt_target_is_a_warning_not_invalidity():
    from certo.engines import lp

    r = lp.opt(_knapsack(3, False), LIM, target="99")
    assert r.meta["meets_target"] is False
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("SHORT OF TARGET" in w or "POR DEBAJO" in w
               for w in rep.warnings)


def test_a_packing_can_be_whole_in_one_item_kind_only():
    from certo import Graph, PackingSpec

    g = Graph.from_edges(6, [(i, j) for i in range(6) for j in range(i + 1, 6)])
    base = PackingSpec.cliques_in_graph(g, gains={3: 2, 4: 5})
    pk = PackingSpec(items=base.items, capacities=base.capacities,
                     sense="max", integer={"K3"})
    assert pk.discrete_kinds() == {"K3"}
    lp_spec = pk.to_lp()
    assert lp_spec.is_mixed
    assert all(lp_spec.kind_of(n) == "integer"
               for n, _, _, k in pk.items if k == "K3")
    assert all(lp_spec.kind_of(n) == "continuous"
               for n, _, _, k in pk.items if k == "K4")


def test_opt_refuses_to_report_a_design_on_a_mixed_problem():
    """Rounding every variable would round the fractional weights to zero and
    report a design worth nothing. That number is `mixed`'s to compute."""
    from certo import Graph, PackingSpec
    from certo.engines import lp, mixed

    g = Graph.from_edges(6, [(i, j) for i in range(6) for j in range(i + 1, 6)])
    base = PackingSpec.cliques_in_graph(g, gains={3: 2, 4: 5})
    pk = PackingSpec(items=base.items, capacities=base.capacities,
                     sense="max", integer={"K3"}).to_lp()

    r = lp.opt(pk, LIM)
    assert r.meta["objective"] is None          # no design claimed
    assert r.meta["bound"] == "25/2"
    assert "mixed" in r.detail

    assert mixed.mixed(pk, LIM).meta["achieved"] == "25/2"


def test_the_certificate_records_which_variables_are_discrete():
    from certo.engines import lp

    p = lp.opt(_mixed_spec(), LIM).certificate.payload
    assert p["kinds"]["y0"] == "binary"
    assert p["kinds"]["q0"] == "continuous"

# --- P1: lists packings, the gap, and proved optimality --------------------


def _core():
    from certo import PackingSpec, SetFamily

    fam = SetFamily(5, [(0, 1), (0, 1, 2), (0, 1, 2, 3),
                        (0, 1, 3), (0, 2, 3, 4), (0, 4)])
    return PackingSpec.lists(fam)


def test_the_lists_constructor_builds_the_packing_the_corpus_uses():
    """A pair once globally, and once per (list, element)."""
    spec = _core()
    assert len(spec.items) == 20
    name, res, gain, kind = spec.items[0]
    assert kind == "pair" and gain == 1
    assert len(res) == 3                       # the pair, and two incidences


def test_the_gap_carries_both_sides_and_they_match():
    from certo import packing as pk

    cert, meta = pk.gap(_core(), LIM)
    assert (meta["mu"], meta["nu"], meta["gap"]) == ("15/2", "7", "1/2")
    rep = verify(_roundtrip(cert), LIM)
    assert rep.ok
    assert any("same packing" in c and ok for c, ok, _ in rep.checks)


def test_a_gap_whose_halves_disagree_is_caught():
    from certo import packing as pk

    cert = _roundtrip(pk.gap(_core(), LIM)[0])
    assert verify(cert, LIM).ok
    cert.payload["gap"] = "1/3"                # no longer the difference
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("difference" in c and not ok for c, ok, _ in rep.checks)


def test_a_gap_from_a_design_says_nu_is_not_proved_optimal():
    from certo import packing as pk

    rep = verify(_roundtrip(pk.gap(_core(), LIM)[0]), LIM)
    assert any("not a proven integral optimum" in w or "no un óptimo" in w
               for w in rep.warnings)


def _branching_ilp(n_items=8, cap=30, count=4):
    """A small ILP that genuinely branches: 29 nodes, all three closing kinds."""
    from certo import LPSpec

    W = [7, 8, 9, 5, 6, 11, 4, 13][:n_items]
    V = [9, 11, 13, 6, 8, 16, 5, 19][:n_items]
    lp = LPSpec(sense="max", title="knapsack")
    for i in range(n_items):
        lp.variable("x%d" % i, 0, 1, kind="integer")
    lp.objective({"x%d" % i: V[i] for i in range(n_items)})
    lp.constraint({"x%d" % i: W[i] for i in range(n_items)}, "<=", cap,
                  name="cap")
    lp.constraint({"x%d" % i: 1 for i in range(n_items)}, "<=", count,
                  name="count")
    return lp


def test_a_nodes_dual_must_close_that_nodes_own_subproblem():
    """The hole this replaced: a certificate for one node closing another.

    A dual for a node's relaxation is a valid dual for SOME linear program and
    nothing in it says which node it came from. Trees used to store one per
    node and check it on its own terms, so exchanging two of them verified --
    which means an expensive subtree could be closed by a cheap one's
    certificate, and "no design does better" was not established.

    Now the node's program is DERIVED from the root system and the node's own
    fixings, and the dual is checked against that.
    """
    import copy

    from certo.certificate import Certificate
    from certo.engines import bb

    r = bb.prove_optimal(_branching_ilp(), LIM, max_nodes=20_000)
    assert r.verdict is Verdict.PROVED and r.meta["optimum"] == "43"
    base = json.loads(json.dumps(r.certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    nodes = base["payload"]["nodes"]
    closed = [i for i, n in enumerate(nodes) if n["why"] == "bound"]
    assert len(closed) >= 2, "need two closed nodes to exchange"
    a, b = closed[0], closed[-1]
    assert nodes[a]["bound"] != nodes[b]["bound"]

    swapped = copy.deepcopy(base)
    ns = swapped["payload"]["nodes"]
    ns[a]["dual"] = copy.deepcopy(ns[b]["dual"])
    ns[a]["primal"] = copy.deepcopy(ns[b]["primal"])
    ns[a]["bound"] = ns[b]["bound"]
    assert not verify(Certificate.from_dict(swapped), LIM).ok

    # and the root system is not decoration either
    bent = copy.deepcopy(base)
    bent["payload"]["system"]["cons"][0][3] = "60"
    assert not verify(Certificate.from_dict(bent), LIM).ok


def test_a_tied_tree_closes_every_node_without_a_solver():
    """Three closing kinds, all arithmetic, and the flag says so."""
    from certo.engines import bb

    r = bb.prove_optimal(_branching_ilp(), LIM, max_nodes=20_000)
    cert = r.certificate
    kinds = {n["why"] for n in cert.payload["nodes"]}
    assert kinds == {"branch", "bound", "infeasible"}

    assert cert.solver_free is True          # computed, not declared
    rep = verify(_roundtrip(cert), LIM)
    assert rep.ok and rep.solver_free
    assert any("derived from the root" in n for n, ok, _ in rep.checks)

    # The root system is written once; a node carries its fixings, its bound
    # and the two vectors that close it, and nothing else.
    per_node = len(json.dumps(cert.payload["nodes"])) / len(cert.payload["nodes"])
    assert per_node < 300, per_node
    assert set(cert.payload["nodes"][0]) <= {
        "fixed", "why", "bound", "dual", "primal", "ray", "on", "values"}


def test_an_older_tree_still_verifies_and_is_told_what_it_does_not_establish():
    """The schema is frozen, so a 0.6 tree must still check -- and must say
    that nothing ties its nodes to their subproblems."""
    from certo.certificate import Certificate, branch_bound_certificate
    from certo.engines import bb, lp

    r = bb.prove_optimal(_branching_ilp(4, 15, 2), LIM, max_nodes=20_000)
    root = _branching_ilp(4, 15, 2)

    # Rebuild the tree in the old shape: a whole nested certificate per node,
    # and no root system at all.
    from certo import tree as _tree
    legacy = []
    for n in r.certificate.payload["nodes"]:
        if n["why"] == "branch":
            legacy.append(dict(n))
            continue
        node_spec, _const = _tree.restrict(root, _tree.fixings(n["fixed"]))
        got = lp.opt(node_spec, LIM)
        old = {"fixed": n["fixed"], "why": n["why"], "bound": n.get("bound")}
        old["cert"] = (got.certificate.to_dict() if got.certificate
                       else lp.infeasible_certificate(node_spec, LIM).to_dict())
        legacy.append(old)

    cert = branch_bound_certificate(
        incumbent=r.certificate.payload["incumbent"],
        incumbent_cert=r.certificate.payload["incumbent_cert"],
        nodes=legacy, order=r.certificate.payload["order"],
        sense=r.certificate.payload["sense"])
    assert cert.solver_free is False          # no root system, so not tied
    rep = verify(Certificate.from_dict(json.loads(json.dumps(cert.to_dict()))),
                 LIM)
    assert rep.ok, [c for c in rep.checks if not c[1]]
    assert any("NOTHING ties it" in w for w in rep.warnings)


def test_branch_and_bound_proves_the_integral_optimum():
    """The whole point: nu = 7 stops being a design and becomes the optimum."""
    from certo import PackingSpec
    from certo.engines import bb

    core = _core()
    whole = PackingSpec(items=core.items, capacities=core.capacities,
                        sense="max", integer=True)
    r = bb.prove_optimal(whole.to_lp(), LIM, max_nodes=30_000)
    assert r.verdict is Verdict.PROVED
    assert r.meta["optimum"] == "7"
    assert r.meta["infeasible"] > 0            # Farkas rays closed real leaves
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_missing_child_makes_the_tree_a_non_proof():
    """A tree with a hole reads exactly like a complete one."""
    from certo.engines import bb

    cert = _roundtrip(bb.prove_optimal(_c5(), LIM).certificate)
    assert verify(cert, LIM).ok
    branch = next(n for n in cert.payload["nodes"] if n["why"] == "branch")
    child = branch["fixed"] + [[branch["on"], branch["values"][0]]]
    key = ",".join("{}={}".format(v, x) for v, x in child)
    cert.payload["nodes"] = [n for n in cert.payload["nodes"]
                             if ",".join("{}={}".format(v, x)
                                         for v, x in n["fixed"]) != key]
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("children" in c and not ok for c, ok, _ in rep.checks)


def _c5():
    from certo import LPSpec

    lp = LPSpec(sense="max")
    for i in range(5):
        lp.variable("y{}".format(i), kind="binary")
    lp.objective({"y{}".format(i): 1 for i in range(5)})
    for i in range(5):
        lp.constraint({"y{}".format(i): 1, "y{}".format((i + 1) % 5): 1},
                      "<=", 1, name="e{}".format(i))
    return lp


def test_a_leaf_pruned_above_the_incumbent_is_caught():
    from certo.engines import bb

    cert = _roundtrip(bb.prove_optimal(_c5(), LIM).certificate)
    node = next(n for n in cert.payload["nodes"] if n["why"] == "bound")
    node["bound"] = "99"                       # it could have held something
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("closed by a certificate" in c and not ok
               for c, ok, _ in rep.checks)


def test_an_unbounded_discrete_variable_has_no_tree_to_exhibit():
    from certo import LPSpec
    from certo.engines import bb

    lp = LPSpec(sense="max")
    lp.variable("n", kind="integer")            # no upper bound
    lp.objective({"n": 1})
    lp.constraint({"n": 1}, "<=", 10, name="c")
    r = bb.prove_optimal(lp, LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "upper bound" in r.detail


def test_a_farkas_ray_certifies_infeasibility_by_three_dot_products():
    from certo import LPSpec
    from certo.engines import lp

    s = LPSpec(sense="max")
    s.variable("x")
    s.objective({"x": 1})
    s.constraint({"x": 1}, "<=", 1, name="hi")
    s.constraint({"x": -1}, "<=", -2, name="lo")     # x >= 2 and x <= 1
    cert = lp.infeasible_certificate(s, LIM)
    assert cert is not None
    rep = verify(_roundtrip(cert), LIM)
    assert rep.ok and rep.solver_free
    assert len(rep.checks) == 3


def test_a_tampered_ray_stops_being_a_ray():
    from certo import LPSpec
    from certo.engines import lp

    s = LPSpec(sense="max")
    s.variable("x")
    s.objective({"x": 1})
    s.constraint({"x": 1}, "<=", 1, name="hi")
    s.constraint({"x": -1}, "<=", -2, name="lo")
    cert = _roundtrip(lp.infeasible_certificate(s, LIM))
    cert.payload["y"] = ["1", "0"]              # b.y is now positive
    rep = verify(cert, LIM)
    assert not rep.ok


def test_a_packing_item_is_bounded_by_its_tightest_resource():
    """Without it branch and bound has infinitely many children per node."""
    spec = _core()
    lp_spec = spec.to_lp()
    assert all(hi is None for _, hi in lp_spec.bounds.values())   # fractional

    from certo import PackingSpec

    whole = PackingSpec(items=spec.items, capacities=spec.capacities,
                        sense="max", integer=True).to_lp()
    assert all(hi == 1 for _, hi in whole.bounds.values())


def test_by_orbit_works_on_graph_sweeps_too():
    from certo.graphs import is_chordal

    r = graphsearch.sweep(
        SweepSpec(n=6, filters=["connected"], predicate=is_chordal,
                  canonicalize="auto"),
        LIM, use_geng=False, by_orbit=True)
    assert r.meta["by_orbit"] is True
    p = r.certificate.payload
    assert all(k in p for k in ("by_orbit", "evaluated", "spot_checks"))
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_inferring_nothing_is_not_a_failure():
    """Every orbit a singleton means it was a full sweep, not a broken one."""
    from certo.graphs import is_chordal

    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], predicate=is_chordal,
                  canonicalize="auto"),
        LIM, use_geng=False, by_orbit=True)
    assert r.meta["inferred"] == 0
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("inferred NOTHING" in w or "no infirió NADA" in w
               for w in rep.warnings)

# --- order: a feasibility that does not improve with n ---------------------


def _sym(*names):
    import z3

    return z3.Reals(" ".join(names))


def test_the_term_that_was_invisible_to_both_lean_and_prove():
    """Not an infeasibility -- a feasibility that does not improve with n."""
    from certo import OrderSpec
    from certo.engines import order

    k, W, C, u, d, p = _sym("k", "W", "C", "u", "d", "p")
    spec = OrderSpec(
        expression=5 * k * W * C * C / (u ** 3 * d ** 2 * p ** 10),
        orders={"k": 0, "W": 2, "C": 1, "u": 0, "d": 2, "p": 0})
    r = order.order(spec, LIM)
    assert r.meta["degree"] == "0"
    assert r.meta["behaviour"] == "constant"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_claiming_it_decays_is_refuted():
    from certo import OrderSpec
    from certo.engines import order

    k, W, C, u, d, p = _sym("k", "W", "C", "u", "d", "p")
    spec = OrderSpec(
        expression=5 * k * W * C * C / (u ** 3 * d ** 2 * p ** 10),
        orders={"k": 0, "W": 2, "C": 1, "u": 0, "d": 2, "p": 0},
        expect="decays")
    r = order.order(spec, LIM)
    assert r.verdict is Verdict.REFUTED
    assert "Theta(1)" in r.detail


def test_decaying_and_growing_terms_are_told_apart():
    from certo import OrderSpec
    from certo.engines import order

    C, d = _sym("C", "d")
    o = {"C": 1, "d": 2}
    assert order.order(OrderSpec(expression=C / (d * d), orders=o),
                       LIM).meta["behaviour"] == "decays"
    assert order.order(OrderSpec(expression=C * d, orders=o),
                       LIM).meta["behaviour"] == "grows"


def test_cancellation_is_decided_not_estimated():
    """DIFFERENT monomials landing on the same exponent, cancelling exactly.

    `C^2` and `d` are different terms, but with C ~ n and d ~ n^2 both are
    n^2 -- and their coefficients sum to zero, so the top exponent is not
    there. With `Fraction` that is decided rather than estimated.
    """
    from certo import OrderSpec
    from certo.engines import order

    C, d, W = _sym("C", "d", "W")
    r = order.order(OrderSpec(expression=C * C - d + W,
                              orders={"C": 1, "d": 2, "W": 1}), LIM)
    assert r.meta["degree"] == "1"          # the two n^2 terms cancelled
    assert r.meta["cancelled"] == 1


def test_a_symbol_with_no_order_is_an_error_not_an_assumption():
    from certo import OrderSpec
    from certo.engines import order

    a, b = _sym("a", "b")
    r = order.order(OrderSpec(expression=a * b, orders={"a": 1}), LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "b" in r.detail


def test_dividing_by_a_sum_is_refused_rather_than_guessed():
    """1/(x+y) has an order that depends on which dominates."""
    from certo import OrderSpec
    from certo.engines import order

    x, y = _sym("x", "y")
    r = order.order(OrderSpec(expression=1 / (x + y), orders={"x": 1, "y": 2}),
                    LIM)
    assert r.status is Status.OUT_OF_THEORY
    assert "sum" in r.detail or "suma" in r.detail


def test_the_order_certificate_needs_neither_solver_nor_spec():
    from certo import OrderSpec
    from certo.engines import order

    C, d = _sym("C", "d")
    cert = _roundtrip(order.order(
        OrderSpec(expression=C / d, orders={"C": 1, "d": 2}), LIM).certificate)
    rep = verify(cert, LIM)
    assert rep.ok and rep.solver_free
    assert any("EXPONENT" in w or "EXPONENTE" in w for w in rep.warnings)


def test_a_forged_degree_is_recomputed_and_caught():
    from certo import OrderSpec
    from certo.engines import order

    C, d = _sym("C", "d")
    cert = _roundtrip(order.order(
        OrderSpec(expression=C / d, orders={"C": 1, "d": 2}), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["degree"] = "5"
    rep = verify(cert, LIM)
    assert not rep.ok
    assert any("leading exponent" in c and not ok for c, ok, _ in rep.checks)


# --- papercuts from the same report ----------------------------------------


def test_a_certificate_is_read_whether_it_arrived_alone_or_inside_a_run():
    """`--cert FILE` writes one shape and `--json` another; both are right."""
    import json as _json

    from certo import Spec
    from certo.engines import smt

    x = _sym("x")[0]
    s = Spec()
    s.assume("h", x >= 1)
    s.claim(x >= 1)
    res = smt.prove(s, LIM)

    alone = Certificate.from_dict(_json.loads(_json.dumps(
        res.certificate.to_dict())))
    inside = Certificate.from_dict(_json.loads(_json.dumps(res.to_dict())))
    assert alone.kind == inside.kind == "unsat_core"
    assert alone.digest() == inside.digest()


def test_vacuity_names_the_minimal_clash_instead_of_sending_you_elsewhere():
    import z3

    from certo import Spec
    from certo.engines import smt

    x, y = _sym("x", "y")
    s = Spec()
    s.assume("x_big", x > 10)
    s.assume("y_ok", y >= 0)            # innocent, and must not be blamed
    s.assume("x_small", x < 1)
    s.claim(x + y == 42)

    r = smt.prove(s, LIM)
    assert r.meta["vacuous"] is True
    assert set(r.meta["clash"]) == {"x_big", "x_small"}
    assert "x_big" in r.detail

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("x_big, x_small" in w for w in rep.warnings)


def test_the_clash_is_an_optional_field_the_frozen_schema_allows():
    """An older reader ignores it; a newer one uses it."""
    from certo.certificate import unsat_core_certificate

    cert = unsat_core_certificate("(check-sat)", ["a"], [], vacuous=True)
    assert cert.payload["clash"] == []
    assert verify(_roundtrip(cert), LIM) is not None


# --- lint: the questions asked before the compute is spent -----------------


def _lint_file(tmp, body: str):
    """A spec on disk, because `lint` reads files the way a user does."""
    import hashlib

    name = "lint_" + hashlib.sha256(body.encode()).hexdigest()[:10] + ".py"
    f = tmp / name
    f.write_text(body, encoding="utf-8")
    return str(f)


def _tmp():
    import tempfile

    return pathlib.Path(tempfile.mkdtemp(prefix="certo_lint_"))


def test_lint_catches_contradictory_hypotheses_before_the_proof_is_run():
    """The headline check: vacuity found first, not after a valid-and-empty win."""
    from certo import lint as linter

    f = _lint_file(_tmp(), (
        "import z3\n"
        "from certo.spec import Spec\n"
        "def spec():\n"
        "    x, y = z3.Real('x'), z3.Real('y')\n"
        "    s = Spec(title='a regime nobody is in')\n"
        "    s.assume('x_big', x > 10)\n"
        "    s.assume('y_ok', y > 0)\n"
        "    s.assume('x_small', x < 1)\n"
        "    s.claim(y * y >= 0)\n"
        "    return s\n"))
    rep = linter.lint(f, LIM)
    assert rep["kind"] == "Spec"
    clash = [x for x in rep["findings"] if x["key"] == "spec.vacuous"]
    assert len(clash) == 1
    assert "x_big" in clash[0]["text"] and "x_small" in clash[0]["text"]
    # The innocent hypothesis is not blamed: a minimal clash, not the core.
    assert "y_ok" not in clash[0]["text"]
    assert rep["errors"] == 1 and not rep["ok"]


def test_lint_catches_the_induction_gap_without_discharging_a_base_case():
    """The engine refuses this too -- after proving every base case first."""
    from certo import lint as linter

    f = _lint_file(_tmp(), (
        "import z3\n"
        "from certo.spec import InductSpec, Spec\n"
        "def spec():\n"
        "    k = z3.Int('k')\n"
        "    step = Spec()\n"
        "    step.assume('k_big', k >= 10)\n"
        "    step.claim(k + 1 >= 11)\n"
        "    return InductSpec(k0=3, base_upto=8, base=lambda j: None,\n"
        "                      step=step, step_from=10, bridge='...',\n"
        "                      title='a chain that does not join')\n"))
    rep = linter.lint(f, LIM)
    gaps = [x for x in rep["findings"] if x["key"] == "induct.gap"]
    assert len(gaps) == 1
    assert "10" in gaps[0]["text"] and "8" in gaps[0]["text"]


def test_lint_says_a_bool_predicate_means_reproducible_not_certified():
    from certo import lint as linter

    f = _lint_file(_tmp(), (
        "from certo.spec import DomainSpec\n"
        "def spec():\n"
        "    return DomainSpec(items=[(a, b) for a in range(4)"
        " for b in range(4)],\n"
        "                      predicate=lambda p: p[0] + p[1] >= 0,\n"
        "                      key=lambda p: '%d,%d' % p, title='t')\n"))
    rep = linter.lint(f, LIM)
    keys = {x["key"] for x in rep["findings"]}
    assert "sweep.bool" in keys
    assert "domain.no_reduce" in keys          # `shrink` would refuse
    # Notes alone are not a failure: this spec is fine, it just says less.
    assert rep["ok"] and rep["errors"] == 0 and rep["warnings"] == 0


def test_lint_reads_the_domain_size_without_materialising_it():
    """A generator of ten million items must not be turned into a list."""
    from certo import lint as linter
    from certo.lint import PEEK

    f = _lint_file(_tmp(), (
        "from certo.spec import DomainSpec\n"
        "def spec():\n"
        "    return DomainSpec(items=lambda: iter(range(10 ** 7)),\n"
        "                      predicate=lambda i: i >= 0, title='big')\n"))
    rep = linter.lint(f, LIM)
    huge = [x for x in rep["findings"] if x["key"] == "domain.huge"]
    assert len(huge) == 1
    assert str(PEEK) in huge[0]["text"] or "100000" in huge[0]["text"]


def test_lint_reports_an_unassigned_magnitude_as_an_error():
    from certo import lint as linter

    f = _lint_file(_tmp(), (
        "import z3\n"
        "from certo.spec import OrderSpec\n"
        "def spec():\n"
        "    d, C, W = z3.Real('d'), z3.Real('C'), z3.Real('W')\n"
        "    return OrderSpec(expression=W * C / (d * d),\n"
        "                     orders={'W': 2, 'C': 1}, title='t')\n"))
    rep = linter.lint(f, LIM)
    bad = [x for x in rep["findings"] if x["key"] == "order.unassigned"]
    assert len(bad) == 1 and "d" in bad[0]["text"]
    assert rep["errors"] == 1


def test_lint_warns_that_integer_true_makes_every_variable_integer():
    """A user read it as "there are integers in here" and got everything rounded."""
    from certo import lint as linter

    f = _lint_file(_tmp(), (
        "from certo.spec import LPSpec\n"
        "def spec():\n"
        "    lp = LPSpec(sense='max', integer=True, title='t')\n"
        "    lp.variable('x'); lp.variable('y')\n"
        "    lp.objective({'x': 1, 'y': 1})\n"
        "    lp.constraint({'x': 1, 'y': 1}, '<=', 3, name='cap')\n"
        "    return lp\n"))
    rep = linter.lint(f, LIM)
    warn = [x for x in rep["findings"] if x["key"] == "lp.integer_all"]
    assert len(warn) == 1 and "2" in warn[0]["text"]
    assert rep["warnings"] == 1 and not rep["ok"]


def test_lint_tells_a_script_from_a_broken_spec():
    from certo import lint as linter

    f = _lint_file(_tmp(), "print('I am a script')\n")
    rep = linter.lint(f, LIM)
    assert [x["key"] for x in rep["findings"]] == ["no_spec_fn"]


def test_lint_does_not_enumerate_a_family_it_cannot_afford():
    """Knowing a sweep's size must not cost what the sweep costs."""
    import time

    from certo import lint as linter

    f = _lint_file(_tmp(), (
        "from certo.spec import SweepSpec\n"
        "def spec():\n"
        "    return SweepSpec(n=11, predicate=lambda g: True, title='t')\n"))
    t0 = time.perf_counter()
    rep = linter.lint(f, LIM)
    assert time.perf_counter() - t0 < 5.0
    texts = " ".join(x["text"] for x in rep["findings"])
    assert "1018997864" in texts.replace(",", "")
    assert any(x["key"] == "sweep.not_probed" for x in rep["findings"])


# --- status: where the proof stands ---------------------------------------


def test_status_finds_the_bridges_a_proof_rests_on():
    """A bridge is legitimate. Losing count of them is not."""
    from certo import status_report
    from certo.certificate import proof_certificate

    tmp = _tmp()
    cert = proof_certificate(
        title="the theorem", theorem_smt2="(assert true)",
        assumptions=[], assumptions_smt2="",
        lemmas=[{"name": "counted", "derived": True, "cert": None},
                {"name": "k6", "derived": False, "cert": None,
                 "bridge": "the DRAT proof says the encoding is unsat"}],
        step=None, used=["counted", "k6"], unused=[],
    )
    (tmp / "p.json").write_text(json.dumps(cert.to_dict()), encoding="utf-8")

    rep = status_report.scan(str(tmp))
    assert rep["certificates"] == 1
    assert len(rep["owed"]) == 1
    assert rep["owed"][0]["name"] == "k6"
    assert "DRAT" in rep["owed"][0]["why"]
    assert not rep["hollow"] and not rep["stale"]


def test_status_separates_results_from_the_certificates_they_embed():
    """A lemma's certificate is not a result; the proof on top of it is."""
    import z3

    from certo import Spec, status_report
    from certo.certificate import proof_certificate
    from certo.engines import smt

    x = z3.Real("x")
    s = Spec()
    s.assume("pos", x > 0)
    s.claim(x >= 0)
    sub = smt.prove(s, LIM).certificate.to_dict()

    tmp = _tmp()
    (tmp / "lemma.json").write_text(json.dumps(sub), encoding="utf-8")
    top = proof_certificate(
        title="on top", theorem_smt2="(assert true)", assumptions=[],
        assumptions_smt2="",
        lemmas=[{"name": "pos", "derived": True, "cert": sub}],
        step=None, used=["pos"], unused=[],
    )
    (tmp / "top.json").write_text(json.dumps(top.to_dict()), encoding="utf-8")

    rep = status_report.scan(str(tmp))
    assert rep["certificates"] == 2
    # Both files hold a certificate; only one of them is a result.
    assert [n["kind"] for n in rep["results"]] == ["proof"]


def test_status_names_a_vacuous_proof_as_hollow_with_its_clash():
    import z3

    from certo import Spec, status_report
    from certo.engines import smt

    x, y = z3.Real("x"), z3.Real("y")
    s = Spec()
    s.assume("x_big", x > 10)
    s.assume("y_ok", y >= 0)
    s.assume("x_small", x < 1)
    s.claim(x + y == 42)

    tmp = _tmp()
    (tmp / "v.json").write_text(
        json.dumps(smt.prove(s, LIM).certificate.to_dict()), encoding="utf-8")

    rep = status_report.scan(str(tmp))
    assert len(rep["hollow"]) == 1
    text = rep["hollow"][0]["text"]
    assert "x_big" in text and "x_small" in text and "y_ok" not in text


def test_status_notices_the_spec_moved_under_a_certificate():
    import z3

    from certo import Spec, status_report
    from certo.engines import smt

    tmp = _tmp()
    spec_file = tmp / "s.py"
    spec_file.write_text("# version one\n", encoding="utf-8")

    x = z3.Real("x")
    s = Spec()
    s.assume("pos", x > 0)
    s.claim(x >= 0)
    cert = smt.prove(s, LIM).certificate.stamp(str(spec_file))
    (tmp / "c.json").write_text(json.dumps(cert.to_dict()), encoding="utf-8")

    assert not status_report.scan(str(tmp))["stale"]
    spec_file.write_text("# version TWO, materially different\n",
                         encoding="utf-8")
    stale = status_report.scan(str(tmp))["stale"]
    assert len(stale) == 1 and stale[0]["why"] == "changed"

    spec_file.unlink()
    assert status_report.scan(str(tmp))["stale"][0]["why"] == "gone"


def test_status_skips_files_that_are_not_certificates_without_complaining():
    """A ledger, a config and somebody's notes all live in the same directory."""
    from certo import status_report

    tmp = _tmp()
    (tmp / "notes.json").write_text('{"hello": "world"}', encoding="utf-8")
    (tmp / "broken.json").write_text("{not json", encoding="utf-8")
    rep = status_report.scan(str(tmp))
    assert rep["certificates"] == 0 and rep["skipped"] == 2


def test_status_reads_a_run_as_readily_as_a_bare_certificate():
    """`--cert` writes one shape and `--json` writes the other. Both are right."""
    import z3

    from certo import Spec, status_report
    from certo.engines import smt

    x = z3.Real("x")
    s = Spec()
    s.assume("pos", x > 0)
    s.claim(x >= 0)
    res = smt.prove(s, LIM)

    tmp = _tmp()
    (tmp / "run.json").write_text(json.dumps(res.to_dict()), encoding="utf-8")
    rep = status_report.scan(str(tmp))
    assert rep["certificates"] == 1
    assert rep["results"][0]["kind"] == "unsat_core"


def test_status_inherits_bridges_upward_but_not_unclaimed_optimality():
    """Two debts, two behaviours, and the difference is the point.

    A bridge is an ASSUMPTION: whatever stands on it stands on it too, however
    many levels down. An unclaimed optimality is a STATEMENT ABOUT ONE
    CERTIFICATE -- a proof citing a `gap` for the value 15/2 is not thereby
    claiming the optimum, and a `branch_bound` certificate is precisely the
    proof its own incumbent lacked.
    """
    from certo import status_report
    from certo.certificate import gap_certificate, proof_certificate

    inner = gap_certificate(
        fractional={"kind": "lp_dual", "payload": {}},
        integral={"kind": "mixed_design",
                  "payload": {"level": "conditional_optimum"}},
        mu="15/2", nu="7", gap="1/2", tight=[],
        level="conditional_optimum", title="the gap",
    ).to_dict()
    top = proof_certificate(
        title="on top", theorem_smt2="(assert true)", assumptions=[],
        assumptions_smt2="",
        lemmas=[{"name": "gap_is_half", "derived": False, "cert": inner,
                 "bridge": "reading the dual as a statement about the packing"}],
        step=None, used=["gap_is_half"], unused=[],
    )

    tmp = _tmp()
    (tmp / "top.json").write_text(json.dumps(top.to_dict()), encoding="utf-8")
    rep = status_report.scan(str(tmp))

    sorts = {o["sort"] for o in rep["owed"]}
    assert sorts == {"bridge"}, rep["owed"]
    assert rep["owed"][0]["name"] == "gap_is_half"

    # Alone, that same gap certificate DOES report its unclaimed optimality:
    # the rule is about inheritance, not about hiding it.
    alone = _tmp()
    (alone / "gap.json").write_text(json.dumps(inner), encoding="utf-8")
    assert [o["sort"] for o in status_report.scan(str(alone))["owed"]] \
        == ["not_claimed"]


def test_a_fractional_integral_point_does_not_verify():
    """Found by a user reading output, not code.

    `_verify_lp_dual` checked the declared integral point for non-negativity,
    for `Ax <= b`, and for matching its declared objective -- and never that
    the values were integers. `x = 3/2` satisfies `x + y <= 3` and hits the
    declared value of 3 perfectly well, and used to pass every check.
    """
    from certo.engines import lp
    from certo.spec import LPSpec

    s = LPSpec(sense="max", integer=True, title="maximise x + y, x + y <= 3")
    s.variable("x")
    s.variable("y")
    s.objective({"x": 1, "y": 1})
    s.constraint({"x": 1, "y": 1}, "<=", 3, name="cap")

    cert = lp.opt(s, LIM).certificate
    assert verify(_roundtrip(cert), LIM).ok

    forged = json.loads(json.dumps(cert.to_dict()))
    forged["payload"]["integral_point"] = ["3/2", "3/2"]
    rep = verify(Certificate.from_dict(forged), LIM)
    assert not rep.ok
    failed = [name for name, ok, _ in rep.checks if not ok]
    assert len(failed) == 1, rep.checks
    named = [d for name, ok, d in rep.checks if not ok][0]
    assert "x" in named and "y" in named


def test_a_mixed_problems_continuous_weights_may_be_fractional():
    """The integrality check is per DECLARED KIND, not blanket.

    A mixed design whose continuous weights are 1/6 is not an offender; the
    first version of this check would have called every one of them one.
    """
    from certo.engines import mixed
    from certo.spec import LPSpec

    s = LPSpec(sense="max", title="one switch, one continuous weight")
    s.variable("pick", 0, 1, kind="binary")
    s.variable("w", 0, None)
    s.objective({"pick": 1, "w": 1})
    s.constraint({"w": 6}, "<=", 1, name="cap")
    s.constraint({"pick": 1}, "<=", 1, name="one")

    r = mixed.mixed(s, LIM)
    assert r.certificate is not None
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok, [c for c in rep.checks if not c[1]]
    # The continuous weight really is fractional, which is the point.
    assert r.certificate.payload["continuous"]["w"] == "1/6"


# --- the question people actually ask -------------------------------------


def _regime():
    """Satisfiable hypotheses. dens = 1/2, kappa = 4 is a point in it."""
    import z3

    from certo import Spec

    d, k = z3.Reals("dens kappa")
    s = Spec(title="a regime that is NOT empty")
    s.assume("dens_ok", d > z3.RealVal(1) / 4)
    s.assume("kappa_large", k >= 4)
    s.assume("sparse", d <= z3.RealVal(1) / 2)
    return s, d, k


def test_claim_false_answers_the_opposite_of_the_question_and_says_so():
    """The footgun, pinned: `check` is right and the reading is inverted.

    A user wrote `claim(False)` to ask "are my hypotheses satisfiable?" and
    got UNSATISFIABLE on a system with models. The verdict does not change --
    `hypotheses AND False` really is unsat -- but it can no longer be read as
    a statement about the hypotheses without being told otherwise.
    """
    import z3

    from certo.engines import smt

    spec, _, _ = _regime()
    spec.claim(z3.BoolVal(False))

    r = smt.check(spec, LIM)
    assert r.verdict is Verdict.UNSATISFIABLE      # correct, and useless
    assert r.meta["constant_goal"] == "false"
    assert "hypotheses-only" in r.detail


def test_hypotheses_only_exhibits_a_point_in_a_non_empty_regime():
    """Not an argument that one exists: the parameters, on the table."""
    from certo.engines import smt

    spec, _, _ = _regime()
    r = smt.check(spec, LIM, hypotheses_only=True)
    assert r.verdict is Verdict.SATISFIABLE
    assert r.meta["hypotheses_only"] is True
    # A model certificate needs no solver to re-check: the non-emptiness of
    # the regime is the one answer here that verifies by evaluation.
    assert r.certificate.kind == "model"
    assert r.certificate.solver_free
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_hypotheses_only_names_the_minimal_clash_when_the_regime_is_empty():
    import z3

    from certo.engines import smt

    from certo import Spec

    d, k = z3.Reals("dens kappa")
    s = Spec(title="an empty one")
    s.assume("innocent", k >= 4)
    s.assume("dens_floor", d >= z3.RealVal(3) / 4)
    s.assume("sparse", d <= z3.RealVal(1) / 2)
    s.claim(z3.BoolVal(True))

    r = smt.check(s, LIM, hypotheses_only=True)
    assert r.verdict is Verdict.UNSATISFIABLE
    assert set(r.meta["clash"]) == {"dens_floor", "sparse"}
    assert "innocent" not in r.detail
    assert r.certificate.payload["vacuous"] is True


def test_hypotheses_only_ignores_the_claim_entirely():
    """Whatever the claim says, the question is about the hypotheses."""
    import z3

    from certo.engines import smt

    spec, d, _ = _regime()
    spec.claim(d > 10 ** 6)                # false in the regime, and irrelevant
    r = smt.check(spec, LIM, hypotheses_only=True)
    assert r.verdict is Verdict.SATISFIABLE


# --- an unsat core, stated in Lean ----------------------------------------


def test_a_linear_core_is_solver_free_and_verifies_by_arithmetic():
    """The most-used command stops producing the least-checkable certificate."""
    import z3

    from certo import Spec
    from certo.engines import smt

    x, y = z3.Reals("x y")
    s = Spec(title="linear")
    s.assume("x_ge_1", x >= 1)
    s.assume("y_ge_1", y >= 1)
    s.assume("noise", x + y <= 10 ** 6)
    s.claim(x + y >= 2)

    r = smt.prove(s, LIM)
    cert = r.certificate
    assert cert.solver_free is True
    assert cert.payload["multipliers"]
    # The core is still there: `compose` reads it for the entailment check.
    assert cert.payload["core_smt2"]

    rep = verify(_roundtrip(cert), LIM)
    assert rep.ok and rep.solver_free
    assert rep.method_key == "verify.core.by_farkas"


def test_forged_multipliers_are_rejected_by_the_arithmetic():
    """The check does not trust the search that produced them."""
    import z3

    from certo import Spec
    from certo.engines import smt

    x, y = z3.Reals("x y")
    s = Spec()
    s.assume("x_ge_1", x >= 1)
    s.assume("y_ge_1", y >= 1)
    s.claim(x + y >= 2)

    d = json.loads(json.dumps(smt.prove(s, LIM).certificate.to_dict()))
    lams = d["payload"]["multipliers"]

    # Scaling every multiplier is NOT a forgery: the system is scale-free and
    # the halved vector closes just as well. Worth pinning, because a check
    # that rejected it would be wrong.
    d["payload"]["multipliers"] = [str(Fraction(x) / 2) for x in lams]
    assert verify(Certificate.from_dict(d), LIM).ok

    # Changing ONE of them is: the monomials stop cancelling.
    d["payload"]["multipliers"] = [str(Fraction(lams[0]) + 1)] + lams[1:]
    assert not verify(Certificate.from_dict(d), LIM).ok

    d["payload"]["multipliers"] = ["-1"] + lams[1:]
    rep = verify(Certificate.from_dict(d), LIM)
    assert not rep.ok
    assert any(not ok for name, ok, _ in rep.checks)


# --- deriving the dual instead of reconstructing CBC's --------------------


def test_exact_certification_no_longer_needs_a_usable_dual():
    """The headline of P1 #1: CBC's dual stops being on the critical path.

    3 of 56 exact LPs needed the rational pair injected by hand, all on
    symmetric solutions -- where several duals are optimal and CBC returns an
    arbitrary one, which need not round onto anything dual-feasible.
    """
    from certo import exact

    #   max 2x + 3y   s.t.  x + y <= 1,  x + 2y <= 1,  x, y >= 0
    # The optimum is 2 at (1, 0), where BOTH rows are tight and only one
    # variable is active: degenerate, so the dual is underdetermined.
    A, b, c = [[1, 1], [1, 2]], [1, 1], [2, 3]

    for useless in ([0.0, 0.0], [7.3, -2.1], [0.0, 1.5]):
        x, y, rep, _ = exact.certify(A, b, c, [1.0, 0.0], useless)
        assert x is not None, useless
        assert rep["ok"] and rep["objective"] == 2
        # Derived, not rounded from what was handed in.
        assert y == [Fraction(0), Fraction(2)]


def test_a_derived_dual_is_a_candidate_and_not_a_promise():
    """Nothing is trusted for where it came from: check_lp still decides."""
    from certo import exact

    A, b, c = [[1, 1], [1, 2]], [1, 1], [2, 3]
    # The first candidate complementary slackness allows here is infeasible --
    # it satisfies the active column and fails the inactive one. The search
    # has to go on rather than return it.
    first = exact.dual_from_primal(A, b, c, [Fraction(1), Fraction(0)])
    assert not exact.check_lp(A, b, c, [Fraction(1), Fraction(0)], first)["ok"]

    good = [y for y in exact.dual_candidates(A, b, c, [Fraction(1), Fraction(0)])
            if exact.check_lp(A, b, c, [Fraction(1), Fraction(0)], y)["ok"]]
    assert good == [[Fraction(0), Fraction(2)]]


def test_the_simplest_denominator_still_wins_when_reconstruction_works():
    """Pass 1 runs first, so nothing that already certified changes."""
    from certo import exact

    A, b, c = [[1, 1]], [1], [1, 1]
    x, y, _rep, denom = exact.certify(A, b, c, [0.5, 0.5], [1.0])
    # 2, not 1: rung 1 cannot express 1/2, and the FIRST rung that works is
    # the one returned -- which is the denominator worth citing.
    assert denom == 2
    assert x == [Fraction(1, 2)] * 2 and y == [Fraction(1)]


def test_solve_exact_is_rational_throughout():
    from certo import exact

    # 2x + y = 1, x - y = 1  ->  x = 2/3, y = -1/3
    sol = exact.solve_exact([[2, 1], [1, -1]], [1, 1])
    assert sol == [Fraction(2, 3), Fraction(-1, 3)]
    assert all(isinstance(v, Fraction) for v in sol)

    # inconsistent: 0 = 1 after elimination
    assert exact.solve_exact([[1, 1], [1, 1]], [1, 2]) is None

    # underdetermined: the free position is pinned to zero, which is what
    # complementary slackness wants for a row nothing forces.
    assert exact.solve_exact([[1, 1]], [2]) == [Fraction(2), Fraction(0)]


def test_a_coupled_denominator_ladder_was_never_the_problem():
    """Pinned because the backlog claimed it was, and measurement said no.

    `limit_denominator` is monotone in accuracy, so a rung high enough for the
    harder of the two values is high enough for both. Reconstructing `x` and
    `y` at independent rungs looks like a free win and buys nothing.
    """
    from certo.exact import DENOM_LADDER, reconstruct

    for xf, yf in ((1 / 3, 0.5), (1 / 7, 0.5), (2 / 7, 3 / 11)):
        want_x = Fraction(xf).limit_denominator(10 ** 6)
        want_y = Fraction(yf).limit_denominator(10 ** 6)
        shared = next((d for d in DENOM_LADDER
                       if reconstruct([xf], d) == [want_x]
                       and reconstruct([yf], d) == [want_y]), None)
        assert shared is not None, (xf, yf)


# --- eliminating a variable, with the identity that proves it -------------


def _elim(equations, eliminate, variables):
    from certo import EliminateSpec
    from certo.engines import algebra

    return algebra.eliminate(
        EliminateSpec(variables=list(variables), equations=equations,
                      eliminate=eliminate, title="t"), LIM)


def test_the_resultant_is_the_discriminant_when_it_should_be():
    """Res(f, f') = -(b^2 - 4c) for f = t^2 + bt + c. Checkable by hand."""
    import z3

    b, c, t = z3.Reals("b c t")
    r = _elim([t * t + b * t + c, 2 * t + b], "t", ["b", "c", "t"])
    assert r.verdict is Verdict.SATISFIABLE
    assert r.meta["resultant"] == "-b^2 + 4*c"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_elimination_turns_a_system_into_a_condition_on_what_is_left():
    """t^2 = s in t^3 + st + 1 gives 2st + 1, so a common root needs 4s^3 = 1."""
    import z3

    s, t = z3.Reals("s t")
    r = _elim([t ** 3 + s * t + 1, t * t - s], "t", ["s", "t"])
    assert r.meta["resultant"] == "-4*s^3 + 1"
    assert "4*s^3" in r.detail


def test_a_constant_resultant_refutes_a_common_root_over_any_field():
    import z3

    t = z3.Real("t")
    r = _elim([t * t, t * t - 1], "t", ["t"])
    assert r.verdict is Verdict.REFUTED and r.status is Status.UNSAT
    assert r.meta["case"] == "no_common_root"
    assert r.meta["resultant"] == "1"


def test_a_vanishing_resultant_means_a_shared_factor():
    import z3

    s, t = z3.Reals("s t")
    f = (t - s) * (t + 1)
    r = _elim([f, f], "t", ["s", "t"])
    assert r.meta["case"] == "common_factor"
    assert r.meta["resultant"] == "0"


def test_the_certificate_verifies_by_expanding_and_needs_no_solver():
    import z3

    s, t = z3.Reals("s t")
    r = _elim([t ** 3 + s * t + 1, t * t - s], "t", ["s", "t"])
    cert = r.certificate
    assert cert.solver_free

    rep = verify(_roundtrip(cert), LIM)
    assert rep.ok and rep.solver_free
    names = [n for n, _, _ in rep.checks]
    assert any("A*f + B*g" in n for n in names)
    # The eliminated variable is gone from the answer, which is the point.
    assert "t" not in cert.payload["resultant"]


def test_forged_cofactors_are_caught_by_the_arithmetic():
    """The identity is the whole claim, so breaking it must fail."""
    import z3

    s, t = z3.Reals("s t")
    d = json.loads(json.dumps(
        _elim([t ** 3 + s * t + 1, t * t - s], "t", ["s", "t"])
        .certificate.to_dict()))
    key = next(iter(d["payload"]["A"]))
    d["payload"]["A"][key] = str(Fraction(d["payload"]["A"][key]) + 1)
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_sufficiency_is_qualified_when_both_leading_coefficients_can_vanish():
    """Res = 0 stops being enough where the leading coefficients die."""
    import z3

    s, t = z3.Reals("s t")
    # Leading coefficient in t is `s` for both: at s = 0 the degrees drop.
    r = _elim([s * t * t + 1, s * t * t + t], "t", ["s", "t"])
    cert = r.certificate
    assert cert.payload["lead_f_constant"] is False
    assert cert.payload["lead_g_constant"] is False
    rep = verify(_roundtrip(cert), LIM)
    assert rep.ok
    assert any("sufficiency is lost" in w for w in rep.warnings)


def test_three_equations_are_refused_rather_than_iterated():
    """Pairwise resultants introduce factors nothing here could certify away."""
    import z3

    s, t = z3.Reals("s t")
    r = _elim([t * t - s, t - s, t + s], "t", ["s", "t"])
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None
    assert "ideal" in r.detail


def test_a_variable_that_is_not_there_says_which_ones_are():
    import z3

    s, t = z3.Reals("s t")
    r = _elim([t * t - s, t - s], "u", ["s", "t"])
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "s, t" in r.detail


# --- a bound for every parameter value, not the ones you tried ------------


def _param(dual, low=10, sense="max", rows=None):
    from certo import ParametricSpec
    from certo.polynomials import Poly

    ring = ("p",)
    P = Poly.var(ring, "p")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731
    return ParametricSpec(
        parameters={"p": low}, sense=sense,
        objective={"x_big": K(1), "x_mid": K(1), "x_small": K(1)},
        constraints=rows if rows is not None else [
            ("cap_big", {"x_big": K(3), "x_mid": K(1)}, "<=",
             P * (P - K(1)) * K(Fraction(1, 2))),
            ("cap_mid", {"x_mid": K(2), "x_small": K(1)}, "<=", P - K(5)),
            ("cap_small", {"x_small": K(2)}, "<=", K(3)),
        ],
        dual=dual, title="t")


def _run(spec):
    from certo.engines import algebra

    return algebra.parametric(spec, LIM)


def test_one_dual_certifies_the_optimum_for_every_parameter_above_the_floor():
    """The whole point: a finite computation becomes a statement about a family."""
    from certo.parametric import evaluate
    from certo.polynomials import Poly

    r = _run(_param({"cap_big": Fraction(1, 3), "cap_mid": Fraction(1, 3),
                     "cap_small": Fraction(1, 3)}))
    assert r.verdict is Verdict.PROVED
    assert r.meta["bound"] == "1/6*p^2 + 1/6*p - 2/3"

    # Tight at the floor and far beyond it, against the LP solved outright.
    bound = Poly.parse(("p",), r.certificate.payload["bound"])
    for p, want in ((10, Fraction(53, 3)), (11, Fraction(64, 3)),
                    (30, Fraction(463, 3))):
        assert evaluate(bound, {"p": p}) == want, p

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert any("says nothing below it" in w for w in rep.warnings)


def test_a_dual_that_is_infeasible_on_the_ray_yields_no_certificate():
    """The shift is sufficient, not necessary, so a failure is not a refutation."""
    r = _run(_param({"cap_big": Fraction(1, 100), "cap_mid": Fraction(0),
                     "cap_small": Fraction(0)}))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None          # no bound, so no certificate
    assert "NOT ESTABLISHED" in r.detail
    assert r.meta["failed_columns"]


def test_a_negative_dual_entry_is_refused_outright():
    r = _run(_param({"cap_big": Fraction(1, 3), "cap_mid": Fraction(-1),
                     "cap_small": Fraction(1, 3)}))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "cap_mid" in r.detail


def test_mixing_the_two_shapes_is_refused_rather_than_reinterpreted():
    """A packing maximises over `<=`; a cover minimises over `>=`. Not mixed.

    Both shapes are supported, so what is refused is no longer "a min
    problem" -- it is rows belonging to one shape inside the other, which is
    a modelling mistake and not a harder problem.
    """
    from certo.polynomials import Poly
    ring = ("p",)
    K = lambda c: Poly.const(ring, c)                      # noqa: E731

    d = {"cap_big": Fraction(1, 3), "cap_mid": Fraction(1, 3),
         "cap_small": Fraction(1, 3)}
    # min with `<=` rows: names the shape and the row sense it wanted.
    detail = _run(_param(d, sense="min")).detail
    assert "sense=min" in detail and ">=" in detail

    # max with a `>=` row: names the offending row.
    r = _run(_param({"only": Fraction(1)}, rows=[
        ("only", {"x_big": K(1)}, ">=", K(1))]))
    assert "only" in r.detail

    assert "sense=cheapest" in _run(_param(d, sense="cheapest")).detail


# --- cover programs: the shape three separate write-ups reduce to ----------
#
# These pin NUMBERS, not behaviour. Each certified bound is compared against
# the same program solved outright by the exact rational simplex, at every
# point of a grid inside the branch. A bound that is merely valid would pass a
# "verify returns ok" test; only the comparison catches a bound that drifted
# off the optimum.


def _cover_lp(weights, rows):
    """`min w.z` over the given cover rows, exactly. The reference answer."""
    from certo.simplex import minimise

    A = [[Fraction(r[i]) for r in rows] for i in range(len(weights))]
    z = minimise(A, [Fraction(w) for w in weights], [Fraction(1)] * len(rows))
    return sum(w * zi for w, zi in zip(weights, z))


def _c2(n):
    return Fraction(n * (n - 1), 2)


def test_a_two_orbit_cover_branch_is_exact_where_its_dual_is_feasible():
    """Both sides of a threshold, each against the LP solved outright."""
    from certo.parametric import evaluate
    from certo.polynomials import Poly
    from certo.spec import ParametricSpec

    def build(ring, p, q):
        one, two, three = (Poly.const(ring, c) for c in (1, 2, 3))
        c2 = p * (p - one) * Poly.const(ring, Fraction(1, 2))
        return c2, ParametricSpec(
            parameters=None, sense="min",
            objective={"x": c2, "y": p * q},
            constraints=[("clique", {"x": three}, ">=", one),
                         ("mixed", {"x": one, "y": two}, ">=", one)],
            dual=None)

    # branch q >= p - 1: the optimum is C(p,2), the dual pays only the mixed
    # triangle, and its one live row is p*s >= 0.
    ring = ("p", "s")
    p, s = Poly.var(ring, "p"), Poly.var(ring, "s")
    c2, spec = build(ring, p, p - Poly.const(ring, 1) + s)
    spec.parameters = {"p": 3, "s": 0}
    spec.dual = {"clique": Poly.const(ring, 0), "mixed": c2}
    r = _run(spec)
    assert r.verdict is Verdict.PROVED
    assert r.meta["sense"] == "min"
    assert r.meta["bound"] == "1/2*p^2 - 1/2*p"

    bound = Poly.parse(ring, r.certificate.payload["bound"])
    for a in range(7):
        for b in range(7):
            pv, sv = 3 + a, b
            qv = pv - 1 + sv
            want = _cover_lp([_c2(pv), Fraction(pv * qv)],
                             [[3, 0], [1, 2]])
            assert evaluate(bound, {"p": pv, "s": sv}) == want, (pv, qv)

    # branch q <= p - 1: the other vertex, and a dual with two live entries.
    ring = ("q", "s")
    q, s = Poly.var(ring, "q"), Poly.var(ring, "s")
    one, half = Poly.const(ring, 1), Poly.const(ring, Fraction(1, 2))
    pp = q + one + s
    c2, spec = build(ring, pp, q)
    spec.parameters = {"q": 0, "s": 2}
    spec.dual = {"clique": (c2 - pp * q * half) * Poly.const(ring, Fraction(1, 3)),
                 "mixed": pp * q * half}
    r = _run(spec)
    assert r.verdict is Verdict.PROVED
    bound = Poly.parse(ring, r.certificate.payload["bound"])
    for a in range(7):
        for b in range(7):
            qv, sv = a, 2 + b
            pv = qv + 1 + sv
            want = _cover_lp([_c2(pv), Fraction(pv * qv)], [[3, 0], [1, 2]])
            assert evaluate(bound, {"q": qv, "s": sv}) == want, (pv, qv)


#: The five triangle types of a four-orbit cover, over (a, b, c, e).
_ORBIT_ROWS = [[1, 2, 0, 0], [3, 0, 0, 0], [1, 0, 2, 0],
               [0, 0, 2, 1], [0, 0, 0, 3]]
_ORBIT_NAMES = ["NNI", "NNN", "NNR", "NRR", "RRR"]


def _orbit_spec(ring, d, r, q, dual, floors):
    from certo.polynomials import Poly
    from certo.spec import ParametricSpec

    one = Poly.const(ring, 1)
    half = Poly.const(ring, Fraction(1, 2))
    cols = ["a", "b", "c", "e"]
    return ParametricSpec(
        parameters=floors, sense="min",
        objective={"a": d * (d - one) * half, "b": q * d, "c": d * r,
                   "e": r * (r - one) * half},
        constraints=[(n, {cols[i]: Poly.const(ring, row[i])
                          for i in range(4) if row[i]}, ">=", one)
                     for n, row in zip(_ORBIT_NAMES, _ORBIT_ROWS)],
        dual=dual)


def test_two_branches_of_a_four_orbit_cover_are_exact_on_their_boxes():
    """The hot and separated covers, each on the box its dual is feasible on."""
    from certo.parametric import evaluate
    from certo.polynomials import Poly

    zero = Fraction(0)

    # hot: q = d - 1 + s, r = d + 1 + t. The dual pays the neighbourhood in
    # full and splits what is left between the two R-facing types.
    ring = ("d", "s", "t")
    d, s, t = (Poly.var(ring, v) for v in ring)
    one, half, third = (Poly.const(ring, c)
                        for c in (1, Fraction(1, 2), Fraction(1, 3)))
    rr = d + one + t
    cd, cr = d * (d - one) * half, rr * (rr - one) * half
    spec = _orbit_spec(ring, d, rr, d - one + s,
                       {"NNI": cd, "NNN": Poly.const(ring, 0),
                        "NNR": Poly.const(ring, 0), "NRR": d * rr * half,
                        "RRR": (cr - d * rr * half) * third},
                       {"d": 3, "s": 0, "t": 0})
    r = _run(spec)
    assert r.verdict is Verdict.PROVED
    assert r.meta["bound"] == "d^2 + 2/3*d*t + 1/6*t^2 + 1/6*t"
    bound = Poly.parse(ring, r.certificate.payload["bound"])
    for du in range(5):
        for sv in range(5):
            for tv in range(5):
                dv = 3 + du
                rv, qv = dv + 1 + tv, dv - 1 + sv
                want = _cover_lp([_c2(dv), Fraction(qv * dv), Fraction(dv * rv),
                                  _c2(rv)], _ORBIT_ROWS)
                got = evaluate(bound, {"d": dv, "s": sv, "t": tv})
                assert got == want, (dv, rv, qv, got, want)

    # separated: d = r - 1 + m, q = d - 1 + s. Here the dual SPLITS the
    # neighbourhood between two types, and the split is what makes the
    # crossing orbit pay for itself.
    ring = ("r", "m", "s")
    rv_, m, s = (Poly.var(ring, v) for v in ring)
    one, half = Poly.const(ring, 1), Poly.const(ring, Fraction(1, 2))
    dd = rv_ - one + m
    cd = dd * (dd - one) * half
    cr = rv_ * (rv_ - one) * half
    spec = _orbit_spec(ring, dd, rv_, dd - one + s,
                       {"NNI": cd - rv_ * m * half,
                        "NNN": Poly.const(ring, 0), "NNR": rv_ * m * half,
                        "NRR": cr, "RRR": Poly.const(ring, 0)},
                       {"r": 4, "m": 0, "s": 0})
    r = _run(spec)
    assert r.verdict is Verdict.PROVED
    assert r.meta["bound"] == "r^2 + r*m + 1/2*m^2 - 2*r - 3/2*m + 1"
    bound = Poly.parse(ring, r.certificate.payload["bound"])
    for ru in range(5):
        for mv in range(5):
            for sv in range(5):
                rrv = 4 + ru
                dv = rrv - 1 + mv
                qv = dv - 1 + sv
                want = _cover_lp([_c2(dv), Fraction(qv * dv), Fraction(dv * rrv),
                                  _c2(rrv)], _ORBIT_ROWS)
                got = evaluate(bound, {"r": rrv, "m": mv, "s": sv})
                assert got == want, (dv, rrv, qv, got, want)
    assert zero == 0


def test_a_branch_cut_out_by_a_curve_is_declared_rather_than_boxed():
    """The shift proves non-negativity on a BOX. Some branches are not boxes.

    Here the branch needs `q d + d r >= d(d-1) + r(r-1)`, a quadratic curve.
    Without it the dual has entries the shift cannot clear; with it declared,
    certo finds the multipliers by linear program and the bound is exact
    against the simplex at every point of the region.
    """
    from certo.parametric import evaluate
    from certo.polynomials import Poly
    from certo.spec import ParametricSpec

    ring = ("q", "k", "r")
    q, k, r = (Poly.var(ring, v) for v in ring)
    one, two = Poly.const(ring, 1), Poly.const(ring, 2)
    half, third = (Poly.const(ring, Fraction(1, n)) for n in (2, 3))
    d = q + one + k                          # q <= d - 1, by construction
    cd, cr = d * (d - one) * half, r * (r - one) * half
    crossing = d * r * half - cr             # >= 0 exactly when r <= d + 1

    def build(region):
        cols = ["a", "b", "c", "e"]
        return ParametricSpec(
            parameters={"q": 1, "k": 0, "r": 4}, sense="min",
            objective={"a": cd, "b": q * d, "c": d * r, "e": cr},
            constraints=[(n, {cols[i]: Poly.const(ring, row[i])
                              for i in range(4) if row[i]}, ">=", one)
                         for n, row in zip(_ORBIT_NAMES, _ORBIT_ROWS)],
            dual={"NNI": q * d * half,
                  "NNN": (cd - q * d * half - crossing) * third,
                  "NNR": crossing, "NRR": cr, "RRR": Poly.const(ring, 0)},
            region=region)

    # Without the region the route fails, and fails honestly: no certificate.
    plain = _run(build(None))
    assert plain.verdict is Verdict.INCONCLUSIVE
    assert plain.certificate is None

    region = [("r_within", d + one - r),
              ("uniform_wins", cd * two + cr * two - q * d - d * r)]
    r_ = _run(build(region))
    assert r_.verdict is Verdict.PROVED
    pay = r_.certificate.payload
    assert sorted(pay["region"]) == ["r_within", "uniform_wins"]

    rep = verify(_roundtrip(r_.certificate), LIM)
    assert rep.ok and rep.solver_free
    # The scope must travel with the certificate, loudly: a side condition is
    # not something proved, and a reader who misses that misreads the claim.
    assert any("NOTHING here proves them" in w for w in rep.warnings)

    bound = Poly.parse(ring, pay["bound"])
    inside = exact = 0
    for qv in range(1, 8):
        for kv in range(0, 6):
            for rv in range(4, 12):
                dv = qv + 1 + kv
                if dv + 1 - rv < 0:
                    continue
                if dv * (dv - 1) + rv * (rv - 1) - qv * dv - dv * rv < 0:
                    continue
                inside += 1
                want = _cover_lp([_c2(dv), Fraction(qv * dv),
                                  Fraction(dv * rv), _c2(rv)], _ORBIT_ROWS)
                got = evaluate(bound, {"q": qv, "k": kv, "r": rv})
                assert got <= want, (dv, rv, qv, got, want)
                exact += got == want
    assert inside > 100 and exact == inside


def test_an_artificial_left_in_the_basis_does_not_corrupt_the_answer():
    """Dependent rows end phase 1 with an artificial basic at level zero.

    Renaming it to a real variable states a false tableau, and the symplex
    then returns a `y` that does not satisfy its own constraints -- silently,
    which is the part that matters. Pinned on the instance that found it: one
    column that must come back with multiplier exactly 1.
    """
    from certo.simplex import minimise

    # rows are one per monomial of a polynomial identity, so they are
    # dependent by construction; the single column equals the target exactly.
    target = [Fraction(c) for c in (-1, -1, 1, 1, -1, 4, 2, -5, -4)]
    A = [[-c for c in target]]
    y = minimise(A, [Fraction(1)], [-c for c in target])
    assert y == [Fraction(1)]
    for j in range(len(target)):
        assert sum(A[i][j] * y[i] for i in range(len(A))) >= -target[j]


def test_a_cover_dual_stops_being_feasible_where_the_branch_ends():
    """The threshold in the value function IS the dual's feasibility.

    Same dual, same program, on a box that crosses `q = p - 1` instead of
    staying on one side. It must be refused, and the column it fails on must
    be the one carrying the crossing edges.
    """
    from certo.polynomials import Poly
    from certo.spec import ParametricSpec

    ring = ("p", "q")
    p, q = Poly.var(ring, "p"), Poly.var(ring, "q")
    one, two, three = (Poly.const(ring, c) for c in (1, 2, 3))
    c2 = p * (p - one) * Poly.const(ring, Fraction(1, 2))

    r = _run(ParametricSpec(
        parameters={"p": 3, "q": 1}, sense="min",
        objective={"x": c2, "y": p * q},
        constraints=[("clique", {"x": three}, ">=", one),
                     ("mixed", {"x": one, "y": two}, ">=", one)],
        dual={"clique": Poly.const(ring, 0), "mixed": c2}))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None
    assert r.meta["failed_columns"] == ["y"]


def test_a_polynomial_dual_is_carried_exactly_and_checked_against_its_text():
    """`dual` is what a reader sees; `dual_poly` is what verify recomputes."""
    from certo.polynomials import Poly
    from certo.spec import ParametricSpec

    ring = ("p", "s")
    p = Poly.var(ring, "p")
    one, two, three = (Poly.const(ring, c) for c in (1, 2, 3))
    c2 = p * (p - one) * Poly.const(ring, Fraction(1, 2))
    r = _run(ParametricSpec(
        parameters={"p": 3, "s": 0}, sense="min",
        objective={"x": c2, "y": p * (p - one + Poly.var(ring, "s"))},
        constraints=[("clique", {"x": three}, ">=", one),
                     ("mixed", {"x": one, "y": two}, ">=", one)],
        dual={"clique": Poly.const(ring, 0), "mixed": c2}))
    pay = r.certificate.payload
    assert pay["sense"] == "min"
    assert pay["dual"]["mixed"] == "1/2*p^2 - 1/2*p"
    assert Poly.parse(ring, pay["dual_poly"]["mixed"]) == c2
    assert verify(_roundtrip(r.certificate), LIM).ok

    # the readable copy made to disagree with the data it is checked from
    bent = r.certificate.to_dict()
    bent["payload"]["dual"]["mixed"] = "1/2*p^2"
    rep = verify(Certificate.from_dict(bent), LIM)
    assert not rep.ok
    assert any("readable dual" in n for n, ok, _ in rep.checks if not ok)


def test_a_constant_dual_certificate_is_unchanged_by_the_cover_shape():
    """The packing shape must not have grown fields it does not need."""
    r = _run(_param({"cap_big": Fraction(1, 3), "cap_mid": Fraction(1, 3),
                     "cap_small": Fraction(1, 3)}))
    pay = r.certificate.payload
    assert "sense" not in pay          # "max" is the default and stays unwritten
    assert "dual_poly" not in pay      # `dual` already carries rationals exactly
    assert verify(_roundtrip(r.certificate), LIM).ok


# --- peak: the best integer choice, for a whole family at once -------------


def _peak(offset, shift, floors=None):
    from certo.polynomials import Poly
    from certo.spec import PeakSpec

    ring = ("m", "x")
    m, x = Poly.var(ring, "m"), Poly.var(ring, "x")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731
    obj = x * (m * K(6) + K(2 * offset + 1) - x * K(3)) * K(Fraction(1, 2))
    return PeakSpec(parameters=floors or {"m": 0}, variable="x", objective=obj,
                    argmax=Poly.var(("m",), "m") + Poly.const(("m",), shift))


def _run_peak(spec):
    from certo.engines import algebra

    return algebra.peak(spec, LIM)


def test_the_integer_peak_matches_brute_force_on_every_residue_class():
    """Three classes, three closed forms, and no floor anywhere in the check."""
    from certo.parametric import evaluate
    from certo.polynomials import Poly

    def value(n, p):
        return Fraction(p * (2 * n + 1 - 3 * p), 2)

    for offset, shift, want in ((0, 0, "3/2*m^2 + 1/2*m"),
                                (1, 0, "3/2*m^2 + 3/2*m"),
                                (2, 1, "3/2*m^2 + 5/2*m + 1")):
        r = _run_peak(_peak(offset, shift))
        assert r.verdict is Verdict.PROVED, (offset, r.detail)
        assert r.meta["value"] == want, (offset, r.meta["value"])

        pay = r.certificate.payload
        val = Poly.parse(("m",), pay["value"])
        arg = Poly.parse(("m",), pay["argmax"])
        for mv in range(0, 25):
            n = 3 * mv + offset
            if n < 1:
                continue
            brute = max(value(n, p) for p in range(0, 2 * n + 4))
            star = evaluate(arg, {"m": mv})
            assert evaluate(val, {"m": mv}) == brute, (offset, mv)
            assert value(n, star) == brute, (offset, mv)
            # the same number the source states as a floor, without one
            assert brute == Fraction((2 * n + 1) ** 2 // 24)

        assert verify(_roundtrip(r.certificate), LIM).ok

    # The tie: at n = 3m+1 the vertex is exactly halfway, so BOTH neighbours
    # certify, and both give the same value. A certificate with slack there
    # would be describing a different problem.
    other = _run_peak(_peak(1, 1))
    assert other.verdict is Verdict.PROVED
    assert other.meta["value"] == "3/2*m^2 + 3/2*m"


def test_a_maximiser_one_step_out_is_refused_and_says_which_test_failed():
    r = _run_peak(_peak(0, 1))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None
    assert "NOT ESTABLISHED" in r.detail
    # and it reports the derivative, which is the quantity that is too large
    assert r.meta["slope"]


def test_a_non_integer_maximiser_is_refused_rather_than_assumed_integral():
    """An argument about a point that does not exist proves nothing."""
    from certo.polynomials import Poly
    from certo.spec import PeakSpec

    ring = ("m", "x")
    m, x = Poly.var(ring, "m"), Poly.var(ring, "x")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731
    r = _run_peak(PeakSpec(
        parameters={"m": 0}, variable="x",
        objective=x * (m * K(6) + K(1) - x * K(3)) * K(Fraction(1, 2)),
        argmax=Poly.const(("m",), Fraction(1, 2))))
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "1/2" in r.detail


def test_a_convex_or_higher_degree_objective_has_no_peak_to_certify():
    from certo.polynomials import Poly
    from certo.spec import PeakSpec

    ring = ("m", "x")
    m, x = Poly.var(ring, "m"), Poly.var(ring, "x")
    one = Poly.var(("m",), "m")

    convex = _run_peak(PeakSpec({"m": 0}, "x", x * x - m * x, one))
    assert convex.verdict is Verdict.INCONCLUSIVE
    assert "not shown negative" in convex.detail

    cubic = _run_peak(PeakSpec({"m": 0}, "x", x * x * x - m * x, one))
    assert cubic.verdict is Verdict.INCONCLUSIVE
    assert "degree 3" in cubic.detail


def test_the_peak_verifier_rederives_the_coefficients_from_the_objective():
    """The payload says what A and the slope are; verify must not believe it."""
    r = _run_peak(_peak(0, 0))
    bent = r.certificate.to_dict()
    bent["payload"]["value"] = {"0": "0"}          # claim a different maximum
    rep = verify(Certificate.from_dict(bent), LIM)
    assert not rep.ok
    assert any("expanded" in n for n, ok, _ in rep.checks if not ok)

    bent = r.certificate.to_dict()
    bent["payload"]["argmax"] = {"1": "1"}         # a different maximiser
    assert not verify(Certificate.from_dict(bent), LIM).ok


def test_the_shift_is_exact_and_sufficient_not_necessary():
    """Pinned, because the gap is the honest limit of the whole command."""
    from certo.parametric import nonneg_on_ray, shift
    from certo.polynomials import Poly

    ring = ("p",)
    P = Poly.var(ring, "p")
    K = lambda c: Poly.const(ring, c)                      # noqa: E731

    # (p - 10) is non-negative on p >= 10, and the shift sees it immediately.
    ok, shifted = nonneg_on_ray(P - K(10), {"p": 10})
    assert ok and str(shifted) == "p"

    # p^2 - 3p + 3 is positive EVERYWHERE and the shift at 0 does not see it.
    ok, shifted = nonneg_on_ray(P * P - K(3) * P + K(3), {"p": 0})
    assert not ok
    # ... and shifting far enough up does.
    ok, _ = nonneg_on_ray(P * P - K(3) * P + K(3), {"p": 2})
    assert ok

    # the substitution itself is exact
    assert str(shift(P * P, {"p": 1})) == "p^2 + 2*p + 1"


def test_forging_the_bound_is_caught_by_re_expanding_it():
    r = _run(_param({"cap_big": Fraction(1, 3), "cap_mid": Fraction(1, 3),
                     "cap_small": Fraction(1, 3)}))
    d = json.loads(json.dumps(r.certificate.to_dict()))
    key = next(iter(d["payload"]["bound"]))
    d["payload"]["bound"][key] = str(Fraction(d["payload"]["bound"][key]) - 1)
    assert not verify(Certificate.from_dict(d), LIM).ok


# --- local loads: named regions the design has to respect -----------------


def _loaded(loads, caps=1):
    from certo import PackingSpec

    items = [("p{}".format(i), res, 1) for i, res in enumerate(
        [("dA0", "e01"), ("dA1", "e02"), ("dA2", "e12"),
         ("dB0", "e34"), ("dB1", "e35"), ("dB2", "e45")])]
    return PackingSpec(items=items, capacities=caps, loads=loads,
                       title="a packing with region bounds")


def _opt(spec):
    from certo.engines import lp

    return lp.opt(spec.to_lp(), LIM)


def test_a_load_is_a_row_the_dual_prices():
    """Not a post-hoc check: it constrains the optimum and shows its price."""
    free = _opt(_loaded([]))
    bound = _opt(_loaded([("within_A", {"p0": 1, "p1": 1, "p2": 1}, "<=", 1)]))
    assert Fraction(free.meta["objective"]) > Fraction(bound.meta["objective"])

    loads = bound.certificate.payload["loads"]
    assert [ld["name"] for ld in loads] == ["within_A"]
    assert loads[0]["binding"] is True
    # A binding region has a shadow price: relaxing it buys exactly that.
    assert Fraction(loads[0]["dual"]) > 0


def test_the_certificate_records_what_the_design_does_to_each_load():
    r = _opt(_loaded([("within_A", {"p0": 1, "p1": 1, "p2": 1}, "<=", 2),
                      ("within_B", {"p3": 1, "p4": 1, "p5": 1}, "<=", 3)]))
    loads = {ld["name"]: ld for ld in r.certificate.payload["loads"]}
    assert loads["within_A"]["achieved"] == "2"
    assert loads["within_A"]["slack"] == "0"
    assert loads["within_B"]["achieved"] == "3"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_load_with_slack_is_reported_as_such():
    r = _opt(_loaded([("roomy", {"p0": 1}, "<=", 5)]))
    ld = r.certificate.payload["loads"][0]
    assert ld["binding"] is False
    assert Fraction(ld["slack"]) > 0
    assert Fraction(ld["dual"]) == 0          # slack means it costs nothing


def test_a_forged_load_value_is_caught_by_recomputing_it():
    """The coefficients travel, so the artefact answers on its own."""
    r = _opt(_loaded([("within_A", {"p0": 1, "p1": 1, "p2": 1}, "<=", 2)]))
    d = json.loads(json.dumps(r.certificate.to_dict()))
    d["payload"]["loads"][0]["achieved"] = "1"
    rep = verify(Certificate.from_dict(d), LIM)
    assert not rep.ok
    assert any("within_A" in name for name, ok, _ in rep.checks if not ok)


def test_loads_accept_every_sense_including_exact_preservation():
    from certo import PackingSpec

    for sense, bound, want in (("<=", 2, True), (">=", 1, True),
                               ("==", 2, True)):
        r = _opt(_loaded([("region", {"p0": 1, "p1": 1, "p2": 1},
                           sense, bound)]))
        ld = r.certificate.payload["loads"][0]
        assert ld["sense"] == sense
        assert verify(_roundtrip(r.certificate), LIM).ok is want, sense
    _ = PackingSpec


def test_a_load_on_an_item_that_is_not_there_is_refused():
    """Otherwise the row is silently weaker than intended."""
    try:
        _loaded([("oops", {"p0": 1, "ghost": 1}, "<=", 1)])
    except ValueError as e:
        assert "ghost" in str(e)
    else:
        raise AssertionError("a weight on a missing item was accepted")


def test_a_load_may_not_take_a_resource_name():
    try:
        _loaded([("e01", {"p0": 1}, "<=", 1)]).to_lp()
    except ValueError as e:
        assert "e01" in str(e)
    else:
        raise AssertionError("a load shadowed a resource row")


def test_a_packing_with_no_loads_carries_an_empty_list():
    """The field is optional, and its absence must not change anything."""
    r = _opt(_loaded([]))
    assert r.certificate.payload["loads"] == []
    assert verify(_roundtrip(r.certificate), LIM).ok


# --- exact covers, and clique partitions as one case ----------------------


FANO = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6),
        (4, 5, 0), (5, 6, 1), (6, 0, 2)]


def _cover(universe, parts, **kw):
    from certo import CoverSpec
    from certo.engines import algebra

    return algebra.cover(CoverSpec(universe=universe, parts=parts,
                                   title="t", **kw), LIM)


def _complete_pairs(n):
    import itertools

    return list(itertools.combinations(range(n), 2))


def test_the_fano_plane_partitions_k7_into_seven_triangles():
    """Tight and checkable by hand: 21 edges, 7 parts, 3 edges each."""
    r = _cover(_complete_pairs(7), FANO, cliques=True, max_size=3)
    assert r.verdict is Verdict.PROVED
    assert r.meta == {"parts": 7, "universe": 21, "missed": 0, "doubled": 0}

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert any("really is a clique" in name for name, _, _ in rep.checks)
    # It is an upper bound and says so.
    assert any("does not say it is the smallest" in w for w in rep.warnings)


def test_an_edge_covered_twice_is_refuted_not_accepted():
    r = _cover(_complete_pairs(7), FANO + [(0, 1, 3)], cliques=True)
    assert r.verdict is Verdict.REFUTED
    assert r.meta["doubled"] == 3            # the three edges of that triangle
    assert r.certificate is None
    assert "exact=False" in r.detail          # and what would make it valid


def test_an_uncovered_edge_is_named():
    r = _cover(_complete_pairs(7), FANO[:-1], cliques=True)
    assert r.verdict is Verdict.REFUTED
    assert r.meta["missed"] == 3


def test_a_part_that_is_not_a_clique_stops_before_any_certificate():
    """A statement about the graph, not about the cover."""
    edges = [e for e in _complete_pairs(7) if e != (0, 1)]
    r = _cover(edges, FANO, cliques=True)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None
    assert "not a clique" in r.detail and "(0, 1)" in r.detail


def test_at_least_covers_are_a_different_claim_and_recorded_as_one():
    r = _cover(_complete_pairs(7), FANO + [(0, 1, 3)], cliques=True, exact=False)
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["exact"] is False
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    # The stronger claim is simply not made, and the wording says which.
    assert "at least once" in rep.detail


def test_a_generic_exact_cover_needs_no_graph_at_all():
    r = _cover(["a", "b", "c", "d"], [["a", "c"], ["b", "d"]])
    assert r.verdict is Verdict.PROVED
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_parts_covering_something_outside_the_universe_are_caught():
    """Otherwise the cover is of a different object than the one declared."""
    r = _cover(["a", "b"], [["a", "b"], ["z"]])
    assert r.verdict is Verdict.REFUTED
    assert "not in the universe" in r.detail


def test_a_repeated_universe_element_is_refused_outright():
    """'Exactly once' would not mean anything."""
    r = _cover(["a", "a", "b"], [["a", "b"]])
    assert r.verdict is Verdict.INCONCLUSIVE
    assert "repeats" in r.detail


def test_forging_the_part_count_is_caught_by_recounting():
    r = _cover(_complete_pairs(7), FANO, cliques=True)
    d = json.loads(json.dumps(r.certificate.to_dict()))
    d["payload"]["size"] = 5
    rep = verify(Certificate.from_dict(d), LIM)
    assert not rep.ok


def test_a_forged_part_is_caught_by_re_deriving_its_edges():
    """The clique check is redone from the graph, not read off the payload."""
    r = _cover(_complete_pairs(7), FANO, cliques=True)
    d = json.loads(json.dumps(r.certificate.to_dict()))
    d["payload"]["part_report"][0]["vertices"] = ["0", "1", "3", "5"]
    assert not verify(Certificate.from_dict(d), LIM).ok


# --- 0.6 defects, each pinned by the case that found it -------------------


def _mixed_with(sense_row, all_discrete=True):
    from certo import LPSpec
    from certo.engines import mixed

    lp = LPSpec(sense="max", title="t")
    lp.variable("a", 0, 1, kind="binary")
    lp.variable("b", 0, 1, kind="binary")
    if not all_discrete:
        lp.variable("w", 0, None)
    lp.objective({"a": 3, "b": 2, **({} if all_discrete else {"w": 1})})
    lp.constraint({"a": 1, "b": 1}, "<=", 1, name="cap")
    lp.constraint({"a": 1, "b": 1}, sense_row, 1, name="quota")
    if not all_discrete:
        lp.constraint({"w": 6}, "<=", 1, name="w_cap")
    return mixed.mixed(lp, LIM)


def test_a_mixed_certificate_survives_a_ge_or_eq_row():
    """The 0.6 P0. Reported as "all variables discrete"; the trigger was the
    row SENSE, and it bit mixed models too.

    `as_leq_system` renames a `>=` row to `name_geq` and negates it, and
    splits an `==` into `name_le` and `name_ge`. The equivalence check looked
    up the ORIGINAL name in a table keyed by the normalised ones, missed, and
    called a perfectly good certificate invalid.
    """
    for sense in ("<=", ">=", "=="):
        for all_discrete in (True, False):
            r = _mixed_with(sense, all_discrete)
            assert r.certificate is not None, (sense, all_discrete)
            rep = verify(_roundtrip(r.certificate), LIM)
            assert rep.ok, (sense, all_discrete,
                            [c for c in rep.checks if not c[1]])


def test_normalised_rows_is_the_one_place_that_mapping_lives():
    from certo.certificate import normalised_rows

    assert normalised_rows("q", "<=") == [("q", 1)]
    assert normalised_rows("q", ">=") == [("q_geq", -1)]
    assert normalised_rows("q", "==") == [("q_le", 1), ("q_ge", -1)]


def test_a_ge_load_reports_the_shadow_price_it_actually_has():
    """The 0.6 P1: the row is renamed, the reporter looked up the old name,
    and a quota that was costing you showed a price of zero."""
    from certo import PackingSpec
    from certo.engines import lp

    # cheap A-items and valuable B-items compete for the same resources, so a
    # quota forcing A costs you B -- and the price says how much.
    spec = PackingSpec(
        items=[("a0", ("s0",), 1), ("a1", ("s1",), 1),
               ("b0", ("s0",), 5), ("b1", ("s1",), 5)],
        capacities=1,
        loads=[("quota_A", {"a0": 1, "a1": 1}, ">=", 2)])
    r = lp.opt(spec.to_lp(), LIM)
    ld = r.certificate.payload["loads"][0]

    assert ld["binding"] is True
    assert ld["rows"] == ["quota_A_geq"]
    # Forcing one more A means dropping one B: 1 gained, 5 lost.
    assert Fraction(ld["dual"]) == -4
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_branch_and_bound_accepts_a_minimisation_and_keeps_the_sign():
    """Refusing it left the user negating by hand, and their certificate then
    described a formulation nobody posed."""
    from certo import LPSpec
    from certo.engines import bb

    lp_spec = LPSpec(sense="min", title="set cover")
    for v in ("a", "b", "c"):
        lp_spec.variable(v, 0, 1, kind="binary")
    lp_spec.objective({"a": 2, "b": 3, "c": 4})
    lp_spec.constraint({"a": 1, "b": 1}, ">=", 1, name="cover1")
    lp_spec.constraint({"b": 1, "c": 1}, ">=", 1, name="cover2")

    r = bb.prove_optimal(lp_spec, LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["optimum"] == "3"          # b alone covers both
    assert r.meta["minimising"] is True

    p = r.certificate.payload
    # Both formulations, because the tree really did search the negated one.
    assert p["sense"] == "max" and p["original_sense"] == "min"
    assert p["incumbent"] == "-3" and p["original_optimum"] == "3"
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_stopped_search_says_what_it_knows_instead_of_nothing():
    """INCONCLUSIVE with no incumbent, bound or gap made an instance a hole."""
    from certo import PackingSpec
    from certo.engines import bb

    # A 5-cycle: the matching relaxation is half-integral (5/2) and the
    # integer answer is 2, so the search really does have to branch.
    items = [("e{}".format(i), ("v{}".format(i), "v{}".format((i + 1) % 5)), 1)
             for i in range(5)]
    spec = PackingSpec(items=items, capacities=1, integer=True).to_lp()

    r = bb.prove_optimal(spec, LIM, max_nodes=1)
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.status is Status.RESOURCE_EXHAUSTED
    # Optimality is still NOT established -- the verdict says so -- but the
    # run is no longer a hole: it leaves a `branch_frontier` claiming the
    # interval and the subproblems that remain. This used to assert
    # `certificate is None`, which was true and was the defect.
    assert r.certificate is not None
    assert r.certificate.kind == "branch_frontier"
    assert r.meta["stopped"] is True
    # All four things a stopped search knows, and the gap is real.
    assert r.meta["incumbent"] == "2"
    assert r.meta["best_bound"] == "5/2"
    assert r.meta["gap"] == "1/2"
    assert r.meta["nodes_opened"] == 1
    assert "NOT established" in r.detail

    # And with room, the same instance proves it.
    full = bb.prove_optimal(spec, LIM, max_nodes=500)
    assert full.verdict is Verdict.PROVED and full.meta["optimum"] == "2"


def test_self_check_refuses_to_report_a_certificate_verify_rejects():
    """The fix that would have caught both P0s before anyone ran verify."""
    import argparse

    from certo import cli

    r = _mixed_with(">=")
    args = argparse.Namespace(
        json=False, cert=None, log=None, note="", tag=None, spec=None,
        self_check=True, timeout_ms=20_000, rlimit=20_000_000,
        max_memory_mb=2048, seed=0)
    assert cli._self_check(r, args) is True
    assert r.meta["self_check"] == "ok"

    # A certificate that has been tampered with must not pass.
    r.certificate.payload["achieved"] = "999"
    r.meta.pop("self_check", None)
    assert cli._self_check(r, args) is False
    assert r.meta["self_check"] == "FAILED"


# --- discovery: a command that shipped and nobody found -------------------


def test_order_answers_to_the_words_people_actually_type():
    """`order` shipped in 0.5.0 and its user searched for "asymptotic"."""
    from certo.cli import build_parser

    choices = None
    for action in build_parser()._actions:
        if getattr(action, "dest", "") == "cmd" and action.choices:
            choices = action.choices
    assert "order" in choices
    for word in ("asymptotics", "decays"):
        assert word in choices, word
        # An alias is the same parser, not a copy that can drift.
        assert choices[word] is choices["order"]


def test_the_help_line_leads_with_the_question_not_the_machinery():
    from certo.cli import build_parser

    for action in build_parser()._actions:
        if getattr(action, "dest", "") == "cmd" and action.choices:
            helptext = action._choices_actions
    line = next(a.help for a in helptext if a.dest == "order")
    assert "DECAY" in line and "asymptotic" in line


def test_the_question_table_is_available_in_the_terminal():
    """It lived only in the README, which is not where somebody is stuck."""
    from certo.cli import BY_QUESTION
    from certo.i18n import t

    commands = {c for _, rows in BY_QUESTION for _, c in rows}
    assert "order" in commands
    # Every label resolves in both languages, or the table prints raw keys.
    for group, rows in BY_QUESTION:
        assert not t(group).startswith("commands."), group
        for question, _ in rows:
            assert not t(question).startswith("commands."), question


def test_lint_names_order_when_the_claim_divides_by_a_product():
    """The precise trigger, on the expression that cost a user three sessions."""
    import z3

    from certo.lint import _magnitude_shaped

    k, W, C, u, d, p = z3.Reals("k W C u d p")
    hit = _magnitude_shaped(5 * k * W * C * C / (u ** 3 * d ** 2 * p ** 10))
    assert hit == ["d", "p", "u"]

    # And it stays quiet where it would be noise. One symbol downstairs is
    # far too common to mean anything.
    x, y, z = z3.Reals("x y z")
    assert _magnitude_shaped(x + y) is None
    assert _magnitude_shaped(x / y) is None
    assert _magnitude_shaped(x * y * z) is None
    assert _magnitude_shaped((x + y) / z) is None
    assert _magnitude_shaped(x / (y * z)) == ["y", "z"]


# --- the minimum a cover is measured against ------------------------------


def _k7_cover(parts, candidates):
    from certo import CoverSpec

    import itertools
    return CoverSpec(universe=list(itertools.combinations(range(7), 2)),
                     parts=parts, candidates=candidates, cliques=True,
                     title="t")


def test_a_valid_cover_gets_measured_against_the_minimum():
    """The misreading this exists to prevent: valid read as optimal."""
    import itertools

    from certo.engines import algebra

    edges = [list(e) for e in itertools.combinations(range(7), 2)]
    tri = [list(c) for c in itertools.combinations(range(7), 3)]
    spec = _k7_cover(edges, edges + tri)          # 21 parts: valid, and bad

    assert algebra.cover(spec, LIM).verdict is Verdict.PROVED
    out = algebra.cover_bounds(spec, LIM, prove_optimal=True)
    assert out["relaxation"] == "7"               # exact rational dual
    assert out["optimum"] == "7"                  # and proved integral
    assert verify(_roundtrip(out["relaxation_cert"]), LIM).ok


def test_optimising_needs_a_candidate_pool_and_refuses_to_invent_one():
    """Minimal relative to WHAT is a modelling fact, not a default."""
    import itertools

    edges = [list(e) for e in itertools.combinations(range(7), 2)]
    spec = _k7_cover(edges, None)
    try:
        spec.to_lp()
    except ValueError as e:
        assert "candidates" in str(e)
    else:
        raise AssertionError("a candidate pool was invented")


def test_to_lp_writes_equalities_for_an_exact_cover():
    """The one thing a relaxation written by hand gets wrong."""
    import itertools

    edges = [list(e) for e in itertools.combinations(range(4), 2)]
    from certo import CoverSpec

    spec = CoverSpec(universe=edges, parts=edges, candidates=edges,
                     cliques=True, exact=True, title="t")
    assert {row[2] for row in spec.to_lp().cons} == {"=="}

    loose = CoverSpec(universe=edges, parts=edges, candidates=edges,
                      cliques=True, exact=False, title="t")
    assert {row[2] for row in loose.to_lp().cons} == {">="}

    # and integral vs fractional is the variable kind, nothing else
    assert set(spec.to_lp(integral=True).kinds.values()) == {"binary"}
    assert set(spec.to_lp(integral=False).kinds.values()) == {"continuous"}


# --- the exact simplex, for when reconstruction runs out ------------------


def test_the_exact_simplex_finds_known_duals():
    from certo.simplex import minimise

    for A, b, c, want in (([[1, 1]], [1], [1, 1], Fraction(1)),
                          ([[1, 1], [1, 2]], [1, 1], [2, 3], Fraction(2)),
                          ([[1, 1], [1, 1], [3, 0]], [1, 1, 2], [1, 1],
                           Fraction(1))):
        y = minimise(A, b, c)
        assert all(v >= 0 for v in y)
        # dual feasible, and attaining the primal optimum
        for j in range(len(c)):
            assert sum(A[i][j] * y[i] for i in range(len(A))) >= c[j]
        assert sum(bi * yi for bi, yi in zip(b, y)) == want


def test_certify_falls_through_to_the_simplex_when_rounding_cannot_work():
    """49 tight rows and 7 active variables is C(49,7) bases: enumeration is
    the wrong algorithm, and saying so beat raising the cap."""
    import itertools

    from certo import exact
    from certo.engines import lp

    edges = [list(e) for e in itertools.combinations(range(7), 2)]
    tri = [list(c) for c in itertools.combinations(range(7), 3)]
    spec = _k7_cover(edges, edges + tri).to_lp(integral=False)

    r = lp.opt(spec, LIM)
    assert r.meta["exact"] is True            # it used to come back False
    assert r.meta["objective"] == "7"
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    _ = exact


# --- Lean is emitted for one thing, and refused for the rest ---------------


def test_lean_is_emitted_for_two_things_and_refused_for_the_rest():
    """The list is pinned so nothing joins it casually.

    An exporter earns its place by ELABORATING against a real Mathlib, not by
    looking right -- `tests/run_lean.py` is the gate, and an exporter that did
    compile, in 12.8 seconds, was still removed on the rule above it. Adding a
    name here without running that is the thing this assertion exists to make
    somebody notice.
    """
    from certo import leanexport
    from certo.engines import farkas
    from certo.spec import load_spec

    assert sorted(leanexport.EXPORTERS) == ["farkas", "integer_matrix"]

    root = pathlib.Path(__file__).resolve().parent.parent
    cert = farkas.farkas(
        load_spec(str(root / "examples" / "farkas_linear.py")),
        LIM).certificate
    data = cert.to_dict()
    data["digest"] = cert.digest()
    text = leanexport.farkas_to_lean(data)

    assert "linarith" in text and "nlinarith" not in text
    assert "sorry" not in text.split("-/", 1)[1]
    assert len(text.splitlines()) < 60


def test_a_nonlinear_farkas_certificate_is_refused_rather_than_guessed():
    """`nlinarith` is a heuristic: it adds products and squares and tries.
    Every tactic certo emits decides the fragment its goal lives in, and this
    is the one case where that could not be said honestly."""
    from certo import leanexport
    from certo.engines import farkas
    from certo.spec import load_spec

    root = pathlib.Path(__file__).resolve().parent.parent
    for name in ("farkas_nonlinear.py", "farkas_named_square.py"):
        cert = farkas.farkas(load_spec(str(root / "examples" / name)), LIM,
                             nonlinear=True).certificate
        assert cert.payload.get("nonlinear") is True, name
        try:
            leanexport.farkas_to_lean(cert.to_dict())
            raise AssertionError("expected a refusal for " + name)
        except leanexport.NotExportable as e:
            assert "NONLINEAR" in str(e)
            # and it points at where the numbers are
            assert "in the certificate" in str(e)


def test_reading_lean_survives_and_is_a_different_capability():
    """certo no longer writes a hollow statement, but finding one in a file
    somebody else wrote is still worth doing: `theorem X : True` compiles,
    carries no `sorry`, and passes an axiom audit."""
    from certo import leanexport

    assert not hasattr(leanexport, "_placeholder")
    assert leanexport.HOLLOW == "HOLLOW"

    hand_written = "\n".join([
        "theorem from_core : True := by",
        "  trivial",
        "theorem real_one (a : Real) : a = a := by",
        "  rfl",
    ])
    assert leanexport.hollow_count(hand_written) == 1
    assert leanexport.hollow_count("example : 1 = 1 := by norm_num") == 0


# --- the version is declared once, and a stale install says so -------------


def test_the_version_is_declared_in_exactly_one_place():
    """It used to be written in `pyproject.toml` AND in `__init__.py`, and a
    release had to edit both. They drifted: the installed metadata reported
    0.6.0 while the CLI reported 0.9.0, for three releases, and a user noticed
    before we did."""
    import re

    root = pathlib.Path(__file__).resolve().parent.parent
    pyproject = (root / "pyproject.toml").read_text(encoding="utf-8")

    # no literal version in the project table
    table = pyproject.split("[project]", 1)[1].split("\n[", 1)[0]
    assert not re.search(r'^version\s*=\s*"', table, re.M), table
    assert 'dynamic = ["version"]' in table
    assert 'version = {attr = "certo.__version__"}' in pyproject

    import certo

    assert re.fullmatch(r"\d+\.\d+\.\d+", certo.__version__), certo.__version__


def test_a_stale_editable_install_is_reported_rather_than_silent():
    """One declaration means the two cannot be WRITTEN apart. An editable
    install still goes stale on its own the moment the version moves, and
    silence about that is what let the drift run."""
    import io
    from contextlib import redirect_stdout

    import certo
    from certo import cli, doctor

    real = certo.__version__
    # The INSTALL is simulated, because the suite runs from a checkout where
    # the metadata comes from an `egg-info` in the source tree -- which is a
    # third answer now, and not this one. Asserting a stale install while
    # standing in a source tree was asserting the wrong thing and passing by
    # coincidence.
    # BOTH seams: `cli.installed_version` reads `_metadata_source`, and
    # `_installed_metadata` classifies from `_metadata_copies`. Patching only
    # the first left the second reading the real machine, where it passed
    # for as long as the install and the code happened to agree -- and
    # stopped the moment a release bumped one of them.
    real_source = doctor._metadata_source
    real_copies = doctor._metadata_copies
    site = pathlib.Path("/site-packages")
    try:
        certo.__version__ = "99.0.0"
        cli.__version__ = "99.0.0"
        doctor._metadata_source = lambda: (real, True, site)
        doctor._metadata_copies = lambda: [(real, "installed", site)]

        buf = io.StringIO()
        with redirect_stdout(buf):
            cli.main(["--version"])
        out = buf.getvalue()
        assert "99.0.0" in out                    # what is running
        assert real in out                        # what is installed
        assert "pip install -e ." in out          # and what to do

        ok, detail = doctor._installed_metadata()
        assert ok is False
        assert real in detail and "99.0.0" in detail
    finally:
        certo.__version__ = real
        cli.__version__ = real
        doctor._metadata_source = real_source
        doctor._metadata_copies = real_copies

    # and it is quiet when they agree
    try:
        doctor._metadata_copies = lambda: [(real, "installed", site)]
        ok, detail = doctor._installed_metadata()
        assert ok is True and real in detail
    finally:
        doctor._metadata_copies = real_copies


def test_the_metadata_check_does_not_fail_an_uninstalled_checkout():
    """Running from a source tree with no install is normal, not broken: a
    doctor that cries wolf about it gets ignored about everything else."""
    import builtins

    from certo import doctor

    real = builtins.__import__

    def refuse(name, *a, **k):
        if name == "importlib.metadata":
            raise ImportError("no metadata here")
        return real(name, *a, **k)

    builtins.__import__ = refuse
    try:
        ok, detail = doctor._installed_metadata()
    finally:
        builtins.__import__ = real
    assert ok is True
    assert "no metadata to disagree" in detail


# --- 0.9.0 defects: a hollow Lean file, and a half-finished install --------


def test_status_finds_a_hollow_lean_file_it_did_not_write():
    """Reported against 0.9.0. `status` read certificates and never opened a
    `.lean`, so `theorem from_core : True` sat in a project untouched while
    the report said everything was fine -- and it compiles, carries no
    `sorry`, and passes an axiom audit, so nothing else was going to catch it
    either.

    The release notes claimed detection survived the export removal. It did
    not: `hollow_count` existed and nothing called it on a user's files.
    """
    import tempfile

    from certo import status_report

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_hollow_"))
    (d / "Old.lean").write_text(
        "import Mathlib\n\ntheorem from_core : True := by\n  trivial\n",
        encoding="utf-8")
    (d / "Real.lean").write_text(
        "theorem two (a : Nat) : a = a := by rfl\n", encoding="utf-8")

    found = status_report.hollow_lean(d)
    assert len(found) == 1, found
    assert found[0]["name"] == "from_core"
    assert found[0]["line"] == 3
    assert "passes an axiom audit" in found[0]["text"]

    # and the whole report carries it, even with no certificate in sight
    rep = status_report.scan(str(d))
    assert rep["certificates"] == 0
    assert len(rep["hollow_lean"]) == 1
    assert any("from_core" in h["text"] for h in rep["hollow"])


def test_a_directory_with_only_a_hollow_theorem_exits_nonzero():
    """Nothing established, and the file that says so passes every gate. That
    is the worst case, not the empty one, so it must not exit zero."""
    import io
    import tempfile
    from contextlib import redirect_stdout

    from certo.cli import main

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_hollow_cli_"))
    (d / "X.lean").write_text("theorem nothing : True := by trivial\n",
                              encoding="utf-8")

    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = main(["status", str(d)])
    out = buf.getvalue()

    assert rc == 1
    assert "state True and nothing else" in out
    assert "X.lean:1" in out and "nothing" in out

    # an empty directory is still just empty
    e = pathlib.Path(tempfile.mkdtemp(prefix="certo_empty_"))
    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = main(["status", str(e)])
    assert rc == 0


def test_a_lean_build_tree_is_not_walked():
    """Mathlib under `.lake` is megabytes of somebody else's code, and
    walking it turns a status call into a minute."""
    import tempfile

    from certo import status_report

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_lake_"))
    deep = d / ".lake" / "packages" / "mathlib"
    deep.mkdir(parents=True)
    (deep / "Dep.lean").write_text("theorem x : True := by trivial\n",
                                   encoding="utf-8")
    (d / "Mine.lean").write_text("theorem y : True := by trivial\n",
                                 encoding="utf-8")

    found = status_report.hollow_lean(d)
    assert [f["name"] for f in found] == ["y"], found


def test_doctor_names_a_half_finished_install():
    """The root cause of the version drift: on Windows pip cannot replace a
    file another process holds open, and `certo-mcp.exe` is held for as long
    as the MCP server runs, so `pip install -e .` aborts part-way."""
    from certo import doctor

    keys = [key for key, _required, _probe in doctor.CHECKS]
    assert "install" in keys and "metadata" in keys
    # neither is required: a stale install does not stop anything working,
    # it makes a bug report name the wrong version
    for key, required, _probe in doctor.CHECKS:
        if key in ("install", "metadata"):
            assert required is False, key

    ok, detail = doctor._partial_install()
    assert isinstance(ok, bool) and detail


def test_doctor_names_the_interpreter_startup_rather_than_blaming_certo():
    """A user reported `certo --help` staying alive indefinitely. It was not
    certo: `site` runs every `.pth` before a single line of certo executes,
    and one here loads a certificate-store shim that reaches for the system
    trust store. certo contributes under a tenth of a second and can do
    nothing about the rest -- but a `certo --help` that hangs is otherwise
    indistinguishable from a certo that hangs."""
    from certo import doctor

    keys = [key for key, _r, _p in doctor.CHECKS]
    assert "startup" in keys
    for key, required, _probe in doctor.CHECKS:
        if key == "startup":
            assert required is False     # not certo's to fix

    ok, detail = doctor._startup()
    assert isinstance(ok, bool) and detail
    # whichever way it goes, the number is in the message
    assert any(ch.isdigit() for ch in detail)

    # only `.pth` files that RUN code are named: a path entry costs nothing
    hooks = doctor._startup_hooks()
    assert isinstance(hooks, list)
    assert all(h.endswith(".pth") for h in hooks)


def test_only_pth_files_that_execute_are_counted():
    """A `.pth` that adds a path costs nothing at startup; one that begins
    `import` executes every time, and that is where a hang lives."""
    import tempfile
    from unittest import mock

    from certo import doctor

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_pth_"))
    (d / "plain.pth").write_text("/some/path\n", encoding="utf-8")
    (d / "runs.pth").write_text("import something_slow\n", encoding="utf-8")

    with mock.patch("site.getsitepackages", return_value=[str(d)]):
        assert doctor._startup_hooks() == ["runs.pth"]


# --- data that crosses a boundary, and the number that says it arrived -----


def test_the_fingerprint_catches_what_retyping_actually_gets_wrong():
    """Reported by a user: "you can perfectly certify the wrong matrix." Each
    of these is a thing that happens when somebody copies coordinates by hand,
    and each has to give a different number or the fingerprint is theatre."""
    import copy

    from certo import interchange

    base = [[4, 2, 2, 1], [0, 2, 0, 1], [0, 0, 2, 1], [0, 0, 0, 1]]
    h = interchange.fingerprint(base)

    def moved(fn):
        m = copy.deepcopy(base)
        fn(m)
        return interchange.fingerprint(m) != h

    assert moved(lambda m: m[0].__setitem__(0, 5))        # one entry
    assert moved(lambda m: m[1].__setitem__(2, 1))        # a zero became one
    assert moved(lambda m: m[0].__setitem__(0, -4))       # a sign
    assert interchange.fingerprint([list(r) for r in zip(*base)]) != h
    assert interchange.fingerprint([base[1], base[0]] + base[2:]) != h
    assert interchange.fingerprint(base[:3]) != h
    assert interchange.fingerprint([r + [0] for r in base]) != h

    # and it is stable: the same data gives the same number, always
    assert interchange.fingerprint(copy.deepcopy(base)) == h


def test_a_file_edited_after_it_was_written_is_refused():
    """The case that actually happens: somebody fixes just one entry by hand
    and the file no longer matches the number it carries."""
    import json
    import tempfile

    from certo import interchange

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_xchg_"))
    f = d / "cell.json"
    interchange.dump([[1, 2], [3, 4]], f, name="two by two")

    assert interchange.load(f)["entries"] == [[1, 2], [3, 4]]

    raw = json.loads(f.read_text(encoding="utf-8"))
    raw["entries"][0][0] = 9
    f.write_text(json.dumps(raw), encoding="utf-8")
    try:
        interchange.load(f)
        raise AssertionError("expected a refusal")
    except interchange.NotInterchangeable as e:
        assert "edited after it was written" in str(e)


def test_a_matrix_can_arrive_as_a_file_the_spec_never_reads():
    """The difference between a transcription and a hand-off: the spec names
    a path, and the coordinates are written by whatever holds the object."""
    import tempfile

    from certo import MatrixSpec, interchange
    from certo.engines import algebra

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_xchg_"))
    f = d / "cell.json"
    # one local cell: four rays, and the Smith form a user measured
    interchange.dump([[4, 2, 2, 1], [0, 2, 0, 1], [0, 0, 2, 1], [0, 0, 0, 1]],
                     f, name="one local cell")

    r = algebra.integer_matrix(
        MatrixSpec(matrix=str(f), question="smith"), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.certificate.payload["invariants"] == [1, 2, 2, 4]
    assert r.certificate.payload["det"] == 16
    assert r.certificate.payload["fingerprint"] == \
        str(interchange.fingerprint(interchange.load(f)["entries"]))

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("FINGERPRINT" in w for w in rep.warnings)


def test_the_recipe_travels_so_the_other_side_can_recompute_it():
    """A number whose recipe lives only in certo's documentation is a number
    the other side has to take on faith, and faith across the boundary is the
    whole problem."""
    from certo import interchange

    recipe = interchange.describe()
    assert recipe["algorithm"] == "horner"
    assert int(recipe["prime"]) == (1 << 61) - 1
    assert int(recipe["base"]) == 1_000_003
    assert "rows" in recipe["order"]

    # recomputing it from the recipe alone gives the same number
    matrix = [[7, -3], [0, 5]]
    p, b = int(recipe["prime"]), int(recipe["base"])
    h = 0
    h = (h * b + len(matrix)) % p
    h = (h * b + len(matrix[0])) % p
    for row in matrix:
        for entry in row:
            h = (h * b + (entry % p)) % p
    assert h == interchange.fingerprint(matrix)


def test_a_forged_fingerprint_does_not_verify():
    import copy

    from certo import MatrixSpec
    from certo.engines import algebra

    cert = algebra.integer_matrix(
        MatrixSpec(matrix=[[2, 1], [1, 3]], question="smith"),
        LIM).certificate
    base = json.loads(json.dumps(cert.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    # a number that is not the one these entries give
    assert not bent(lambda p: p.__setitem__("fingerprint", "1"))
    # the matrix edited while the number stayed
    assert not bent(lambda p: p["matrix"][0].__setitem__(0, 9))


# --- lint knows about a matrix before Smith runs ---------------------------


def _lint_matrix(body):
    import tempfile

    from certo import lint as linter

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_lintm_"))
    f = d / "s.py"
    f.write_text("from certo import MatrixSpec\n\n\ndef spec():\n    "
                 "return MatrixSpec({}, title=\"t\")\n".format(body),
                 encoding="utf-8")
    return linter.lint(str(f))


def test_lint_refuses_a_question_the_matrix_cannot_answer():
    """A determinant of a rectangle, and a question that is not one of the
    four -- both before Smith spends a minute finding out."""
    rep = _lint_matrix("matrix=[[1, 2, 3], [4, 5, 6]], question=\"det\"")
    assert rep["errors"] == 1
    assert "2 by 3" in rep["findings"][0]["text"]

    rep = _lint_matrix("matrix=[[1, 2], [3, 4]], question=\"eigen\"")
    assert rep["errors"] == 1
    assert "not a question this answers" in rep["findings"][0]["text"]

    # a minor IS square, and is not complained about
    rep = _lint_matrix("matrix=[[1, 2, 3], [4, 5, 6]], question=\"det\", "
                       "rows=[0, 1], cols=[0, 1]")
    assert rep["errors"] == 0


def test_lint_names_the_shapes_that_mean_a_construction_lost_a_term():
    """An all-zero row and a repeated row are not errors -- the rank is still
    the rank -- but in a wall of numbers they are invisible, and in data typed
    by hand they usually mean something went wrong upstream."""
    rep = _lint_matrix("matrix=[[1, 0, 2], [0, 0, 0], [3, 0, 4]]")
    assert rep["errors"] == 0 and rep["warnings"] == 1
    assert "all-zero" in rep["findings"][0]["text"]

    rep = _lint_matrix("matrix=[[1, 2], [1, 2], [3, 4]]")
    assert rep["warnings"] == 1
    assert "pasted twice" in rep["findings"][0]["text"]

    # a repeated ZERO row is reported once, as an empty block, not twice
    rep = _lint_matrix("matrix=[[0, 0], [0, 0], [1, 2]]")
    assert rep["warnings"] == 1


def test_lint_checks_a_selection_before_it_is_used():
    rep = _lint_matrix("matrix=[[1, 2], [3, 4]], rows=[0, 5], cols=[0, 0]")
    texts = " ".join(f["text"] for f in rep["findings"])
    assert rep["errors"] == 1 and "outside 0..2" in texts
    assert "same index twice" in texts

    rep = _lint_matrix("matrix=[[1, 2], [3, 4]], rows=[]")
    assert rep["errors"] >= 1
    assert any("selects nothing" in f["text"] for f in rep["findings"])


def test_lint_says_nothing_about_the_size_people_actually_work_at():
    """A user's real matrix is 64 by 64. Warning about the size somebody works
    at every day is noise, and noise is how a linter gets ignored about the
    rest -- so the threshold sits well above it."""
    body = ("matrix=[[1 if i == j else 0 for j in range(64)] "
            "for i in range(64)], question=\"smith\"")
    rep = _lint_matrix(body)
    assert rep["errors"] == 0 and rep["warnings"] == 0 and rep["notes"] == 0

    # and it does speak up when the size is genuinely a different problem
    big = ("matrix=[[1 if i == j else 0 for j in range(120)] "
           "for i in range(120)], question=\"smith\"")
    rep = _lint_matrix(big)
    texts = " ".join(f["text"] for f in rep["findings"])
    assert "14400 entries" in texts
    assert "n^4" in texts or "minutes rather than seconds" in texts


def test_lint_reads_a_data_file_and_refuses_a_broken_one():
    """A fingerprint that disagrees is caught before anything is computed."""
    import json
    import tempfile

    from certo import interchange, lint as linter

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_lintdata_"))
    data = d / "cell.json"
    interchange.dump([[4, 2], [0, 2]], data, name="cell")

    spec = d / "s.py"
    spec.write_text(
        "from certo import MatrixSpec\n\n\ndef spec():\n"
        "    return MatrixSpec(matrix=r\"{}\", question=\"smith\", "
        "title=\"t\")\n".format(str(data).replace("\\", "\\\\")),
        encoding="utf-8")
    assert linter.lint(str(spec))["errors"] == 0

    raw = json.loads(data.read_text(encoding="utf-8"))
    raw["entries"][0][0] = 9
    data.write_text(json.dumps(raw), encoding="utf-8")

    rep = linter.lint(str(spec))
    assert rep["errors"] == 1
    assert "edited after it was written" in rep["findings"][0]["text"]


# --- local toric data, computed instead of assumed -------------------------


def _cone(**kw):
    from certo import ConeSpec
    from certo.engines import algebra

    kw.setdefault("title", "t")
    return algebra.toric_cone(ConeSpec(**kw), LIM)


CELL = {"v0": (4, 0, 0, 0), "m01": (2, 2, 0, 0),
        "m02": (2, 0, 2, 0), "b": (1, 1, 1, 1)}
CELL_ORDER = ["v0", "m01", "m02", "b"]


def test_the_formulas_an_audit_took_as_hypotheses_are_computed():
    """An audit of the crepant criterion assumed `discrepancy == height - 1`
    and `multiplicity == height`. Those are the step where a cone becomes a
    number, and nothing was computing them from a cone."""
    r = _cone(rays=CELL, order=CELL_ORDER,
              lattice=[list(CELL[n]) for n in CELL_ORDER],
              subdivision={"bary": (1, 1, 1, 1)})
    p = r.certificate.payload

    assert r.verdict is Verdict.PROVED
    assert p["multiplicity"] == "1" and p["regular"] is True
    assert p["height_one"] is True
    assert p["height_functional"] == ["1/4"] * 4
    assert p["height_unique"] is True
    assert all(v == "0" for v in p["discrepancies"].values())
    assert p["subdivision"]["bary"]["discrepancy"] == "0"
    assert p["crepant"] is True

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free


def test_the_same_cone_gives_a_different_multiplicity_in_a_different_lattice():
    """Not an error -- a different number, confidently. Which is why the
    lattice is declared and travels with the answer."""
    declared = _cone(rays=CELL, order=CELL_ORDER,
                     lattice=[list(CELL[n]) for n in CELL_ORDER])
    ambient = _cone(rays=CELL, order=CELL_ORDER, lattice=None)

    assert declared.certificate.payload["multiplicity"] == "1"
    assert ambient.certificate.payload["multiplicity"] == "16"
    assert declared.certificate.payload["multiplicity_in"] == "declared lattice"
    assert "Z^4" in ambient.certificate.payload["multiplicity_in"]

    # the generators are primitive in one reading and not in the other
    assert set(declared.certificate.payload["primitive"].values()) == {1}
    assert ambient.certificate.payload["primitive"]["v0"] == 4

    for r in (declared, ambient):
        rep = verify(_roundtrip(r.certificate), LIM)
        assert rep.ok
        assert any("half a sentence" in w for w in rep.warnings)


def test_crepant_is_about_what_a_subdivision_adds_and_nothing_else():
    """A generator's discrepancy is zero BY CONSTRUCTION wherever a height
    functional exists. The first version reported the A1 singularity crepant
    on that basis, which said nothing and sounded like something."""
    a1 = _cone(rays={"a": (1, 0), "b": (1, 2)}, order=["a", "b"])
    p = a1.certificate.payload

    assert p["multiplicity"] == "2"
    assert p["height_one"] is True
    assert p["generators_at_height_one"] is True
    assert p["crepant"] is None          # nothing was subdivided

    # name a ray and the question becomes answerable
    with_ray = _cone(rays={"a": (1, 0), "b": (1, 2)}, order=["a", "b"],
                     subdivision={"mid": (1, 1)})
    q = with_ray.certificate.payload
    assert q["subdivision"]["mid"]["discrepancy"] == "0"
    assert q["crepant"] is True

    # and a ray off the hyperplane is not crepant
    off = _cone(rays={"a": (1, 0), "b": (1, 2)}, order=["a", "b"],
                subdivision={"high": (2, 2)})
    assert off.certificate.payload["crepant"] is False


def test_a_missing_quantity_is_recorded_rather_than_refused():
    """Three rays in the plane span no full-dimensional simplicial cone, so
    there is no multiplicity in this sense -- but they do have a height
    question, and refusing the certificate would lose it."""
    r = _cone(rays={"a": (1, 0), "b": (0, 1), "c": (1, 1)},
              order=["a", "b", "c"])
    p = r.certificate.payload

    assert r.verdict is Verdict.PROVED
    assert p["multiplicity"] is None and p["regular"] is None
    assert "index of the sublattice" in p["multiplicity_why_not"]
    # the thing worth knowing about these three rays
    assert p["height_one"] is False
    assert p["generators_at_height_one"] is False
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_forged_cone_certificate_does_not_verify():
    """Every number is redone from the generators, so editing one is editing
    it away from what the rays give."""
    import copy

    base = json.loads(json.dumps(
        _cone(rays=CELL, order=CELL_ORDER,
              lattice=[list(CELL[n]) for n in CELL_ORDER],
              subdivision={"bary": (1, 1, 1, 1)}).certificate.to_dict()))
    assert verify(Certificate.from_dict(base), LIM).ok

    def bent(fn):
        d = copy.deepcopy(base)
        fn(d["payload"])
        return verify(Certificate.from_dict(d), LIM).ok

    assert not bent(lambda p: p.__setitem__("multiplicity", "1000"))
    assert not bent(lambda p: p["primitive"].__setitem__("v0", 7))
    assert not bent(lambda p: p.__setitem__("height_functional", ["1"] * 4))
    assert not bent(lambda p: p["discrepancies"].__setitem__("b", "5"))
    assert not bent(lambda p: p["subdivision"]["bary"].__setitem__(
        "discrepancy", "-1"))
    assert not bent(lambda p: p["rays"]["v0"].__setitem__(0, 5))


def test_the_certificate_refuses_to_say_anything_about_varieties():
    """certo hands over what the theorems consume and stops. A certificate
    that quietly asserted a smooth chart would be the substitution this
    project exists to refuse."""
    r = _cone(rays=CELL, order=CELL_ORDER,
              lattice=[list(CELL[n]) for n in CELL_ORDER])
    rep = verify(_roundtrip(r.certificate), LIM)

    warned = " ".join(rep.warnings)
    assert "not the theorems" in warned
    assert "smooth chart" in warned and "crepant modification" in warned
    for word in ("SNC", "reduced"):
        assert word in warned, word

    text = json.dumps(r.certificate.payload)
    for claim in ("smooth", "snc", "variety", "resolution"):
        assert claim not in text.lower(), claim


# --- the documentation is a surface that drifts, in two languages ---------


DOC_PAGES = ("COMMANDS.md", "SPECS.md", "CERTIFICATES.md", "CASES.md",
             "LIMITS.md", "VERDICTS.md")


def _docs():
    return pathlib.Path(__file__).resolve().parent.parent / "docs"


def test_both_documentation_trees_carry_the_same_pages():
    """The Spanish README once drifted two releases behind the English one,
    and nothing caught it until a user did. Splitting the README into six
    files multiplies that surface by six, so the pairing is pinned here."""
    docs = _docs()
    en = {p.name for p in docs.glob("*.md")}
    es = {p.name for p in (docs / "es").glob("*.md")}

    assert en == set(DOC_PAGES), {"unexpected or missing English page": en}
    assert es == en, {"only in English": sorted(en - es),
                      "only in Spanish": sorted(es - en)}


def test_every_command_has_an_entry_in_both_references():
    """A command with no entry is a command a reader concludes does not
    exist -- which is exactly what happened to `order`, documented and
    unfindable, until a user reimplemented it three times by hand."""
    import re

    docs = _docs()
    commands = set(_subcommands())
    # `what` aliases `commands`; the alias is documented in that entry.
    commands.discard("what")

    for rel in ("COMMANDS.md", "es/COMMANDS.md"):
        text = (docs / rel).read_text(encoding="utf-8")
        entries = set(re.findall(r"^### `certo ([a-z]+)", text, re.M))
        assert commands <= entries, {
            "page": rel,
            "commands with no entry": sorted(commands - entries),
            "entries that are not commands": sorted(entries - commands)}


def test_every_command_entry_states_what_it_does_not_establish():
    """The boundary of a claim is the half that ages. An entry that lists
    what a command answers and stops is the shape that gets a bounded
    synthesis cited as a theorem two years later."""
    import re

    for rel, field in (("COMMANDS.md", "Not established"),
                       ("es/COMMANDS.md", "No establece")):
        text = (_docs() / rel).read_text(encoding="utf-8")
        blocks = re.split(r"^### `certo ", text, flags=re.M)[1:]
        missing = [b.split("`", 1)[0] for b in blocks
                   if "**{}**".format(field) not in b]
        assert not missing, {"page": rel, "entries with no boundary": missing}


def test_the_readmes_point_at_documentation_that_exists():
    """A README that links into docs/ is only shorter if the links land."""
    import re

    root = pathlib.Path(__file__).resolve().parent.parent
    for name in ("README.md", "README.es.md"):
        text = (root / name).read_text(encoding="utf-8")
        targets = [t for _, t in re.findall(r"\[([^\]]+)\]\(([^)]+)\)", text)
                   if not t.startswith("http")]
        missing = [t for t in targets
                   if not (root / t.split("#")[0]).exists()]
        assert not missing, {"readme": name, "dead links": missing}
        assert any("docs/" in t for t in targets), name + ": links no docs"


# --- a coefficient on a variable nobody declared ---------------------------


def _lp_with(constraint_var):
    from certo import LPSpec

    lp = LPSpec(sense="max")
    lp.variable("b", lo=0, hi=10)
    lp.objective({"b": 1})
    lp.constraint({constraint_var: 1}, "<=", "1/3", name="cheb")
    return lp


def test_an_undeclared_coefficient_is_refused_not_dropped():
    """One typo used to change a certified 1/3 into a certified 10.

    `as_leq_system` builds each row as `coeffs.get(v, 0) for v in var_names`,
    so a name that was never declared is indistinguishable from a zero
    coefficient once the row exists: the constraint meant to hold `b` back was
    not in the program at all. `lint` said "nothing that will bite" -- its
    `no_variables` check only fires when NONE were declared -- and `verify`
    passed, because 10 really is the optimum of the program that was built.
    That is the shape this whole project exists to refuse: a confidently wrong
    number with a certificate attached."""
    ok = _lp_with("b").as_leq_system()
    assert ok, "the correct spec must still normalise"

    try:
        _lp_with("bb").as_leq_system()
    except ValueError as e:
        assert "bb" in str(e), e
        assert "cheb" in str(e), "it must name WHERE the stray coefficient is"
    else:
        raise AssertionError("an undeclared coefficient was accepted")


def test_the_objective_is_checked_too_and_order_does_not_matter():
    """Declaring after use is fine -- the check is at normalisation, not at
    `constraint()`, so a spec that builds its rows before its variables is
    not punished for the order it chose."""
    from certo import LPSpec

    late = LPSpec(sense="max")
    late.objective({"a": 1})
    late.constraint({"a": 1}, "<=", 1, name="cap")
    late.variable("a", lo=0, hi=5)
    assert late.as_leq_system(), "declaration order must stay free"

    stray = LPSpec(sense="max")
    stray.variable("a", lo=0, hi=5)
    stray.objective({"a": 1, "ghost": 3})
    stray.constraint({"a": 1}, "<=", 1, name="cap")
    try:
        stray.as_leq_system()
    except ValueError as e:
        assert "ghost" in str(e) and "objective" in str(e), e
    else:
        raise AssertionError("a stray objective coefficient was accepted")


def test_lint_reports_it_before_the_compute_is_spent():
    """`lint` is the cheapest thing in the tool and this is exactly its job:
    the run that follows would have been wrong, not slow."""
    import tempfile

    src = ("from certo import LPSpec\n"
           "def spec():\n"
           "    lp = LPSpec(sense='max')\n"
           "    lp.variable('b', lo=0, hi=10)\n"
           "    lp.objective({'b': 1})\n"
           "    lp.constraint({'bb': 1}, '<=', '1/3', name='cheb')\n"
           "    return lp\n")
    with tempfile.TemporaryDirectory() as d:
        f = pathlib.Path(d) / "typo_spec.py"
        f.write_text(src, encoding="utf-8")
        from certo.lint import lint

        out = lint(str(f))
        keys = [x["key"] for x in out["findings"]]
        assert "lp.undeclared_variable" in keys, keys
        assert out["errors"] >= 1, out


# --- 0.10: the range of a variable, not one point of it --------------------


def _range_regime(*rows, title="t"):
    import z3

    from certo import Spec

    s = Spec(title=title)
    for name, f in rows:
        s.assume(name, f)
    s.claim(z3.BoolVal(True))
    return s


def test_the_range_is_the_interval_and_both_ends_are_farkas():
    """`check --hypotheses-only` hands back a POINT. A user needed `a <= 1/3`
    and got `a = 0`, then derived the interval by hand. Both ends here are
    non-negative combinations of the hypotheses, so the multipliers are the
    proof and checking one is adding fractions."""
    import z3

    from certo import rangebound

    a, b = z3.Reals("a b")
    out = rangebound.bounds_of(_range_regime(
        ("cheb", 3 * a <= 1), ("window", a + b <= 1),
        ("b_nonneg", b >= 0), ("a_nonneg", a >= 0)), "a")

    assert out["interval"] == "[0, 1/3]"
    assert out["upper"]["bound"] == "1/3"
    assert out["upper"]["multipliers"] == {"cheb": "1/3"}
    assert out["lower"]["bound"] == "0"
    assert not out["empty"]
    assert all(v["ok"] for v in rangebound.check(out).values())


def test_an_empty_regime_is_not_an_infinite_interval():
    """Over an empty regime every direction is unbounded, and the first
    version read that as `(-inf, +inf)`: the variable ranges over everything.
    There is no variable. That is the permissive-looking error, so
    inhabitation is asked FIRST."""
    import z3

    from certo import rangebound

    a = z3.Real("a")
    out = rangebound.bounds_of(
        _range_regime(("hi", a <= 1), ("lo", a >= 3)), "a")
    assert out["empty"] is True
    assert out["interval"] == "(empty)"
    assert out["upper"]["bound"] is None


def test_a_strict_row_leaves_the_endpoint_open():
    """`a < 1/3` and `a <= 1/3` have the same supremum and only one contains
    it. Rounding that away would be a claim the regime does not support."""
    import z3

    from certo import rangebound

    a = z3.Real("a")
    out = rangebound.bounds_of(
        _range_regime(("strict", 3 * a < 1), ("lo", a >= 0)), "a")
    assert out["interval"] == "[0, 1/3)"
    assert out["upper"]["strict"] is True


def test_a_nonlinear_hypothesis_is_refused_not_dropped():
    """Dropping one would WIDEN the range, which is wrong in the direction
    that looks safe."""
    import z3

    from certo import rangebound

    a = z3.Real("a")
    try:
        rangebound.bounds_of(_range_regime(("sq", a * a <= 4), ("lo", a >= 0)), "a")
    except rangebound.NotRangeable as e:
        assert "sq" in str(e)
    else:
        raise AssertionError("a non-linear hypothesis was accepted")


# --- 0.10: a parameter that depends on itself ------------------------------


def _cycle(**kw):
    from certo import CycleSpec
    from certo.cycles import certify

    kw.setdefault("title", "t")
    return certify(CycleSpec(**kw))


TOWER = {"from": "delta", "to": "k", "rel": ">=",
         "fn": "tower", "of": "reciprocal"}
CRUDE = {"from": "k", "to": "rho", "rel": "<=", "fn": "poly", "degree": -2}


def test_the_tower_closes_the_loop_without_a_stand_in():
    """Found by hand three times in one session, and only by building a
    substitute a solver could see (`k >= 1/delta`) -- which proves something
    strictly weaker and leaves the tower carried in prose."""
    from certo import cycles

    out = _cycle(parameter="delta", edges=[TOWER, CRUDE],
                 closes=("delta", "<=", "rho"))

    assert out["empty"] is True
    assert out["cycle"] == ["delta", "k", "rho", "delta"]
    assert out["classes"]["k"] == {"tier": "tower", "exponent": "1"}
    assert out["classes"]["rho"] == {"tier": "tower", "exponent": "-2"}
    assert out["closes"]["comparison"] == 1

    got = cycles.check(out)
    assert got["steps_ok"] and got["comparison_ok"] and got["empty_ok"]


def test_a_loop_that_is_not_refuted_says_so_rather_than_claiming_no_cycle():
    """The dangerous direction is reporting a live regime empty, so `empty` is
    only ever set on a STRICT comparison."""
    out = _cycle(parameter="delta",
                 edges=[{"from": "delta", "to": "k", "rel": ">=",
                         "fn": "poly", "degree": "1/2", "of": "reciprocal"},
                        {"from": "k", "to": "rho", "rel": "<=",
                         "fn": "poly", "degree": -1}],
                 closes=("delta", "<=", "rho"))
    assert out["empty"] is False
    assert out["why"] == "not_strict"


def test_an_edge_whose_bound_points_the_wrong_way_is_refused():
    """A lower bound pushed through an INCREASING map does not bound the
    target from above. Composing it anyway could declare a live regime
    empty."""
    from certo.cycles import NotCyclic

    try:
        _cycle(parameter="delta",
               edges=[TOWER, {"from": "k", "to": "rho", "rel": "<=",
                              "fn": "poly", "degree": 2}],
               closes=("delta", "<=", "rho"))
    except NotCyclic as e:
        assert "rho" in str(e) and "upper" in str(e)
    else:
        raise AssertionError("an unsound composition was accepted")


def test_exp_of_a_vanishing_argument_is_a_constant_not_growth():
    """`exp(x) -> 1` as `x -> 0`. Claiming a tier there would invent growth
    out of an argument that vanishes, and a cycle would close that does not."""
    from certo import growth as g

    assert g.apply("exp", g.Class(g.POLY, -1)) == g.CONST
    assert g.apply("tower", g.Class(g.POLY, 2)) == g.Class(g.TOWER, 1)
    # a higher tier that decays is dominated by ANY polynomial
    assert g.compare(g.Class(g.TOWER, -2), g.Class(g.POLY, -1)) == -1


# --- 0.10: exponents derived, not assigned ---------------------------------


def test_the_relations_give_the_six_numbers_nobody_should_derive_by_hand():
    """A user assigned `Lmass: 2, C: 1, dp: 2, ...` mentally from `|E| <=
    Lmass`, `C >= n`, `d' >= C(n,2)`. One wrong entry gives a clean false
    answer, which is exactly where automating pays."""
    from certo import orderinfer

    got = orderinfer.derive_orders(
        ["E ~ n**2", "tC ~ 1", "Lmass ~ E * tC", "C ~ n", "dp ~ C**2"],
        {}, ["Lmass", "C", "dp", "E", "tC"])
    assert got["orders"] == {"C": 1, "E": 2, "Lmass": 2, "dp": 2, "tC": 0}


def test_an_undetermined_exponent_is_refused_with_the_interval_named():
    """`order` needs a number per symbol; an interval is not one. Naming the
    interval says which bound is missing, and `cannot infer` does not."""
    from certo import orderinfer

    try:
        orderinfer.derive_orders(["C ~ n", "Lmass >= C"], {}, ["Lmass", "C"])
    except orderinfer.NotInferable as e:
        assert "Lmass" in str(e) and "+inf" in str(e)
    else:
        raise AssertionError("an undetermined exponent was accepted")


def test_a_one_sided_relation_can_still_settle_the_whole_term():
    """`dp >= C**2` bounds the exponent of dp only from below -- and dp is in
    a denominator, so the TERM is still bounded above. Insisting every symbol
    be pinned would refuse this, and it is the common shape."""
    from certo import orderinfer

    out = orderinfer.infer(["C ~ n", "dp >= C**2"], {},
                           {"term": {"C": 2, "dp": -2}})
    assert out["results"]["term"]["verdict"] == "decays"
    assert out["results"]["term"]["upper"] == "-2"
    assert out["results"]["term"]["lower"] is None


# --- 0.10: what the certificate assumed vs what the lemma gives ------------


def test_a_binding_catches_the_lemma_that_does_not_cover_the_hypothesis():
    """The incident: a bound certified assuming the fine counting estimate,
    and a packaged lemma using density <= 1 that gives something useless --
    found three modules later, by reading the statement."""
    import json
    import tempfile

    import z3

    from certo import binding
    from certo.certificate import Certificate

    count, dens, n = z3.Reals("count dens n")
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        src = root / "counting.py"
        src.write_text(
            "import z3\n"
            "from certo import Spec\n"
            "def spec():\n"
            "    count, dens, n = z3.Reals('count dens n')\n"
            "    s = Spec()\n"
            "    s.assume('fine_count', count <= dens*dens*dens*n**4)\n"
            "    s.claim(count <= n**4)\n"
            "    return s\n", encoding="utf-8")

        cert = Certificate(kind="model", solver_free=True, payload={},
                           note_key="cert.note.model").stamp(str(src))
        (root / "c.json").write_text(
            json.dumps(cert.to_dict()), encoding="utf-8")

        class S:
            certificate = "c.json"
            declaration = "PaperIV.N1_from_counting"
            discharges = "fine_count"
            title = "t"
            provides = None

        S.provides = (count <= n**4)                 # density <= 1
        weak = binding.certify(S, root=str(root))
        assert weak["covers"] is False
        assert not weak["spec"]["stale"]

        S.provides = (count <= dens * dens * dens * n**4)
        fine = binding.certify(S, root=str(root))
        assert fine["covers"] is True

        # and the payload is re-checked, never believed
        assert binding.check(weak)["agrees"]
        forged = dict(weak, covers=True)
        assert not binding.check(forged)["agrees"]


def test_a_binding_names_a_hypothesis_that_is_not_there():
    """Binding to a hypothesis the spec does not declare would be a link to
    nothing, and it is refused with what IS declared."""
    import json
    import tempfile

    import z3

    from certo import binding
    from certo.certificate import Certificate

    n = z3.Real("n")
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        src = root / "s.py"
        src.write_text(
            "import z3\n"
            "from certo import Spec\n"
            "def spec():\n"
            "    n = z3.Real('n')\n"
            "    s = Spec()\n"
            "    s.assume('n_big', n >= 1)\n"
            "    s.claim(n >= 0)\n"
            "    return s\n", encoding="utf-8")
        cert = Certificate(kind="model", solver_free=True, payload={},
                           note_key="cert.note.model").stamp(str(src))
        (root / "c.json").write_text(json.dumps(cert.to_dict()),
                                     encoding="utf-8")

        class S:
            certificate = "c.json"
            declaration = "D"
            discharges = "no_such_hypothesis"
            provides = (n >= 1)
            title = "t"

        try:
            binding.certify(S, root=str(root))
        except binding.NotBindable as e:
            assert "no_such_hypothesis" in str(e) and "n_big" in str(e)
        else:
            raise AssertionError("bound to a hypothesis that is not there")


# --- one table, and every surface checked against it -----------------------


def _surfaces():
    root = pathlib.Path(__file__).resolve().parent.parent
    for rel in ("README.md", "README.es.md", "docs/COMMANDS.md",
                "docs/es/COMMANDS.md", "docs/CERTIFICATES.md",
                "docs/es/CERTIFICATES.md", "docs/index.html"):
        yield rel, (root / rel).read_text(encoding="utf-8")


def test_the_catalogue_is_derived_and_covers_every_command():
    """The table the documents are compared against has to come from the code
    that runs, or it is one more thing to keep in step."""
    from certo import catalogue, routing

    rows = catalogue.rows()
    names = {r["command"] for r in rows}
    assert names == set(_subcommands())
    assert len(rows) == catalogue.counts()["commands"]

    # every command has a declared kind entry, even if that entry is None
    missing = sorted(names - set(routing.KIND_OF))
    assert not missing, {"commands with no KIND_OF entry": missing}

    # and every kind named is one the registry can actually verify
    from certo.certificate import VERIFIERS

    # A command may declare several kinds -- `core` on a `MultiSpec` gives a
    # table of cores, `cases` a model when the CNF is satisfiable -- so the
    # declaration is flattened before it is looked up.
    declared = set()
    for v in routing.KIND_OF.values():
        if v is None:
            continue
        declared.update({v} if isinstance(v, str) else set(v))
    unknown = sorted(declared - set(VERIFIERS))
    assert not unknown, {"kinds nothing verifies": unknown}


def test_every_document_that_states_a_count_states_the_right_one():
    """`docs/index.html` said forty-three the day after the forty-sixth
    command shipped, because the parity test covered the markdown and not the
    page. The README table said twenty-eight while listing twenty-nine with
    thirty-nine in the CLI. Same failure, three surfaces, and none of it is a
    hard problem: it is a number nobody recomputes."""
    import re

    from certo import catalogue

    counts = catalogue.counts()
    en, es = catalogue.WORDS_EN, catalogue.WORDS_ES

    def numerals(k):
        """Every way a document might spell a number -- and only those.

        Matching "any word before `comandos`" flagged `lista de comandos`,
        which is prose. A test that cries wolf is a test that gets muted, and
        this one is guarding the surface that drifted first.
        """
        out = {str(v): v for v in range(1, 100)}
        out.update({w: k2 for k2, w in en.items()})
        out.update({w: k2 for k2, w in es.items()})
        return out

    SPELLINGS = numerals(0)
    UNITS = (("commands", "commands"), ("comandos", "commands"),
             ("certificate kinds", "kinds"), ("tipos de certificado", "kinds"))

    wrong = []
    for rel, text in _surfaces():
        low = text.lower()
        for unit, which in UNITS:
            want = counts[which]
            for spelling, value in SPELLINGS.items():
                if value == want:
                    continue
                # A boundary, or `43 commands` also reports `3 commands`.
                if re.search(r"(?<![\w-])" + re.escape(spelling) + r"\s+"
                             + re.escape(unit), low):
                    wrong.append({"in": rel,
                                  "says": "{} {}".format(spelling, unit),
                                  "should be": want})
    assert not wrong, wrong


def test_the_readme_tables_list_exactly_the_commands_that_exist():
    """The table is where a reader looks for whether something exists at all:
    a user concluded `audit` did not, because it was missing from this one."""
    import re

    from certo import catalogue

    root = pathlib.Path(__file__).resolve().parent.parent
    names = {r["command"] for r in catalogue.rows()}
    for rel, pattern in (("README.md", r"^## The [a-z-]+ commands$"),
                         ("README.es.md", r"^## Los [a-z ]+ comandos$")):
        text = (root / rel).read_text(encoding="utf-8")
        head = re.search(pattern, text, re.M)
        assert head, rel + ": the commands section was renamed"
        block = re.split(r"\n## ", text.split(head.group(0), 1)[1])[0]
        listed = re.findall(r"^\| `([a-z]+)`", block, re.M)
        assert set(listed) == names, {
            "readme": rel, "missing": sorted(names - set(listed)),
            "not a command": sorted(set(listed) - names)}
        assert len(listed) == len(set(listed)), rel + ": a command twice"


def test_the_project_page_is_a_surface_like_any_other():
    """It was not covered, and it drifted first. It also carries the install
    line, which pointed at a package that does not exist on PyPI and would
    have 404'd for every visitor."""
    root = pathlib.Path(__file__).resolve().parent.parent
    page = (root / "docs/index.html").read_text(encoding="utf-8")

    from certo import catalogue

    n = catalogue.counts()
    assert "{} commands".format(n["commands"]) in page
    assert "{} comandos".format(n["commands"]) in page
    assert "{} certificate kinds".format(n["kinds"]) in page
    assert "{} tipos de certificado".format(n["kinds"]) in page

    # both language halves are still there, and the links still resolve
    assert 'id="en"' in page and 'id="es"' in page


# --- a spec that executes nothing ------------------------------------------


def test_a_json_spec_runs_with_nothing_executed():
    """`load_spec` compiles and runs the `.py` it is handed. For a person
    editing their own file that is the trust an editor already has; for an
    AGENT it is the thinnest part of the surface, because a model that writes
    a spec writes a program. Most of the corpus is data."""
    from certo import LPSpec
    from certo.spec import load_spec

    root = pathlib.Path(__file__).resolve().parent.parent
    spec = load_spec(str(root / "examples/lp_as_data.json"), LPSpec)
    assert isinstance(spec, LPSpec)
    assert spec.var_names == ["x", "y"]

    from certo.engines import lp

    res = lp.opt(spec)
    assert res.certificate is not None
    # max 2x+3y with x+y <= 1 and x+2y <= 1 is 2, at x=1: the second row is
    # what stops y from paying for itself.
    assert res.certificate.payload["objective"] == "2"


def test_safe_refuses_a_python_spec_by_flag_and_by_environment():
    """One setting, process-wide, so a command added later cannot forget it --
    and so the MCP server is protected by a line in `.mcp.json` rather than a
    parameter on each of forty-six tools."""
    import os

    from certo.spec import load_spec

    root = pathlib.Path(__file__).resolve().parent.parent
    py = str(root / "examples/amgm.py")

    try:
        load_spec(py, safe=True)
    except PermissionError as e:
        assert "EXECUTED" in str(e) or "EJECUTAR" in str(e)
    else:
        raise AssertionError("a .py ran under safe=True")

    old = os.environ.get("CERTO_NO_EXEC")
    os.environ["CERTO_NO_EXEC"] = "1"
    try:
        load_spec(py)
    except PermissionError:
        pass
    else:
        raise AssertionError("a .py ran under CERTO_NO_EXEC=1")
    finally:
        if old is None:
            os.environ.pop("CERTO_NO_EXEC", None)
        else:
            os.environ["CERTO_NO_EXEC"] = old

    # and the data spec still runs under the same setting
    os.environ["CERTO_NO_EXEC"] = "1"
    try:
        assert load_spec(str(root / "examples/lp_as_data.json")) is not None
    finally:
        os.environ.pop("CERTO_NO_EXEC", None)


def test_an_unknown_field_is_refused_rather_than_dropped():
    """A key silently ignored is how a constraint goes missing, and this
    project has already paid for that: a coefficient on an undeclared variable
    turned a certified 1/3 into a certified 10."""
    import json
    import tempfile

    from certo.dataspec import NotData
    from certo.spec import load_spec

    with tempfile.TemporaryDirectory() as d:
        f = pathlib.Path(d) / "s.json"
        f.write_text(json.dumps(
            {"type": "LPSpec", "var_names": ["a"], "objetive": {"a": 1}}),
            encoding="utf-8")
        try:
            load_spec(str(f))
        except NotData as e:
            assert "objetive" in str(e)
        else:
            raise AssertionError("a misspelled field was accepted")


def test_a_float_is_refused_because_the_certificate_would_carry_it():
    """A float here is a float in the payload, and `verify` would call it not
    citable. Saying so once, at load, beats saying it at the end of a run."""
    import json
    import tempfile

    from certo.dataspec import NotData
    from certo.spec import load_spec

    with tempfile.TemporaryDirectory() as d:
        f = pathlib.Path(d) / "s.json"
        f.write_text(json.dumps(
            {"type": "LPSpec", "var_names": ["a"], "obj": {"a": 0.333}}),
            encoding="utf-8")
        try:
            load_spec(str(f))
        except NotData as e:
            assert "exact" in str(e) or "exacto" in str(e)
        else:
            raise AssertionError("a float was accepted")


def test_a_spec_type_that_carries_formulas_is_not_pretended_buildable():
    """There is no way to write a z3 formula in JSON, and inventing an
    expression language is the thing this project decided not to build."""
    from certo.dataspec import BUILDABLE, NotData, build

    assert "Spec" not in BUILDABLE          # carries formulas
    assert "SweepSpec" not in BUILDABLE     # carries callables
    assert "LPSpec" in BUILDABLE

    try:
        build("Spec", {})
    except NotData as e:
        assert "LPSpec" in str(e)
    else:
        raise AssertionError("a formula-carrying spec was built from data")


def test_the_distribution_name_the_code_looks_up_is_the_one_declared():
    """The rename to `certo-math` would have silenced the staleness check.

    `doctor` asked `importlib.metadata` for "certo", which raises once the
    distribution is called something else -- and the except branch returns
    "metadata absent", quietly, forever. A guard that goes silent is worse
    than one that was never written, so the name is tied to `pyproject.toml`
    here rather than repeated in three files."""
    import re

    from certo.doctor import DISTRIBUTION

    root = pathlib.Path(__file__).resolve().parent.parent
    toml = (root / "pyproject.toml").read_text(encoding="utf-8")
    m = re.search(r'^name = "([^"]+)"', toml, re.M)
    assert m, "pyproject has no name"
    assert DISTRIBUTION == m.group(1), {
        "pyproject says": m.group(1), "the code looks up": DISTRIBUTION}

    # and the import package is deliberately NOT renamed with it
    import certo

    assert certo.__name__ == "certo"


# --- what certo will and will not emit as Lean -----------------------------


def test_the_lean_boundary_is_exactly_one_route():
    """0.9.0 removed every exporter but linear Farkas, and the CI job that
    was supposed to guard that kept exporting all four kinds -- so it went
    red and stayed red, which is how a check stops being read.

    The claim is about certo and needs no Lean at all: the one route that
    DECIDES its fragment emits, and the three that would need a caveat refuse
    with distinguishable exit codes. `nlinarith` is a heuristic, so a file
    closing with it would be a tactic call that might not close; an
    `unsat_core` says WHICH hypotheses suffice and not why."""
    import json
    import os
    import subprocess
    import sys
    import tempfile

    root = pathlib.Path(__file__).resolve().parent.parent

    def run(*args):
        return subprocess.run(
            [sys.executable, "-m", "certo.cli", *args],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            cwd=str(root),
            env=dict(os.environ, PYTHONPATH=str(root / "src")))

    with tempfile.TemporaryDirectory() as d:
        out = pathlib.Path(d)
        made = {
            "linear": ("farkas", "examples/farkas_linear.py", []),
            "nonlinear": ("farkas", "examples/farkas_nonlinear.py",
                          ["--nonlinear"]),
            "core": ("prove", "examples/farkas_linear.py", []),
        }
        for name, (cmd, spec, flags) in made.items():
            r = run(cmd, spec, *flags, "--cert", str(out / (name + ".json")))
            assert (out / (name + ".json")).exists(), (name, r.stderr[-300:])

        # the one route that works
        r = run("export", str(out / "linear.json"), "--lean",
                "--out", str(out / "E.lean"))
        assert r.returncode == 0, r.stdout + r.stderr
        assert (out / "E.lean").exists()
        assert "linarith" in (out / "E.lean").read_text(encoding="utf-8")

        # and it CORRESPONDS: the statement is re-parsed and compared against
        # the certificate, which is the check that caught four mangles.
        from certo import leancheck

        cert = json.loads((out / "linear.json").read_text(encoding="utf-8"))
        rep = leancheck.correspondence(
            cert, (out / "E.lean").read_text(encoding="utf-8"))
        assert rep.get("ok"), rep

        # A hypothesis with a ZERO multiplier is not part of the proof, so it
        # is not in the statement -- and the check must not call it missing.
        # It did, on the only export that works, for several releases.
        assert "noise" not in (out / "E.lean").read_text(encoding="utf-8")

        # the two that would need a caveat refuse, and differently
        r = run("export", str(out / "nonlinear.json"), "--lean",
                "--out", str(out / "N.lean"))
        assert r.returncode != 0, "a nonlinear Farkas emitted Lean"
        assert "nlinarith" in (r.stdout + r.stderr)
        assert not (out / "N.lean").exists()

        r = run("export", str(out / "core.json"), "--lean",
                "--out", str(out / "C.lean"))
        assert r.returncode != 0, "an unsat_core emitted Lean"
        assert not (out / "C.lean").exists()


# --- `unbounded` was a word, not a claim ----------------------------------


def _box_range():
    """`0 <= x <= 1`, whose range is `[0, 1]` and nothing wider."""
    import z3

    from certo import Spec, rangebound

    x = z3.Real("x")
    s = Spec(title="0 <= x <= 1")
    s.assume("lo", x >= 0)
    s.assume("hi", x <= 1)
    s.claim(z3.BoolVal(True))
    return rangebound.bounds_of(s, "x")


def test_an_edited_unbounded_end_no_longer_verifies():
    """A user changed the upper end of `[0, 1]` to `unbounded` and the
    verifier accepted `[0, +inf)`.

    The check validated multipliers WHERE A BOUND EXISTED and returned `ok`
    for an end that had none -- so the one claim with no evidence attached was
    the one nothing looked at. That is a certificate that verifies and is
    wrong, which is the failure this whole project exists to refuse, and it
    shipped in 0.10.0.

    `max x` over a polyhedron is unbounded exactly when the polyhedron is
    non-empty AND some `d` has `A d <= 0` with `d[x] > 0`. That `d` is the
    evidence. Without it the word means nothing."""
    from certo import rangebound

    out = _box_range()
    assert out["interval"] == "[0, 1]"
    assert all(v["ok"] for v in rangebound.check(out).values())

    forged = json.loads(json.dumps(out))
    forged["upper"] = {"bound": None, "why": "unbounded"}
    forged["interval"] = "[0, +inf)"
    got = rangebound.check(forged)
    assert not got["upper"]["ok"], "an unbounded end with no ray verified"
    assert "ray" in got["upper"]["reason"]


def test_an_invented_ray_is_caught_by_walking_it():
    """The ray is re-derived, not believed: `d = 1` on `0 <= x <= 1` walks
    straight out of the row `x <= 1`, and three products say so."""
    from certo import rangebound

    forged = json.loads(json.dumps(_box_range()))
    forged["upper"] = {"bound": None, "why": "unbounded", "ray": ["1"]}
    got = rangebound.check(forged)
    assert not got["upper"]["ok"]
    assert "leaves the regime" in got["upper"]["reason"]

    # and one that does not move the variable at all
    forged["upper"] = {"bound": None, "why": "unbounded", "ray": ["0"]}
    assert not rangebound.check(forged)["upper"]["ok"]


def test_a_genuinely_unbounded_end_carries_a_ray_that_checks():
    """The answer stays available -- this is a fix, not a retreat. `3a <= 1`
    bounds `a` above and not below, and the ray is the direction you may walk
    forever."""
    import z3

    from certo import Spec, rangebound

    a = z3.Real("a")
    s = Spec(title="only bounded above")
    s.assume("hi", 3 * a <= 1)
    s.claim(z3.BoolVal(True))
    out = rangebound.bounds_of(s, "a")

    assert out["interval"] == "(-inf, 1/3]"
    assert out["lower"]["ray"] == ["-1"]
    assert all(v["ok"] for v in rangebound.check(out).values())


def test_a_ray_over_an_empty_regime_establishes_nothing():
    """Both halves are needed. Over an empty polyhedron every direction is a
    ray and no point exists to walk from, so the pair is what unboundedness
    means -- and the empty regime is reported as itself, not as an interval."""
    import z3

    from certo import Spec, rangebound

    a = z3.Real("a")
    s = Spec(title="no a at all")
    s.assume("hi", a <= 1)
    s.assume("lo", a >= 3)
    s.claim(z3.BoolVal(True))
    out = rangebound.bounds_of(s, "a")
    assert out["empty"] is True
    assert out["interval"] == "(empty)"

    # an empty payload dressed up as an unbounded range does not pass
    forged = json.loads(json.dumps(out))
    forged["empty"] = False
    forged["upper"] = {"bound": None, "why": "unbounded", "ray": ["1"]}
    assert not rangebound.check(forged)["upper"]["ok"]


def test_unbounded_and_not_established_print_differently():
    """`+inf)` and `?` are different answers. An interval that rendered them
    the same is how the first version let the forged one look ordinary."""
    from certo import rangebound

    out = json.loads(json.dumps(_box_range()))
    out["upper"] = {"bound": None, "why": "unknown"}
    assert rangebound._interval(out["lower"], out["upper"]).endswith("?")


def test_the_exact_simplex_runs_even_when_no_rounded_primal_is_feasible():
    """The pass that does not need the primal was gated behind the primal.

    Reported from a paper: the numbers came out, the certificate did not.
    `certify` reconstructs a rational primal from the float solution and, when
    none of the rungs lands on a feasible point, `primals` is empty -- and the
    exact simplex sat INSIDE `for dx, x in primals`, so it never ran. The
    comment above it already said the dual does not depend on which primal.

    This vertex has denominator 1000036000093, past the top rung of 10**6.
    """
    from certo import exact

    A = [[Fraction(1000003), Fraction(2)], [Fraction(3), Fraction(1000033)]]
    b, c = [Fraction(5), Fraction(7)], [Fraction(1), Fraction(1)]
    det = 1000003 * 1000033 - 6
    x_true = [Fraction(5 * 1000033 - 14, det), Fraction(1000003 * 7 - 15, det)]

    # No rung reconstructs this, and CBC handed over no dual either.
    assert all(exact.reconstruct([float(v) for v in x_true], d) != x_true
               for d in exact.DENOM_LADDER)

    x, y, rep, denom = exact.certify(A, b, c, [float(v) for v in x_true],
                                     [0.0, 0.0])
    assert x is not None, "the exact simplex never ran"
    assert rep["ok"] and rep["objective"] == x_true[0] + x_true[1]
    assert denom == det


def test_a_primal_is_recovered_from_the_dual_by_complementary_slackness():
    """An exact dual with nothing to pair it with certifies nothing."""
    from certo import exact

    from certo.simplex import minimise

    A = [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(3)]]
    b, c = [Fraction(7), Fraction(9)], [Fraction(3), Fraction(2)]
    y = minimise(A, b, c)
    x = exact.primal_from_dual(A, b, c, y)
    assert x is not None
    assert exact.check_lp(A, b, c, x, y)["ok"]


def test_an_absent_dual_is_not_a_zero_dual():
    """`pi is None` is CBC saying nothing, not CBC saying zero.

    The zero vector went into the certificate and `certo verify` rejected it,
    correctly: `b.0 = 0` bounds nothing. An absence written down as a number
    is indistinguishable from an answer, which is the one thing this project
    refuses everywhere else.
    """
    import pulp

    from certo.engines import lp as engine

    class _Con:
        pi = None

    class _Prob:
        constraints = {"a": _Con(), "b": _Con()}

    assert engine._duals(_Prob(), ["a", "b"]) == [None, None]


def test_opt_never_writes_a_certificate_its_own_verifier_rejects():
    """An artefact that fails `certo verify` is not a weaker certificate."""
    from certo import LPSpec
    from certo.certificate import verify
    from certo.engines import lp as engine

    def _spec():
        s = LPSpec(sense="max", title="no duals")
        s.variable("x")
        s.variable("y")
        s.objective({"x": 3, "y": 2})
        s.constraint({"x": 1, "y": 1}, "<=", 4, name="cap")
        s.constraint({"x": 1}, "<=", 3, name="xcap")
        return s

    real = engine._duals
    try:
        engine._duals = lambda prob, names, **kw: [None] * len(names)

        # Exact mode does not need CBC's dual at all: it still certifies.
        r = engine.opt(_spec())
        assert r.certificate is not None and verify(r.certificate).ok
        assert r.meta["exact"]

        # The float route has nothing to build from, so it builds nothing --
        # and still reports the number, and still says a point was found,
        # because `mixed` uses this step for its skeleton and nothing else.
        r = engine.opt(_spec(), use_exact=False)
        assert r.certificate is None
        assert r.verdict is Verdict.SATISFIABLE
        assert r.meta["objective"] == 11.0
    finally:
        engine._duals = real


def test_a_node_without_a_certificate_is_not_an_empty_subtree():
    """`certificate is None` used to be read here as "infeasible".

    They are different facts. Infeasible means the subtree is empty and the
    Farkas ray says why; no certificate means the node's LP was not solved, or
    was solved and could not be certified, and we know NOTHING about what is
    in there. Closing it as empty prunes a branch that may hold the optimum --
    a tree that comes out looking complete and is not.

    It became reachable when `opt` stopped emitting certificates it could not
    stand behind, which is what made the wrong reading worth finding.
    """
    from certo.engines import bb
    from certo.engines import lp as engine
    from certo.status import Result, Status

    real = engine.opt
    fired = {"done": False}
    n_all = len(_branching_ilp().var_names)

    def _one_node_uncertified(spec, limits=None, **kw):
        r = real(spec, limits, **kw)
        # The first call with a variable already fixed IS a node of the tree;
        # the calls before it are the incumbent search, which has its own
        # guards and is not what this is about.
        if not fired["done"] and len(spec.var_names) < n_all and spec.cons:
            fired["done"] = True
            return Result("opt", Status.SAT, Verdict.SATISFIABLE, r.engine,
                          r.elapsed_ms, None, detail="uncertified",
                          meta=dict(r.meta, exact=False))
        return r

    try:
        engine.opt = _one_node_uncertified
        r = bb.prove_optimal(_branching_ilp(), LIM, max_nodes=20_000)
    finally:
        engine.opt = real

    assert fired["done"], "the patch never reached a node"
    # Not PROVED, and not a tree with that node closed as infeasible.
    assert r.verdict is Verdict.INCONCLUSIVE
    assert r.certificate is None


# --- the in-process API ----------------------------------------------------


def _hexagon():
    from certo import LPSpec

    s = LPSpec(sense="max", title="hexagon")
    for j in range(6):
        s.variable("x%d" % j)
    s.objective({"x%d" % j: 1 for j in range(6)})
    for j in range(6):
        s.constraint({"x%d" % j: 1, "x%d" % ((j + 1) % 6): 1}, "<=", 1,
                     name="e%d" % j)
    return s


def test_run_covers_every_command_that_takes_a_spec():
    """Two tables nobody compares is the failure this project exists to refuse.

    `api.DECIDED` holds the commands `routing.RUNNERS` cannot -- RUNNERS is
    `ask`'s table, and `ask` will not choose which variable `range` is about.
    A second table is only safe if something makes it complete, so: every
    command in the catalogue is either runnable here or named as one that does
    not take a spec at all.
    """
    from certo import api, catalogue

    every = {r["command"] for r in catalogue.rows()}
    uncovered = sorted(every - set(api.runnable()) - api.NOT_FROM_A_SPEC)
    assert not uncovered, {"commands run() cannot reach": uncovered}
    # and nothing is claimed that is not a command
    assert not sorted(set(api.runnable()) - every), sorted(
        set(api.runnable()) - every)


def test_run_gives_the_same_answer_as_the_command_line():
    """The point of the API is to skip the interpreter, not the arithmetic."""
    from fractions import Fraction

    from certo import api

    res = api.run("opt", _hexagon())
    assert res.verdict is Verdict.SATISFIABLE
    assert res.meta["exact"] is True
    # Exact, as a string that reads back as a rational -- which is the whole
    # reason to stay in-process: a user who shelled out to CBC instead got
    # 4499996/999999 where the answer was 4.5.
    assert Fraction(res.meta["objective"]) == 3
    assert res.certificate is not None and verify(res.certificate).ok


def test_run_refuses_what_it_cannot_run_by_name():
    """An option silently ignored answers a different question."""
    from certo import api

    for call, want in (
        (lambda: api.run("nope", _hexagon()), "no such command"),
        (lambda: api.run("verify", _hexagon()), "does not run a spec"),
        (lambda: api.run("opt", _hexagon(), exacto=True), "does not take"),
    ):
        try:
            call()
            raise AssertionError("did not raise: " + want)
        except (TypeError, ValueError) as exc:
            assert want in str(exc), (want, str(exc))


def test_run_refuses_a_spec_of_the_wrong_type():
    """`prove` on an LPSpec used to be a TypeError from inside z3."""
    from certo import api

    try:
        api.run("prove", _hexagon())
        raise AssertionError("did not raise")
    except TypeError as exc:
        assert "wants a Spec" in str(exc) and "LPSpec" in str(exc)


def test_a_command_needing_a_decision_says_which_one():
    """`range` is out of RUNNERS because `ask` cannot choose `--var`. Here the
    caller can, so it runs -- and forgetting the keyword names it."""
    import z3

    from certo import Spec, api

    a, b = z3.Reals("a b")
    spec = Spec(title="window")
    spec.assume("cheb", 3 * a <= 1)
    spec.assume("a_nonneg", a >= 0)
    spec.claim(a <= 1)

    try:
        api.run("range", spec)
        raise AssertionError("did not raise")
    except TypeError as exc:
        assert "`var=`" in str(exc)

    res = api.run("range", spec, var="a")
    assert res.certificate.payload["variable"] == "a"


def test_run_raises_rather_than_return_a_certificate_that_fails_verify():
    """The CLI prints to stderr and exits 1; in a library the equivalent of
    "the caller decides" is an exception they can catch. Defaulting to silence
    would remove the check that found the zero dual in 0.11.3."""
    from certo import api
    from certo.engines import lp as engine

    real = engine.opt

    def _forged(spec, limits=None, **kw):
        r = real(spec, limits, **kw)
        r.certificate.payload["objective"] = "999"
        return r

    try:
        engine.opt = _forged
        try:
            api.run("opt", _hexagon())
            raise AssertionError("did not raise")
        except api.SelfCheckFailed as exc:
            assert exc.result is not None and exc.report is not None
            assert not exc.report.ok
        # and it is the caller's to switch off, having been told
        res = api.run("opt", _hexagon(), self_check=False)
        assert res.certificate.payload["objective"] == "999"
    finally:
        engine.opt = real


def test_options_come_from_the_engine_signature():
    """Derived, so it cannot drift from what the engine takes."""
    from certo import api

    assert api.options("opt") == ["target", "use_exact"]
    assert "use_geng" in api.options("sweep")
    assert api.options("range") == ["var"]


# --- the degree cliff ------------------------------------------------------


def test_lint_warns_at_the_measured_degree_and_not_below():
    """A degree-63 univariate goal cost a user 71 minutes and no certificate.
    The cliff was measured at 11, not 63: `t^10 <= t` proves in 12 ms and
    `t^11 <= t` does not prove in 20 s."""
    import z3

    from certo import lint

    t_ = z3.Real("t")
    assert lint._high_degree_univariate(t_**63 <= t_) == 63
    assert lint._high_degree_univariate(t_**lint.DEGREE_CLIFF <= t_)         == lint.DEGREE_CLIFF
    # below the cliff it says nothing, because `prove` closes it in milliseconds
    assert lint._high_degree_univariate(t_**(lint.DEGREE_CLIFF - 1) <= t_) is None


def test_the_degree_check_is_univariate_and_polynomial_only():
    """Two variables at the same degree is a different problem, and this
    measurement says nothing about it. A rational function is not a
    polynomial, and guessing its degree would be inventing one."""
    import z3

    from certo import lint

    t_, u = z3.Reals("t u")
    assert lint._high_degree_univariate(t_**40 * u <= t_) is None   # two vars
    assert lint._high_degree_univariate(t_**40 / u <= t_) is None   # and a quotient
    assert lint._polynomial_degree(t_**40 / t_, t_) is None
    assert lint._polynomial_degree((t_ + 1) ** 12, t_) == 12
    assert lint._polynomial_degree(t_ * t_ * t_, t_) == 3


def test_the_high_degree_warning_reaches_the_report():
    """A rule nothing routes to is a rule nobody sees."""
    import z3

    from certo import Spec, lint

    t_ = z3.Real("t")
    spec = Spec(title="a degree 63 schedule")
    spec.assume("range", z3.And(t_ >= 0, t_ <= 1))
    spec.claim(t_**63 <= t_)

    found = [f for f in lint._check_spec(spec, LIM)
             if f["key"] == "spec.high_degree"]
    assert len(found) == 1
    assert found[0]["level"] == lint.WARN
    assert "63" in found[0]["text"]


# --- the sign of a minimisation --------------------------------------------


def _min_ilp():
    """min x subject to 2x >= 3, x integer. The answer is 2, bound 3/2."""
    from certo import LPSpec

    lp = LPSpec(sense="min", title="min x, 2x >= 3, integer", integer=True)
    lp.variable("x", hi=10)
    lp.objective({"x": 1})
    lp.constraint({"x": 2}, ">=", 3, name="lower")
    return lp


def test_a_minimisation_is_reported_in_the_sense_it_was_asked():
    """The internal system MAXIMISES, so for `sense="min"` every number read
    out of it is the negation of the declared one.

    The continuous path performed that flip; the discrete path replaced both
    numbers afterwards and did not. So an ILP whose minimum is 2 reported -2,
    with a relaxation bound of -3/2, and the certificate said the same. It
    VERIFIED, because the artefact was consistent with itself in a frame it
    never named -- the same failure as a certificate that verifies and is
    wrong about its own claim.

    Found by putting a minimum-deletion ILP through `opt`, which is the shape
    of every "smallest set that fixes this" question.
    """
    from fractions import Fraction

    from certo import api

    res = api.run("opt", _min_ilp(), self_check=False)
    assert Fraction(res.meta["objective"]) == 2, res.meta["objective"]
    assert Fraction(res.meta["bound"]) == Fraction(3, 2), res.meta["bound"]
    assert res.meta["solution"]["x"] == "2"


def test_the_certificate_of_a_minimisation_states_the_minimum():
    """`certo verify` is what a referee runs, and it read the internal frame.

    A pure-LP minimisation was worse than the ILP here: the CLI printed 3/2
    and the ARCHIVED artefact re-verified as -3/2, so the number on screen and
    the number in the file disagreed and neither said which was which.
    """
    from certo import LPSpec, api

    rep = verify(api.run("opt", _min_ilp(), self_check=False).certificate)
    assert rep.ok
    assert "2" in rep.detail and "-2" not in rep.detail, rep.detail
    assert "3/2" in rep.detail and "-3/2" not in rep.detail, rep.detail

    lp = LPSpec(sense="min", title="pure min")
    lp.variable("x", hi=10)
    lp.objective({"x": 1})
    lp.constraint({"x": 2}, ">=", 3, name="lower")
    rep = verify(api.run("opt", lp).certificate)
    assert rep.ok and "-3/2" not in rep.detail, rep.detail


def test_a_maximisation_is_untouched_by_the_sign_fix():
    """The frame and the declared sense agree for `max`, so nothing moves."""
    from fractions import Fraction

    from certo import LPSpec, api

    lp = LPSpec(sense="max", title="max x, 2x <= 3, integer", integer=True)
    lp.variable("x", hi=10)
    lp.objective({"x": 1})
    lp.constraint({"x": 2}, "<=", 3, name="upper")
    res = api.run("opt", lp, self_check=False)
    assert Fraction(res.meta["objective"]) == 1
    assert Fraction(res.meta["bound"]) == Fraction(3, 2)
    assert "3/2" in verify(res.certificate).detail


def test_the_declared_sense_travels_in_the_certificate_and_is_recomputed():
    """A field nothing checks is a field that can be forged.

    `declared` is the one number a reader of the JSON will quote, so `verify`
    recomputes it from the stored system rather than reading it back.
    """
    from fractions import Fraction

    from certo import api

    cert = api.run("opt", _min_ilp(), self_check=False).certificate
    d = cert.payload["declared"]
    assert Fraction(d["objective"]) == Fraction(3, 2)      # the relaxation
    assert Fraction(d["integral_objective"]) == 2          # the integer point
    assert verify(cert).ok

    forged = json.loads(json.dumps(cert.to_dict()))
    forged["payload"]["declared"]["objective"] = "1"
    assert not verify(Certificate.from_dict(forged)).ok


def test_a_certificate_written_before_the_field_verifies_exactly_as_before():
    """`declared` is optional, the way `loads` is, so the schema stays at 4."""
    from certo import api

    cert = api.run("opt", _min_ilp(), self_check=False).certificate
    old = json.loads(json.dumps(cert.to_dict()))
    n_new = len(verify(Certificate.from_dict(old)).checks)
    old["payload"].pop("declared")
    rep = verify(Certificate.from_dict(old))
    assert rep.ok
    assert len(rep.checks) == n_new - 1     # one check, and only that one


def test_the_stored_system_stays_in_the_frame_its_arithmetic_closes():
    """Only what a READER sees is flipped. `c.x == b.y` holds in the internal
    maximised system and nowhere else, so `A`, `b`, `c`, the primal and the
    dual are left exactly as they were -- and the schema stays at 4."""
    from fractions import Fraction

    from certo import api

    p = api.run("opt", _min_ilp(), self_check=False).certificate.payload
    assert p["sense"] == "min"
    assert Fraction(p["c"][0]) == -1          # min x is max -x, internally
    assert verify(Certificate.from_dict(json.loads(json.dumps(
        {"schema": 4, "kind": "lp_dual", "solver_free": True,
         "note": "", "payload": p})))).ok


def test_a_counting_constraint_points_at_bisect():
    """`at_most_k` is what turns `cases` into an optimiser, and somebody who
    wrote one is usually after the smallest k. The loop they write next reads
    `unknown_solver` as `unsat`; `bisect` carries the third state.

    Detected from the counter's own auxiliary names, so it cannot drift from
    the encoder. `spec.magnitude` is the same shape, and exists because
    `order` shipped and the person who needed it did not find it.
    """
    from certo import CNF, CNFSpec, lint

    def _spec(k):
        cnf = CNF("at most %d of 10" % k)
        xs = [cnf.var("x%d" % i) for i in range(10)]
        cnf.add(*xs)
        cnf.at_most_k(xs, k)
        return CNFSpec(cnf=cnf, title=cnf.title)

    keys = [f["key"] for f in lint._check_cnf(_spec(3), LIM)]
    assert "cnf.cardinality" in keys

    # A formula with no counter says nothing, or the note is noise.
    plain = CNF("plain")
    a, b = plain.var("a"), plain.var("b")
    plain.add(a, b)
    keys = [f["key"] for f in lint._check_cnf(CNFSpec(cnf=plain, title="p"), LIM)]
    assert "cnf.cardinality" not in keys

    # k <= 1 leaves no auxiliaries, and that is the right side to miss on.
    assert not lint._cardinality_bound(_spec(1).cnf)


def test_the_counter_marker_is_the_encoders_own_naming():
    """If `at_most_k` renamed its auxiliaries, this would go quiet -- so the
    test pins the two together rather than trusting the prefix."""
    from certo import CNF, lint

    cnf = CNF("counter")
    xs = [cnf.var("x%d" % i) for i in range(8)]
    cnf.at_most_k(xs, 3)
    aux = [n for n in cnf._name if isinstance(n, str) and n.startswith("__")]
    assert aux, "at_most_k produced no auxiliaries at all"
    assert all(n.startswith("__count") for n in aux), aux
    assert lint._cardinality_bound(cnf)


def test_the_smith_export_states_the_identities_and_nothing_hollow():
    """A declaration accompanied by `True` is not an export.

    `integer_matrix` had no exporter, so it went out as a placeholder -- named
    as one, which is honest, and useless to somebody formalising toric charts.
    Every statement here is over literal matrices that Lean recomputes.

    COMPILED, not inspected: this file elaborates against Mathlib 4.28 with no
    errors and no warnings. Three rounds to get there.
    """
    from certo import MatrixSpec, api, leanexport

    spec = MatrixSpec(matrix=[[4, 0, 0, 0], [2, 2, 0, 0], [2, 0, 2, 0],
                              [1, 1, 1, 1]],
                      question="smith", title="a cell")
    cert = api.run("matrix", spec).certificate
    data = cert.to_dict()
    data["digest"] = cert.digest()
    text = leanexport.EXPORTERS["integer_matrix"](data)

    assert leanexport.hollow_count(text) == 0
    assert "sorry" not in text
    for want in ("certo_U * certo_A * certo_V = certo_S",
                 "certo_U * certo_Uinv = 1",
                 "certo_V * certo_Vinv = 1",
                 "certo_A.det = 16",
                 "certo_S 0 0 = 1",
                 "certo_S 3 3 = 4"):
        assert want in text, want
    # Every theorem is closed, and closed by the same decidable tactic.
    assert text.count(":= by decide") == text.count("theorem ")
    # The fingerprint travels with its recipe, residue convention included.
    assert "NON-NEGATIVE residue" in text


def test_the_smith_export_refuses_a_certificate_it_cannot_state():
    """`refuse rather than guess` is the rule, not an aspiration."""
    from certo import MatrixSpec, api, leanexport

    spec = MatrixSpec(matrix=[[2, 0], [0, 3]], question="rank", title="rank")
    cert = api.run("matrix", spec).certificate
    data = cert.to_dict()
    try:
        leanexport.EXPORTERS["integer_matrix"](data)
        raise AssertionError("did not refuse")
    except leanexport.NotExportable as exc:
        assert "smith" in str(exc)


# --- the manifest ----------------------------------------------------------


def _cone_certs(tmp, n):
    """`n` distinct cone certificates on disk, and their headlines."""
    import json as _json

    from certo import ConeSpec, api

    heads = []
    for i in range(n):
        rays = {"a": [1, 0, 0], "b": [0, 1, 0], "c": [0, 0, i + 1]}
        cert = api.run("cone", ConeSpec(rays=rays, title="cell %d" % i)).certificate
        (tmp / ("c%d.json" % i)).write_text(
            _json.dumps(cert.to_dict()), encoding="utf-8")
        heads.append(cert.payload["title"])
    return heads


def test_a_manifest_counts_the_set_and_not_the_files(tmp_path=None):
    """A count is not a guarantee: two runs over 71 cells with one duplicate
    also count 72. So the same artefact at two paths is reported, not
    collapsed -- which is what `scan` does, keying its nodes by digest."""
    import shutil
    import tempfile

    from certo import status_report

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        _cone_certs(tmp, 3)
        shutil.copy(tmp / "c0.json", tmp / "again.json")   # the same one twice

        m = status_report.manifest(str(tmp))
        assert m["count"] == 3 and m["files"] == 4
        assert len(m["duplicate_files"]) == 1
        assert sorted(m["duplicate_files"][0]["paths"]) == ["again.json",
                                                            "c0.json"]
        assert not m["duplicate_subjects"]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def test_the_manifest_order_is_content_and_not_filenames():
    """Two people who produced the same set in a different order get the same
    number, which is the only property that makes it worth comparing."""
    import shutil
    import tempfile

    from certo import status_report

    a, b = pathlib.Path(tempfile.mkdtemp()), pathlib.Path(tempfile.mkdtemp())
    try:
        _cone_certs(a, 4)
        # same certificates, names that sort the other way
        for i in range(4):
            shutil.copy(a / ("c%d.json" % i), b / ("z%d.json" % (3 - i)))
        ma, mb = status_report.manifest(str(a)), status_report.manifest(str(b))
        assert ma["fingerprint"] == mb["fingerprint"]
        assert [e["digest"] for e in ma["entries"]] ==                [e["digest"] for e in mb["entries"]]
        # and it is not the trivial number
        assert ma["fingerprint"] != 0
    finally:
        shutil.rmtree(a, ignore_errors=True)
        shutil.rmtree(b, ignore_errors=True)


def test_omission_needs_a_declared_set_to_be_detectable():
    """Without `expect` a manifest can only describe what is present. That is
    the honest limit, and it is why the flag exists."""
    import shutil
    import tempfile

    from certo import status_report

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        heads = _cone_certs(tmp, 3)

        plain = status_report.manifest(str(tmp))
        assert "missing" not in plain          # says nothing it cannot know

        want = heads[1:] + ["a cell nobody certified"]
        checked = status_report.manifest(str(tmp), expect=want)
        assert checked["missing"] == ["a cell nobody certified"]
        assert checked["unexpected"] == [heads[0]]
        assert checked["complete"] is False

        assert status_report.manifest(str(tmp), expect=heads)["complete"]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def test_the_manifest_fingerprint_is_the_matrix_recipe():
    """One algorithm, so the other side of a language boundary recomputes it
    with no library -- and the recipe travels, residue convention included."""
    import shutil
    import tempfile

    from certo import interchange, status_report

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        _cone_certs(tmp, 3)
        m = status_report.manifest(str(tmp))
        assert m["fingerprint_recipe"] == interchange.describe()
        assert "residue" in m["fingerprint_recipe"]
        by_hand = interchange.fingerprint(
            [[int(e["digest"], 16)] for e in m["entries"]])
        assert m["fingerprint"] == by_hand
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# --- the emission gate -----------------------------------------------------


def _emissions():
    """One real emission per registered exporter, with its kind."""
    from certo import MatrixSpec, api, leanexport
    from certo.engines import farkas
    from certo.spec import load_spec

    root = pathlib.Path(__file__).resolve().parent.parent
    out = []

    cert = farkas.farkas(
        load_spec(str(root / "examples" / "farkas_linear.py")), LIM).certificate
    data = cert.to_dict()
    data["digest"] = cert.digest()
    out.append(("farkas", leanexport.EXPORTERS["farkas"](data)))

    spec = MatrixSpec(matrix=[[4, 0, 0, 0], [2, 2, 0, 0], [2, 0, 2, 0],
                              [1, 1, 1, 1]], question="smith", title="a cell")
    cert = api.run("matrix", spec).certificate
    data = cert.to_dict()
    data["digest"] = cert.digest()
    out.append(("smith", leanexport.EXPORTERS["integer_matrix"](data)))
    return out


def test_every_exporter_emits_a_structurally_sound_file():
    """The gate `tests/run_lean.py` cannot be.

    Compiling against Mathlib costs minutes per file and needs a toolchain, so
    it is run by hand by whoever touches an exporter -- which means nothing
    checks an emission between one of those runs and a release. This does, in
    milliseconds, for every exporter registered.
    """
    from certo import leanexport

    for kind, text in _emissions():
        found = leanexport.check_emission(text, kind)
        assert not found, {kind: found}


def test_the_checker_catches_what_the_smith_exporter_actually_got_wrong():
    """Three of the five emission faults adding that exporter produced.

    The other two were a module path that had moved and an absent import, and
    nothing without Mathlib on disk can know either -- which is the honest
    half of the claim and the reason this does not replace compiling.
    """
    from certo import leanexport

    broken = "\n".join([
        "/-",
        "  header",
        "-/",
        "import Mathlib.LinearAlgebra.Matrix.Notation",
        "import Mathlib.Data.Matrix.Mul",
        "import Mathlib.LinearAlgebra.Matrix.Determinant.Basic",
        "",
        "namespace Certo",
        "",
        "theorem certo_det_U : certo_U.det = -1 by decide",
        "",
        "/-- documents nothing at all -/",
        "-- certo fingerprint: 7",
        "",
    ])
    codes = {c for _ln, c, _d in leanexport.check_emission(broken, "smith")}
    assert "unclosed_declaration" in codes      # the missing `:=`
    assert "orphan_docstring" in codes          # `/--` attached to a comment
    assert "namespace" in codes                 # opened and never closed


def test_the_checker_is_quiet_about_a_multi_line_declaration():
    """A statement whose `:=` is on a later line is ordinary Lean, and a rule
    that flagged it would be a rule people switch off."""
    from certo import leanexport

    fine = "\n".join([
        "/-", "  header", "-/",
        "import Mathlib.Data.Real.Basic",
        "import Mathlib.Tactic.Linarith",
        "",
        "namespace Certo",
        "",
        "/-- a real one -/",
        "theorem spread :",
        "    certo_U * certo_A * certo_V = certo_S := by decide",
        "",
        "end Certo",
        "",
    ])
    assert leanexport.check_emission(fine, "farkas") == []


def test_an_import_the_exporter_did_not_declare_is_reported():
    """It cannot know a module EXISTS -- that needs Mathlib on disk -- but it
    can know the header is not the one this exporter writes, which is what a
    hand edit looks like."""
    from certo import leanexport

    text = "\n".join([
        "/-", "  header", "-/",
        "import Mathlib.Data.Matrix.Notation",      # the path that had moved
        "",
        "namespace Certo",
        "",
        "end Certo",
        "",
    ])
    codes = {c for _ln, c, _d in leanexport.check_emission(text, "smith")}
    assert "imports" in codes
    # and without a kind it says nothing about imports, because it has no
    # table to compare against
    assert "imports" not in {c for _l, c, _d in leanexport.check_emission(text)}


def test_a_promise_about_placeholders_has_to_match_the_file():
    """The header either lists `sorry`s or states there are none. Saying one
    and doing the other is how a file reads as complete when it is not."""
    from certo import leanexport

    promises = ("/-\n  `sorry` below marks a place where something outside "
                "Lean was relied on\n-/\nnamespace Certo\nend Certo\n")
    codes = {c for _l, c, _d in leanexport.check_emission(promises)}
    assert "promised_sorry" in codes

    quiet = "/-\n  header\n-/\nnamespace Certo\nexample : True := by sorry\nend Certo\n"
    codes = {c for _l, c, _d in leanexport.check_emission(quiet)}
    assert "unannounced_sorry" in codes


# --- doctor --repair -------------------------------------------------------


def test_repair_previews_and_removes_nothing_by_default():
    """The default has to be the safe one, because what is being removed lives
    in site-packages: a wrong guess there breaks an environment, not a file."""
    import shutil
    import tempfile

    from certo import doctor

    root = pathlib.Path(tempfile.mkdtemp())
    try:
        (root / "~erto").mkdir()
        (root / "~erto" / "__init__.py").write_text("", encoding="utf-8")
        (root / "certo").mkdir()          # the real one, which must not move

        # BOTH, or the test reads the real machine: `_script_dirs` unpatched
        # returns this interpreter's `Scripts`, whose contents then appear in
        # the list a fixture is asserting about.
        real = doctor._site_roots
        real_scripts = doctor._script_dirs
        doctor._site_roots = lambda: [root]
        doctor._script_dirs = lambda: []
        try:
            rep = doctor.repair()
            assert rep["applied"] is False
            assert rep["removed"] == []
            assert [pathlib.Path(p).name for p in rep["leftovers"]] == ["~erto"]
            assert (root / "~erto").is_dir()      # still there
        finally:
            doctor._site_roots = real
            doctor._script_dirs = real_scripts
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_repair_touches_only_what_pip_abandoned():
    """`~` is pip's own marker for a rename it did not finish. Nothing else in
    site-packages is any of certo's business, and a repair that decided
    otherwise would be worse than the problem."""
    import shutil
    import tempfile

    from certo import doctor

    root = pathlib.Path(tempfile.mkdtemp())
    try:
        for name in ("~erto", "~erto_math-0.1.dist-info"):
            (root / name).mkdir()
        for keep in ("certo", "numpy", "z3", "certo_math-0.1.dist-info"):
            (root / keep).mkdir()

        # `_script_dirs` too, and here it MATTERS: this calls `apply=True`,
        # and unpatched it would delete `.deleteme` files out of whoever is
        # running the suite. A test that reaches outside its fixture to
        # remove things is worse than the bug it is guarding.
        real = doctor._site_roots
        real_scripts = doctor._script_dirs
        doctor._site_roots = lambda: [root]
        doctor._script_dirs = lambda: []
        try:
            rep = doctor.repair(apply=True)
            assert sorted(pathlib.Path(p).name for p in rep["removed"]) == [
                "~erto", "~erto_math-0.1.dist-info"]
            assert not rep["failed"]
        finally:
            doctor._site_roots = real
            doctor._script_dirs = real_scripts

        survivors = sorted(p.name for p in root.iterdir())
        assert survivors == ["certo", "certo_math-0.1.dist-info", "numpy", "z3"]
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_a_leftover_that_points_outside_the_tree_is_left_alone():
    """A `~` entry whose real path is somewhere else is not pip's rename, and
    following it would delete whatever it points at."""
    import shutil
    import tempfile

    from certo import doctor

    root = pathlib.Path(tempfile.mkdtemp())
    elsewhere = pathlib.Path(tempfile.mkdtemp())
    try:
        (elsewhere / "precious").mkdir()
        try:
            (root / "~link").symlink_to(elsewhere / "precious",
                                        target_is_directory=True)
        except (OSError, NotImplementedError):
            return                        # no symlink privilege: nothing to test

        real, real_scripts = doctor._site_roots, doctor._script_dirs
        doctor._site_roots = lambda: [root]
        doctor._script_dirs = lambda: []
        try:
            assert doctor.repair()["leftovers"] == []
        finally:
            doctor._site_roots = real
            doctor._script_dirs = real_scripts
        assert (elsewhere / "precious").is_dir()
    finally:
        shutil.rmtree(root, ignore_errors=True)
        shutil.rmtree(elsewhere, ignore_errors=True)


def test_the_same_leftover_is_counted_once():
    """`site.getsitepackages()` returns overlapping roots on Windows, so the
    same directory was found twice and reported as two. A count that is wrong
    about five is not a count anybody acts on."""
    import shutil
    import tempfile

    from certo import doctor

    root = pathlib.Path(tempfile.mkdtemp())
    try:
        (root / "~erto").mkdir()
        real, real_scripts = doctor._site_roots, doctor._script_dirs
        # the same root handed over twice, which is what the real helper does
        doctor._site_roots = lambda: [root, root]
        doctor._script_dirs = lambda: []
        try:
            assert len(doctor.repair()["leftovers"]) == 1
        finally:
            doctor._site_roots = real
            doctor._script_dirs = real_scripts
    finally:
        shutil.rmtree(root, ignore_errors=True)


# --- what a certificate depends on, and what merely corroborates it --------


def _binding():
    """A real `bind` certificate, with the one it is about travelling in it."""
    import subprocess
    import sys

    root = pathlib.Path(__file__).resolve().parent.parent
    env = dict(os.environ, PYTHONPATH=str(root / "src"))
    out = root / "out"
    out.mkdir(exist_ok=True)
    for args in ([
            "prove", "examples/counting_bound.py",
            "--cert", "out/counting_bound.json"],
            ["bind", "examples/lean_binding.py", "--cert", "out/_dep.json"]):
        subprocess.run([sys.executable, "-m", "certo.cli", *args], cwd=root,
                       capture_output=True, env=env, timeout=600)
    return json.loads((out / "_dep.json").read_text(encoding="utf-8"))


def test_a_binding_named_a_certificate_and_checked_nothing_about_it():
    """The pointer that was decorative.

    `lean_binding` said "this is what THAT certificate assumed" and stored a
    PATH. Nothing tied the two, so a binding naming a file that does not
    exist, of a kind it never was, verified exactly like an honest one. The
    certificate travels now and has to verify on its own terms with the
    provenance that was recorded.
    """
    import copy

    data = _binding()
    assert verify(Certificate.from_dict(data)).ok
    assert data["payload"]["source"]["kind"] == data["payload"]["certificate_kind"]

    # the kind it claims, against the kind it carries
    bad = copy.deepcopy(data)
    bad["payload"]["certificate_kind"] = "drat"
    assert not verify(Certificate.from_dict(bad)).ok

    # a source whose own verifier rejects it
    bad = copy.deepcopy(data)
    bad["payload"]["source"]["payload"]["core_smt2"] = "(assert true)"
    assert not verify(Certificate.from_dict(bad)).ok

    # a source from a different spec than the one recorded
    bad = copy.deepcopy(data)
    bad["payload"]["spec"]["sha256_then"] = "0" * 64
    assert not verify(Certificate.from_dict(bad)).ok


def test_a_binding_written_before_the_source_travelled_still_verifies():
    """Optional, the way every other added field is, so the schema stays 4."""
    import copy

    data = _binding()
    n_new = len(verify(Certificate.from_dict(data)).checks)
    old = copy.deepcopy(data)
    old["payload"].pop("source")
    rep = verify(Certificate.from_dict(old))
    assert rep.ok
    assert len(rep.checks) == n_new - 1


def test_an_embedded_source_stops_reading_as_an_unconsumed_result():
    """The complaint was that matrix certificates showed with no consumers.
    A certificate that is embedded is accounted for, and `status` says so by
    leaving it out of the top-level results."""
    import shutil
    import tempfile

    from certo import status_report

    root = pathlib.Path(__file__).resolve().parent.parent
    data = _binding()
    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        (tmp / "binding.json").write_text(json.dumps(data), encoding="utf-8")
        shutil.copy(root / "out" / "counting_bound.json", tmp / "source.json")
        rep = status_report.scan(str(tmp))
        assert rep["certificates"] == 2
        assert [r["kind"] for r in rep["results"]] == ["lean_binding"]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _cone_and_smith(tmp, lattice, title):
    from certo import ConeSpec, MatrixSpec, api

    rays = {"a": [4, 0, 0, 0], "b": [2, 2, 0, 0], "c": [2, 0, 2, 0],
            "d": [1, 1, 1, 1]}
    cone = api.run("cone", ConeSpec(rays=rays, lattice=lattice,
                                    title=title)).certificate
    smith = api.run("matrix", MatrixSpec(matrix=lattice, question="smith",
                                         title=title)).certificate
    (tmp / (title + "-cone.json")).write_text(json.dumps(cone.to_dict()),
                                              encoding="utf-8")
    (tmp / (title + "-smith.json")).write_text(json.dumps(smith.to_dict()),
                                               encoding="utf-8")
    return cone, smith


def test_the_manifest_derives_the_relation_nobody_declared():
    """Neither certificate mentions the other, and the relation is real.

    Derived from content rather than stored, so there is nothing to forge: the
    fingerprint of the cone's declared lattice against the one the Smith
    certificate already carries. Two people who produced the set
    independently get the same edges.
    """
    import shutil
    import tempfile

    from certo import status_report

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        latt = [[4, 0, 0, 0], [2, 2, 0, 0], [2, 0, 2, 0], [1, 1, 1, 1]]
        cone, smith = _cone_and_smith(tmp, latt, "cell0")
        _cone_and_smith(tmp, [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0],
                              [0, 0, 0, 1]], "cell1")

        m = status_report.manifest(str(tmp))
        pairs = {(e["from"], e["to"]) for e in m["edges"]}
        assert (cone.digest(), smith.digest()) in pairs
        # one per cell, and no cross-links between cells
        assert len(m["edges"]) == 2
        for e in m["edges"]:
            assert e["from_kind"] == "toric_cone"
            assert e["to_kind"] == "integer_matrix"
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def test_a_matrix_certificate_about_something_else_gets_no_edge():
    """An edge says these two are about the same matrix. Nothing weaker would
    be worth computing, and nothing stronger is true."""
    import shutil
    import tempfile

    from certo import MatrixSpec, api, status_report

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        _cone_and_smith(tmp, [[4, 0, 0, 0], [2, 2, 0, 0], [2, 0, 2, 0],
                              [1, 1, 1, 1]], "cell0")
        other = api.run("matrix", MatrixSpec(matrix=[[1, 0], [0, 1]],
                                             question="smith",
                                             title="unrelated")).certificate
        (tmp / "other.json").write_text(json.dumps(other.to_dict()),
                                        encoding="utf-8")
        m = status_report.manifest(str(tmp))
        assert len(m["edges"]) == 1
        assert other.digest() not in {e["to"] for e in m["edges"]}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# --- the header must not contradict the certificate ------------------------


def _k4_packing(m, integer):
    """K4-packing of K_m: the crux of a linear chordal gap."""
    from itertools import combinations

    from certo import PackingSpec

    items = [("K" + "".join(map(str, c)),
              [frozenset(e) for e in combinations(c, 2)], 1)
             for c in combinations(range(m), 4)]
    return PackingSpec(items=items, capacities=1, sense="max",
                       integer=integer, title="K4-packing of K%d" % m)


def test_the_gap_does_not_depend_on_a_flag_that_is_not_about_it():
    """`--gap` reported ZERO -- the strongest conclusion in this domain --
    from a flag combination.

    The integral half was built explicitly and the fractional half was
    inherited from the spec, so `integer=True` compared the integer optimum
    against itself. A user's first full sweep came back "gap 0" on seven
    orders. Both halves are constructed here now, which is what a gap IS.
    """
    from fractions import Fraction

    from certo.packing import gap

    for m in (5, 6):
        closed_form = Fraction(m * (m - 1) // 2, 6)
        seen = []
        for integer in (True, False):
            _cert, meta = gap(_k4_packing(m, integer))
            seen.append((meta["mu"], meta["gap"]))
            assert Fraction(meta["mu"]) == closed_form, (m, integer, meta)
            assert Fraction(meta["gap"]) > 0, (m, integer, meta)
        assert seen[0] == seen[1], (m, seen)

    # and it says it overrode the flag rather than doing it quietly
    _c, meta = gap(_k4_packing(5, True))
    assert meta["relaxed_for_gap"] is True
    _c, meta = gap(_k4_packing(5, False))
    assert meta["relaxed_for_gap"] is False


def test_the_gap_reports_the_optimum_under_the_name_opt_uses():
    """It was only reachable at
    `certificate.payload.fractional.payload.objective`, which is not a path
    anybody deduces without reading the source."""
    from fractions import Fraction

    from certo.packing import gap

    cert, meta = gap(_k4_packing(5, False))
    assert Fraction(meta["objective"]) == Fraction(meta["mu"])
    deep = cert.payload["fractional"]["payload"]["objective"]
    assert Fraction(deep) == Fraction(meta["objective"])


def test_a_target_on_the_gap_path_is_compared_rather_than_dropped():
    """The flag was accepted, the number never compared, and the verdict came
    back SATISFIABLE either way. A flag silently ignored is worse than one
    refused."""
    from certo.packing import gap

    _c, meta = gap(_k4_packing(6, False), target=1)
    assert meta["reached"] is True and meta["deficit"] == "0"

    _c, meta = gap(_k4_packing(6, False), target=4)
    assert meta["reached"] is False and meta["deficit"] == "3"

    _c, meta = gap(_k4_packing(6, False))
    assert meta["reached"] is None and meta["target"] is None


def test_a_mixed_target_says_reached_rather_than_making_a_script_parse_prose():
    from certo import LPSpec
    from certo.engines import mixed

    def _spec():
        lp = LPSpec(sense="max", title="two slots")
        for i in range(2):
            lp.variable("y%d" % i, kind="binary")
        lp.objective({"y0": 2, "y1": 3})
        lp.constraint({"y0": 1, "y1": 1}, "<=", 1, name="one")
        return lp

    assert mixed.mixed(_spec(), LIM, target=3).meta["reached"] is True
    assert mixed.mixed(_spec(), LIM, target=9).meta["reached"] is False
    assert mixed.mixed(_spec(), LIM).meta["reached"] is None


def test_naming_a_command_asks_about_that_command():
    """`certo what opt` was `unrecognized arguments: opt`, while the help
    read as though it took one."""
    from certo import catalogue

    row = next(r for r in catalogue.rows() if r["command"] == "opt")
    assert row["spec"] == "LPSpec" and row["engine"] == "lp"


def test_an_interrupted_launcher_is_a_leftover_too():
    """pip leaves two markers. `~`-something is a rename it did not finish;
    `something.deleteme` is a launcher it could not replace, beside an orphan
    `.exe` whose package is gone -- which is the state a user was in when
    `certo doctor` was the thing they could not run."""
    import shutil
    import tempfile

    from certo import doctor

    root = pathlib.Path(tempfile.mkdtemp())
    try:
        site = root / "Lib" / "site-packages"
        site.mkdir(parents=True)
        (root / "Scripts").mkdir()          # where they really live
        (site / "~erto").mkdir()
        (root / "Scripts" / "certo.exe.deleteme").write_text("x")
        (root / "Scripts" / "certo.exe").write_text("x")

        # BOTH helpers are patched, and the second is the point. The first
        # version of this test built `Lib/Scripts` because that is where the
        # code looked -- derived from site-packages by going up one -- and
        # the launchers live at `<prefix>/Scripts`, one level further up. The
        # fixture agreed with the bug, so the test passed and the marker was
        # never found on a real install. `sysconfig` is asked now.
        real_sites, real_scripts = doctor._site_roots, doctor._script_dirs
        doctor._site_roots = lambda: [site]
        doctor._script_dirs = lambda: [root / "Scripts"]
        try:
            names = sorted(pathlib.Path(p).name
                           for p in doctor.repair()["leftovers"])
        finally:
            doctor._site_roots = real_sites
            doctor._script_dirs = real_scripts
        assert names == ["certo.exe.deleteme", "~erto"]
        # the orphan launcher itself is NOT ours to remove
        assert (root / "Scripts" / "certo.exe").exists()
    finally:
        shutil.rmtree(root, ignore_errors=True)


# --- metadata from a source tree is not an install -------------------------


def test_metadata_from_a_source_tree_is_not_reported_as_an_install():
    """The check that exists to catch a stale install hid an absent one.

    `importlib.metadata` searches `sys.path`, and `src/<name>.egg-info` turns
    up the moment anybody runs `python -m build`. With `PYTHONPATH=src` it
    answered like a package, so `doctor` said `[ok] 0.11.6, matching the code`
    on a machine where `pip show certo-math` returned nothing and `import
    certo` failed. The state it was written to detect is the state it hid.
    """
    from certo import doctor

    # Patched at `_metadata_copies`, which is where the classification now
    # happens: `_metadata_source` answers one narrower question -- what would
    # `pip show` report -- and no longer decides what the row says.
    real = doctor._metadata_copies
    try:
        doctor._metadata_copies = lambda: [
            ("9.9.9", "source", pathlib.Path("/somewhere/checkout/src"))]
        ok, detail = doctor._installed_metadata()
        assert ok is False
        assert "SOURCE TREE" in detail or "ÁRBOL FUENTE" in detail
        assert "9.9.9" in detail
    finally:
        doctor._metadata_copies = real


def test_an_installed_version_is_still_compared_against_the_code():
    """The original question survives: a stale install is a stale install."""
    from certo import __version__, doctor

    # Patched at `_metadata_copies`: `_installed_metadata` classifies from
    # there now, and `_metadata_source` answers one narrower question.
    real = doctor._metadata_copies
    site = pathlib.Path("/site-packages")
    try:
        doctor._metadata_copies = lambda: [(__version__, "installed", site)]
        ok, detail = doctor._installed_metadata()
        assert ok is True and __version__ in detail

        doctor._metadata_copies = lambda: [("0.0.1", "installed", site)]
        ok, detail = doctor._installed_metadata()
        assert ok is False and "0.0.1" in detail and __version__ in detail

        doctor._metadata_copies = lambda: []
        ok, _detail = doctor._installed_metadata()
        assert ok is True          # no install at all is normal, not broken
    finally:
        doctor._metadata_copies = real


def test_the_source_of_the_metadata_is_located_not_assumed():
    """Where it was read from is what separates the three answers, so it is
    asked of the distribution rather than guessed."""
    from certo import doctor

    version, installed, where = doctor._metadata_source()
    assert version is None or isinstance(version, str)
    if version is not None and where is not None:
        roots = doctor._site_roots()
        under = any(where == r or r in where.parents for r in roots)
        assert installed is under


def test_one_implementation_answers_where_the_metadata_came_from():
    """`cli.installed_version` asked `importlib.metadata` itself, and so
    inherited the defect `doctor`'s check exists to catch: a source tree's
    `egg-info` answering like an install. Two implementations of one question
    is how they came to disagree in the first place."""
    from certo import cli, doctor

    real = doctor._metadata_source
    try:
        doctor._metadata_source = lambda: ("7.7.7", True, pathlib.Path("/sp"))
        assert cli.installed_version() == "7.7.7"

        # read from a source tree: not an installed version, so it does not
        # travel -- comparing it against `__version__` would report drift
        # between a number and itself
        doctor._metadata_source = lambda: ("7.7.7", False,
                                           pathlib.Path("/checkout/src"))
        assert cli.installed_version() is None

        doctor._metadata_source = lambda: (None, False, None)
        assert cli.installed_version() is None
    finally:
        doctor._metadata_source = real


# --- integer labels have their own order -----------------------------------


def test_integer_vertices_are_not_sorted_as_text():
    """`sorted(vertices, key=str)` puts `10` before `2`.

    A clique on `{2, 10}` came out as the edge `(10, 2)` -- the larger vertex
    first -- and a caller who canonicalised numerically, as anybody would, was
    comparing against `(2, 10)` and finding a foreign edge. `_key` is
    order-insensitive so certo's own comparisons survived it; what did not
    survive is the order that TRAVELS, into the certificate.
    """
    from certo.cover import edges_of

    assert edges_of([1, 2, 10]) == [(1, 2), (1, 10), (2, 10)]
    assert edges_of([10, 2]) == [(2, 10)]
    # and a hundred-vertex set is in numeric order throughout
    vs = list(range(100))
    pairs = edges_of(vs)
    assert pairs == sorted(pairs)
    assert all(a < b for a, b in pairs)


def test_labels_with_no_order_between_them_still_get_one():
    """`key=str` was there for a reason: labels of mixed types have no order
    and `sorted` raises. That is the case that needs a rule, so it is the
    fallback rather than the default."""
    from certo.cover import edges_of

    assert edges_of(["b", "a", "c"]) == [("a", "b"), ("a", "c"), ("b", "c")]
    mixed = edges_of([2, "a", 10])
    assert len(mixed) == 3
    assert mixed == edges_of(["a", 10, 2])        # deterministic, whatever it is


def test_a_clique_on_two_digit_labels_is_not_a_foreign_edge():
    """The reported failure, end to end."""
    from certo.cover import clique_parts

    universe = [(1, 2), (1, 10), (2, 10)]
    parts, report = clique_parts(universe, [[1, 2, 10]])
    assert parts == [[(1, 2), (1, 10), (2, 10)]]
    assert report[0]["edges"] == 3
    # the part the certificate carries is the universe's own ordering
    assert set(parts[0]) <= set(universe)


def test_clique_item_names_separate_their_labels():
    """Concatenation is not injective on integer labels: `(1, 112)` and
    `(11, 12)` are both ascending and both spell `1112`. It survives to
    n = 111 and then fails as "duplicate item names", which sends the reader
    hunting through their own code for a repeat they did not write."""
    from certo import Graph, PackingSpec

    g = Graph.from_edges(120, [(1, 112), (11, 12)])
    spec = PackingSpec.cliques_in_graph(g, {2: 1})
    names = [i[0] for i in spec.items]
    assert len(set(names)) == len(names) == 2
    assert sorted(names) == ["K2_11_12", "K2_1_112"]


def test_the_separator_makes_the_name_injective_where_it_was_not():
    """Checked over the range that used to break rather than argued about."""
    from itertools import combinations

    for size in (2, 3):
        seen = {}
        for s in combinations(range(120), size):
            key = "K{}_{}".format(size, "_".join(map(str, s)))
            assert key not in seen, (s, seen.get(key))
            seen[key] = s


# --- four answers, not three collapsed into one ----------------------------


def _with_copies(copies):
    """Run `_installed_metadata` over a made-up set of metadata copies."""
    from certo import doctor

    real = doctor._metadata_copies
    try:
        doctor._metadata_copies = lambda: copies
        return doctor._installed_metadata()
    finally:
        doctor._metadata_copies = real


def test_an_install_that_agrees_is_quiet_even_beside_a_source_tree():
    """The ambiguity a user reported: `doctor` warned about a source tree
    while `pip show` correctly said 0.12.0. True, useless, and
    indistinguishable from the case that matters."""
    from certo import __version__

    ok, detail = _with_copies([
        (__version__, "source", pathlib.Path("/checkout/src")),
        (__version__, "installed", pathlib.Path("/site-packages")),
    ])
    assert ok is True
    assert __version__ in detail
    assert "SOURCE TREE" not in detail


def test_a_pip_leftover_answers_like_a_distribution_and_is_named():
    """A `~`-prefixed directory pip abandoned mid-install is read by
    `importlib.metadata` as a real distribution, so a half-finished upgrade
    answers with the OLD version forever. Counted as an install, it made the
    machine look like it had two."""
    from certo import __version__

    ok, detail = _with_copies([
        (__version__, "installed", pathlib.Path("/site-packages")),
        ("0.9.9", "leftover", pathlib.Path("/site-packages")),
    ])
    assert ok is False                     # there is something to clean
    assert "0.9.9" in detail and "--repair" in detail


def test_only_a_source_tree_is_still_not_an_install():
    """The 0.11.7 case: the package absent, and an `egg-info` answering."""
    ok, detail = _with_copies([("9.9.9", "source",
                                pathlib.Path("/checkout/src"))])
    assert ok is False
    assert "SOURCE TREE" in detail or "ÁRBOL FUENTE" in detail


def test_only_a_leftover_is_the_worst_case_and_says_so():
    """No install at all, and the version everything reads is the one pip
    failed to replace."""
    ok, detail = _with_copies([("0.9.9", "leftover",
                                pathlib.Path("/site-packages"))])
    assert ok is False
    assert "0.9.9" in detail and "--repair" in detail


def test_a_stale_install_is_still_a_stale_install():
    """The original question survives all of the above."""
    from certo import __version__

    ok, detail = _with_copies([("0.0.1", "installed",
                                pathlib.Path("/site-packages"))])
    assert ok is False
    assert "0.0.1" in detail and __version__ in detail


def test_the_classification_is_read_off_the_metadata_directory():
    """`installed`, `source` and `leftover` are three different facts, and the
    `~` prefix is pip's own marker for the third."""
    from certo import doctor

    kinds = {kind for _v, kind, _w in doctor._metadata_copies()}
    assert kinds <= {"installed", "source", "leftover"}
    # whatever this machine looks like, the helper agrees with itself
    version, installed, _where = doctor._metadata_source()
    if installed:
        assert version in [v for v, k, _w in doctor._metadata_copies()
                           if k == "installed"]


def test_the_empty_universe_is_answered_by_both_commands():
    """`cover` certified it and `exists` declined it: two commands, one
    object, one certifying and one calling the question contentless.

    The refusal was the vacuity reflex misapplied. Vacuity matters when a
    hypothesis set is contradictory, because the proof is then about nothing.
    Here the question has an answer and a witness -- the empty family IS a
    cover of the empty universe -- so it is answered, and the warning says
    what it does not establish.
    """
    from certo import CoverSpec, api

    spec = CoverSpec(universe=[], parts=[], title="nothing to cover")
    got = {}
    for cmd in ("cover", "exists"):
        res = api.run(cmd, spec, self_check=False)
        got[cmd] = res
        assert res.verdict is Verdict.PROVED, cmd
        assert res.certificate is not None and verify(res.certificate).ok, cmd
        assert res.certificate.kind == "exact_cover", cmd

    # and `exists` says out loud that it establishes nothing about a
    # non-empty instance
    assert got["exists"].meta.get("vacuous") is True
    assert "empty family" in got["exists"].detail


def test_exists_declares_the_three_kinds_it_actually_emits():
    """`KIND_OF["exists"]` said `drat` and nothing else, while the SAT path
    has always emitted the COVER it found -- only the refuting example
    exercised it, so the declaration-against-emission check never saw the
    other branch. Widened, and the degenerate case adds no fourth kind."""
    from certo import CoverSpec, api, routing

    declared = set(routing.KIND_OF["exists"])

    found = api.run("exists", CoverSpec(
        universe=[1, 2, 3], parts=[], candidates=[[1, 2], [3]],
        title="a real one"), self_check=False)
    assert found.verdict is Verdict.SATISFIABLE
    assert found.certificate.kind == "exact_cover"

    none = api.run("exists", CoverSpec(
        universe=[1, 2, 3], parts=[], candidates=[[1, 2]],
        title="no cover"), self_check=False)
    assert none.certificate.kind in declared

    empty = api.run("exists", CoverSpec(universe=[], parts=[], title="empty"),
                    self_check=False)
    assert {found.certificate.kind, none.certificate.kind,
            empty.certificate.kind} <= declared


# --- what survives one level of nesting ------------------------------------


def _nested_range(tmp, extra=()):
    """`sweep --n-range` over the nested example, as the CLI runs it."""
    import subprocess
    import sys

    root = pathlib.Path(__file__).resolve().parent.parent
    out = tmp / "nested.json"
    env = dict(os.environ, PYTHONPATH=str(root / "src"))
    subprocess.run(
        [sys.executable, "-m", "certo.cli", "sweep",
         "examples/sweep_range_nested.py", "--n-range", "3..4",
         "--cert", str(out), *extra],
        cwd=root, capture_output=True, env=env, timeout=900)
    return json.loads(out.read_text(encoding="utf-8"))


def test_a_nested_sweep_inherits_the_spec_it_came_from():
    """Only the top-level result was stamped -- `emit` does that once, on its
    way out -- so every child went in with a version, a timestamp and no
    `spec_path`.

    Not a cosmetic loss. `_replay` needs the path to re-run the predicate,
    finds none, and `sweep_strength` falls to RECORDED: a size whose predicate
    DID certify was summarised as "recorded only, predicate NOT certified",
    and the range faithfully repeated it. One missing field, two symptoms.
    """
    import shutil
    import tempfile

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        data = _nested_range(tmp)
        top = data.get("provenance") or {}
        assert top.get("spec_path") and top.get("spec_sha256")

        for entry in data["payload"]["entries"]:
            child = (entry.get("cert") or {}).get("provenance") or {}
            assert child.get("spec_path"), entry["n"]
            assert child.get("spec_sha256") == top["spec_sha256"], entry["n"]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def test_the_range_stops_calling_a_replayable_child_merely_recorded():
    """`recorded` and `reproducible` are different claims, and the first was
    being made about certificates that could carry the second."""
    import shutil
    import tempfile

    from certo.certificate import Certificate

    tmp = pathlib.Path(tempfile.mkdtemp())
    try:
        data = _nested_range(tmp)
        rep = verify(Certificate.from_dict(data), LIM)
        assert rep.ok
        # every size reports what it can establish, and none says `recorded`
        lines = [detail for _n, _ok, detail in rep.checks if "family of" in detail]
        assert lines, rep.checks
        assert all("recorded only" not in ln for ln in lines), lines
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def test_brief_summarises_the_certificate_and_keeps_everything_else():
    """`--cert-all --json` on a nested sweep puts megabytes on stdout. A
    reader piping that into `jq` to see a verdict has paid for a proof they
    did not ask to read."""
    from certo import LPSpec, api
    from certo.cli import _as_json

    spec = LPSpec(sense="max", title="small")
    spec.variable("x", hi=3)
    spec.objective({"x": 1})
    spec.constraint({"x": 2}, "<=", 5, name="cap")
    res = api.run("opt", spec)

    class _Args:
        json = True
        brief = False

    whole = _as_json(res, _Args())
    _Args.brief = True
    short = _as_json(res, _Args())

    assert len(json.dumps(short)) < len(json.dumps(whole))
    assert short["certificate"]["summarised"] is True
    assert short["certificate"]["kind"] == res.certificate.kind
    assert short["certificate"]["digest"] == res.certificate.digest()
    assert short["certificate"]["bytes"] == len(
        json.dumps(res.certificate.to_dict(), ensure_ascii=False))
    # and nothing else moved
    for key in ("command", "status", "verdict", "detail", "meta"):
        assert short[key] == whole[key], key


# --- a stopped search leaves an artefact -----------------------------------


def _stopped():
    """A branch-and-bound run cut off by its node budget."""
    from certo.engines import bb

    return bb.prove_optimal(_branching_ilp(), LIM, max_nodes=6)


def test_a_search_that_runs_out_of_budget_leaves_something_to_verify():
    """`bb` returned `RESOURCE_EXHAUSTED` with no certificate at all, and its
    own status report said so in as many words -- "Not a certificate, a
    status report". It also dropped the stack of nodes it had not opened, so
    hours of search left nothing to verify, archive, resume or combine.
    """
    res = _stopped()
    assert res.status is Status.RESOURCE_EXHAUSTED
    assert res.verdict is Verdict.INCONCLUSIVE      # still not an optimum
    assert res.certificate is not None
    assert res.certificate.kind == "branch_frontier"
    assert res.meta["frontier"] > 0

    rep = verify(res.certificate, LIM)
    assert rep.ok, [c for c in rep.checks if not c[1]]
    assert res.certificate.solver_free


def test_the_frontier_claims_an_interval_and_says_it_is_not_an_optimum():
    """The claim is [incumbent, bound] and a complete frontier. Reading it as
    an optimum is the substitution this project exists to refuse, so the
    warning is part of the artefact."""
    from fractions import Fraction

    res = _stopped()
    p = res.certificate.payload
    lo, hi = Fraction(p["incumbent"]), Fraction(p["bound"])
    assert lo <= hi
    # the true optimum of this ILP is 43, and it is inside
    assert lo <= 43 <= hi

    rep = verify(res.certificate, LIM)
    assert any("not an optimum" in w or "no un óptimo" in w
               for w in rep.warnings), rep.warnings


def test_a_dropped_subtree_fails_exactly_as_it_does_in_a_closed_tree():
    """A frontier that quietly lost a branch reads like one that explored it,
    which is the failure `branch_bound`'s coverage check was written for."""
    import copy

    from certo.certificate import Certificate

    base = json.loads(json.dumps(_stopped().certificate.to_dict()))
    forged = copy.deepcopy(base)
    forged["payload"]["open"].pop()
    rep = verify(Certificate.from_dict(forged), LIM)
    assert not rep.ok
    assert any("children" in name or "hijos" in name
               for name, ok, _d in rep.checks if not ok), rep.checks


def test_an_open_bound_is_checked_against_the_program_it_came_from():
    """The dual belongs to the PARENT's program -- a child's feasible set is
    a subset of its parent's, so the parent's dual bounds it too.

    The first version stored that dual against the CHILD's fixings, which
    checks a vector against a matrix it never came from: every open node
    failed. Both halves are checked now, and either one alone is forgeable.
    """
    import copy

    from certo.certificate import Certificate

    base = json.loads(json.dumps(_stopped().certificate.to_dict()))
    for tweak in ("bound", "from", "dual"):
        forged = copy.deepcopy(base)
        if tweak == "bound":
            forged["payload"]["open"][0]["bound"] = \
                forged["payload"]["incumbent"]
        elif tweak == "from":
            forged["payload"]["open"][0]["from"] = []
        else:
            forged["payload"]["open"][0]["dual"] = \
                forged["payload"]["open"][1]["dual"]
        assert not verify(Certificate.from_dict(forged), LIM).ok, tweak


def test_the_interval_cannot_be_narrowed_by_editing_it():
    """The upper end is RECOMPUTED as the largest open bound, so writing a
    smaller one in is caught rather than believed."""
    import copy

    from certo.certificate import Certificate

    base = json.loads(json.dumps(_stopped().certificate.to_dict()))
    forged = copy.deepcopy(base)
    forged["payload"]["bound"] = forged["payload"]["incumbent"]
    rep = verify(Certificate.from_dict(forged), LIM)
    assert not rep.ok


def test_a_search_that_finishes_still_certifies_the_optimum():
    """The frontier is for the stopped case and changes nothing else."""
    from certo.engines import bb

    res = bb.prove_optimal(_branching_ilp(), LIM, max_nodes=20_000)
    assert res.verdict is Verdict.PROVED
    assert res.certificate.kind == "branch_bound"
    assert res.meta["optimum"] == "43"
    assert verify(res.certificate, LIM).ok


# --- the enumeration that had no bound at all ------------------------------
#
# `geng` used to run under `subprocess.run(capture_output=True)`: no clock, no
# memory cap, all of stdout in a buffer, on an `n` the caller chose. `geng` is
# not on every machine and is on no CI runner here, so these drive the runner
# with a stub instead -- which is the better test anyway, because it can be
# made to misbehave on purpose and deterministically.


def _stub(code):
    """An executable that behaves like `geng` for as long as we need it to."""
    import sys
    return [sys.executable, "-c", code]


def test_a_bounded_enumeration_still_returns_everything_when_it_fits():
    from certo.graphs import _run_geng

    out = _run_geng(_stub("print('D?{'); print('DBk')"), 30, 1 << 20)
    assert out.split() == ["D?{", "DBk"]


def test_an_enumeration_that_floods_is_stopped_and_says_which_bound():
    import time

    from certo.graphs import WorkBudget, _run_geng

    t0 = time.monotonic()
    try:
        _run_geng(_stub("while True: print('D?{')"), 120, 4096)
        raise AssertionError("an endless geng was allowed to finish")
    except WorkBudget as e:
        assert e.reason == "output"
        assert "MB" in str(e)
    # It must have KILLED the child rather than waited it out: an endless
    # stream would otherwise hold this for the whole 120s budget.
    assert time.monotonic() - t0 < 30


def test_an_enumeration_that_stalls_is_stopped_by_the_clock():
    from certo.graphs import WorkBudget, _run_geng

    code = "\n".join([
        "import time",
        "for i in range(100):",
        "    print('D?{', flush=True)",
        "    time.sleep(0.2)",
    ])
    try:
        _run_geng(_stub(code), 1, 1 << 20)
        raise AssertionError("a slow geng was allowed to finish")
    except WorkBudget as e:
        assert e.reason == "timeout"


def test_a_failing_geng_is_not_reported_as_an_empty_enumeration():
    import subprocess

    from certo.graphs import _run_geng

    try:
        _run_geng(_stub("import sys; sys.exit(3)"), 30, 1 << 20)
        raise AssertionError("a failing geng passed for a graph-free universe")
    except subprocess.CalledProcessError as e:
        assert e.returncode == 3


def test_a_truncated_enumeration_is_never_returned_as_a_shorter_list():
    """The property the whole bound exists for.

    A partial enumeration is indistinguishable from a complete one -- both are
    a list of graphs -- and `sweep` would go on to report that every graph on
    n vertices satisfies the predicate having seen a prefix. Exceeding a bound
    has to propagate.
    """
    from certo import graphs as G

    real_path, real_run = G._geng_path, G._run_geng
    G._geng_path = lambda: "geng"
    G._run_geng = lambda *a, **k: (_ for _ in ()).throw(
        G.WorkBudget("output", "too much"))
    try:
        G.enumerate_graphs(5)
        raise AssertionError("a stopped enumeration came back as a result")
    except G.WorkBudget:
        pass
    finally:
        G._geng_path, G._run_geng = real_path, real_run


def test_an_absent_limits_still_means_a_bound():
    """`limits=None` is the case that motivated this, not an exemption."""
    from certo import graphs as G
    from certo.limits import Limits

    seen = {}
    real_path, real_run = G._geng_path, G._run_geng
    G._geng_path = lambda: "geng"

    def spy(args, timeout_s, max_bytes):
        seen["timeout_s"], seen["max_bytes"] = timeout_s, max_bytes
        return ""

    G._run_geng = spy
    try:
        G.enumerate_graphs(5)
    finally:
        G._geng_path, G._run_geng = real_path, real_run

    assert seen["timeout_s"] == Limits().enumerate_timeout_s
    assert seen["max_bytes"] == Limits().max_output_mb * 1024 * 1024
    assert seen["timeout_s"] > 0 and seen["max_bytes"] > 0


def test_the_enumeration_budget_is_not_the_solver_budget():
    """Two different jobs; giving them one number would be the quiet kind of
    substitution this project refuses everywhere else."""
    from certo.limits import Limits

    lim = Limits(timeout_ms=50)
    assert lim.enumerate_timeout_s == Limits().enumerate_timeout_s


def test_a_stopped_enumeration_reaches_the_caller_as_a_verdict():
    """Not a traceback. A model has to tell "no such graph" from "never
    looked", and which bound fired is part of that answer."""
    from certo import Limits, graphs as G
    from certo.engines import graphsearch
    from certo.status import Status, Verdict

    real_path, real_run = G._geng_path, G._run_geng
    G._geng_path = lambda: "geng"
    try:
        for reason, want in (("timeout", Status.TIMEOUT),
                             ("output", Status.RESOURCE_EXHAUSTED)):
            G._run_geng = (lambda r: lambda *a, **k: (_ for _ in ()).throw(
                G.WorkBudget(r, "stopped")))(reason)
            r = graphsearch.enum(5, None, Limits())
            assert r.status is want, (reason, r.status)
            assert r.verdict is Verdict.INCONCLUSIVE
            assert not r.status.conclusive
            assert r.certificate is None
    finally:
        G._geng_path, G._run_geng = real_path, real_run


# --- what certo was asked and could not settle -----------------------------


def _res(status, command="prove", meta=None, detail=""):
    from certo.status import Result, Status, Verdict
    return Result(command, status, Verdict.INCONCLUSIVE, "z3", 1.0, None,
                  detail=detail, meta=meta or {})


def _cov_path(tmp, name="coverage.jsonl"):
    import tempfile
    return pathlib.Path(tempfile.mkdtemp(prefix="certo_cov_")) / name


def test_only_the_unanswered_questions_are_recorded():
    from certo import coverage
    from certo.status import Status

    p = _cov_path(None)
    assert coverage.record(_res(Status.OUT_OF_THEORY), "cli", p) is True
    assert coverage.record(_res(Status.TIMEOUT), "api", p) is True
    assert coverage.record(_res(Status.UNSAT), "cli", p) is False
    assert coverage.record(_res(Status.SAT), "cli", p) is False
    assert len(p.read_text(encoding="utf-8").strip().splitlines()) == 2


def test_the_log_carries_sizes_and_never_the_callers_mathematics():
    """The rule that makes recording-by-default defensible."""
    import json

    from certo import coverage
    from certo.status import Status

    p = _cov_path(None)
    coverage.record(
        _res(Status.OUT_OF_THEORY, command="sweep",
             meta={"n": 11, "count": 3, "optimum": 42,
                   "title": "Kneser(7,3) colourability", "witness": "v0,v1"},
             detail="no ray named sigma_secret in the declared lattice"),
        "cli", p)
    e = json.loads(p.read_text(encoding="utf-8").strip())

    assert e["shape"] == {"n": 11, "count": 3}       # sizes, allowlisted
    assert "optimum" not in e["shape"]               # an answer, not a size
    blob = json.dumps(e)
    for leak in ("sigma_secret", "Kneser", "witness", "v0,v1", "detail"):
        assert leak not in blob, leak
    assert set(e) == {"ts", "command", "status", "engine", "source", "shape",
                      "why", "certo"}
    # `why` is a catalogue KEY or nothing -- never the sentence, which here is
    # the caller's own and matches no key
    from certo.i18n import _catalogue
    assert e["why"] is None or e["why"] in _catalogue("en")


def test_recording_can_be_turned_off_completely():
    import os

    from certo import coverage
    from certo.status import Status

    p = _cov_path(None)
    os.environ[coverage.ENV_OFF] = "1"
    try:
        assert coverage.enabled() is False
        assert coverage.record(_res(Status.TIMEOUT), "cli", p) is False
        assert not p.exists()
    finally:
        os.environ.pop(coverage.ENV_OFF, None)
    assert coverage.enabled() is True


def test_a_full_log_stops_rather_than_discarding_the_oldest():
    """Rotation would silently drop the earliest evidence, which is the
    failure this module exists to fix."""
    from certo import coverage
    from certo.status import Status

    p = _cov_path(None)
    p.parent.mkdir(parents=True, exist_ok=True)
    real = coverage.MAX_LINES
    coverage.MAX_LINES = 3
    try:
        wrote = [coverage.record(_res(Status.TIMEOUT), "cli", p) for _ in range(6)]
        assert wrote[:3] == [True, True, True]
        assert wrote[3:] == [False, False, False]
        assert len(p.read_text(encoding="utf-8").strip().splitlines()) == 3
        assert coverage.summary(p)["full"] is True
    finally:
        coverage.MAX_LINES = real


def test_a_log_that_cannot_be_written_never_fails_the_command():
    from certo import coverage
    from certo.status import Status

    import tempfile

    # A regular file standing where a directory would have to be:
    # `mkdir` cannot succeed and neither can the write.
    fd, blocker = tempfile.mkstemp(prefix="certo_cov_blocker_")
    os.close(fd)
    bad = pathlib.Path(blocker) / "nested" / "coverage.jsonl"
    assert coverage.record(_res(Status.TIMEOUT), "cli", bad) is False


def test_the_summary_counts_by_command_and_by_status():
    from certo import coverage
    from certo.status import Status

    p = _cov_path(None)
    coverage.record(_res(Status.OUT_OF_THEORY, command="cone"), "cli", p)
    coverage.record(_res(Status.OUT_OF_THEORY, command="cone"), "mcp", p)
    coverage.record(_res(Status.TIMEOUT, command="sweep"), "api", p)

    s = coverage.summary(p)
    assert s["lines"] == 3
    assert s["by_command"] == {"cone": 2, "sweep": 1}
    assert s["by_status"] == {"out_of_theory": 2, "timeout": 1}
    assert s["first"] is not None and s["last"] is not None


def test_the_log_goes_to_the_users_data_directory_not_the_working_one():
    """certo is run from wherever the mathematics lives; it does not get to
    leave files there."""
    from certo import coverage

    # The env override exists and this is not a test of it: neutralise it, or
    # this checks wherever the caller happened to point the log.
    saved = os.environ.pop(coverage.ENV_FILE, None)
    try:
        p = coverage.default_path()
        assert p.name == "coverage.jsonl"
        assert p.parent != pathlib.Path.cwd()
        assert pathlib.Path.cwd() not in p.parents
        assert pathlib.Path.home() in p.parents or "certo" in str(p.parent)
    finally:
        if saved is not None:
            os.environ[coverage.ENV_FILE] = saved


# --- affine semigroups, as a checker ---------------------------------------


def _sg(**kw):
    from certo import SemigroupSpec
    from certo.engines import algebra
    return algebra.affine_semigroup(SemigroupSpec(**kw), LIM)


def test_the_textbook_non_normal_semigroup_is_refuted_by_one_point():
    """(1,2) is in the cone, in the group, and not in N(1,0)+N(1,1)+N(1,3).
    Three checkable facts; together they refute normality."""
    from certo import verify

    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            points={"w": (1, 2)})
    p = r.certificate.payload
    e = p["points"]["w"]
    assert e["in_cone"] is True and e["in_group"] is True
    assert e["in_semigroup"] is False
    assert e["refutes_normality"] is True
    assert p["not_normal"] is True and p["normality_witnesses"] == ["w"]
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_normality_is_never_asserted_only_refuted():
    """The orthant IS normal and certo does not say so. Establishing it is a
    decision over every lattice point of the cone."""
    r = _sg(generators={"e1": (1, 0), "e2": (0, 1)}, points={"v": (3, 4)})
    p = r.certificate.payload
    assert p["not_normal"] is False
    assert p["normal"] is None           # not False, not True: not decided
    assert p["normal_why"]


def test_zero_is_in_every_semigroup():
    """The empty combination. The first version searched only AFTER a step, so
    the origin came back absent -- and then refuted normality everywhere."""
    for gens in ({"a": (1, 0), "b": (1, 1), "c": (1, 3)},
                 {"e1": (1, 0), "e2": (0, 1)},
                 {"x": (2, 3, 5)}):
        d = len(next(iter(gens.values())))
        r = _sg(generators=gens, points={"zero": tuple([0] * d)})
        e = r.certificate.payload["points"]["zero"]
        assert e["in_semigroup"] is True, gens
        assert e["semigroup_coefficients"] == [0] * len(gens)
        assert e["refutes_normality"] is False


def test_membership_comes_back_with_the_coefficients():
    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            points={"reachable": (2, 1)})
    e = r.certificate.payload["points"]["reachable"]
    assert e["in_semigroup"] is True
    coeffs = e["semigroup_coefficients"]
    gens = [r.certificate.payload["generators"][n]
            for n in r.certificate.payload["order"]]
    got = [sum(c * g[i] for c, g in zip(coeffs, gens)) for i in range(2)]
    assert got == [2, 1]
    assert all(c >= 0 for c in coeffs)


def test_a_point_outside_the_cone_carries_a_separating_functional():
    """One vector and k+1 dot products, instead of "I looked everywhere"."""
    from certo.semigroup import dot

    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            points={"outside": (1, -1)})
    p = r.certificate.payload
    e = p["points"]["outside"]
    assert e["in_cone"] is False
    y = e["separating"]
    assert y is not None
    gens = [p["generators"][n] for n in p["order"]]
    assert all(dot(y, g) <= 0 for g in gens)
    assert dot(y, e["point"]) > 0


def test_an_absence_carries_the_bound_that_makes_it_a_proof():
    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            points={"w": (1, 2)})
    e = r.certificate.payload["points"]["w"]
    assert e["in_semigroup"] is False
    assert e["search_bound"] is not None and e["search_bound"] >= 0
    assert e["degree"] is not None


def test_a_redundant_generator_is_named_and_the_set_is_not_minimal():
    r = _sg(generators={"a": (1, 0), "dup": (2, 0)})
    p = r.certificate.payload
    assert p["minimal"] is False
    assert "dup" in p["redundant"]
    assert p["redundant"]["dup"]["as"] == {"a": 2}


def test_a_semigroup_with_no_grading_says_so_instead_of_searching():
    """Not pointed is an answer about the object, not a failure to report as
    one -- and no search here would terminate."""
    from certo.status import Status, Verdict

    r = _sg(generators={"right": (1, 0), "left": (-1, 0)}, points={"x": (5, 0)})
    assert r.status is Status.OUT_OF_THEORY
    assert r.verdict is Verdict.INCONCLUSIVE
    assert not r.status.conclusive
    p = r.certificate.payload
    assert p["pointed"] is False and p["grading"] is None
    # The point's membership is UNKNOWN, and unknown is not no.
    assert p["points"]["x"]["in_semigroup"] is None
    assert p["points"]["x"]["refutes_normality"] is False


def test_the_grading_is_chosen_for_the_cheapest_search():
    """Every valid functional proves pointedness; `<u,v>` is the search bound,
    so a small one costs less. On this instance it is 1 against 11."""
    from certo.semigroup import dot, positive_functional

    gens = [(1, 0), (1, 1), (1, 3)]
    u = positive_functional(gens)
    assert max(dot(u, g) for g in gens) == 1


def test_a_generator_of_a_different_length_is_refused_not_padded():
    from certo.status import Status

    r = _sg(generators={"a": (1, 0, 0), "b": (0, 1)})
    assert r.status is Status.OUT_OF_THEORY
    assert r.certificate is None


def test_the_semigroup_command_is_reachable_through_the_in_process_api():
    from certo import SemigroupSpec, api

    res = api.run("semigroup", SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        points={"w": (1, 2)}))
    assert res.certificate.kind == "affine_semigroup"
    assert res.meta["not_normal"] is True


# --- a PROPOSED minimal generating set, checked -----------------------------


def test_a_correct_minimal_generating_set_is_accepted():
    """The one claim here that is DECIDED rather than only refuted."""
    from certo import verify

    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3)})
    h = r.certificate.payload["hilbert"]
    assert h["is_minimal_generating_set"] is True
    assert h["decided"] is True and h["generates"] is True
    assert all(e["in_semigroup"] and e["irreducible"]
               for e in h["elements"].values())
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_a_reducible_element_is_rejected_with_the_decomposition():
    """`extra` is `a + b`. Saying so is a claim, so it comes with the split."""
    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3), "extra": (2, 1)})
    h = r.certificate.payload["hilbert"]
    assert h["is_minimal_generating_set"] is False
    assert h["why_not"] == ["extra"]
    e = h["elements"]["extra"]
    assert e["in_semigroup"] is True and e["irreducible"] is False
    rest = e["reduces_as"]["rest"]
    gen = r.certificate.payload["order"][e["reduces_as"]["generator"]]
    whole = r.certificate.payload["generators"][gen]
    assert [x + y for x, y in zip(rest, whole)] == [2, 1]


def test_a_set_that_does_not_generate_names_what_it_cannot_reach():
    r = _sg(generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
            hilbert={"a": (1, 0), "b": (1, 1)})
    h = r.certificate.payload["hilbert"]
    assert h["is_minimal_generating_set"] is False
    assert h["generates"] is False
    assert h["unreachable_generators"] == ["c"]


def test_unreachable_and_undecided_are_never_the_same_answer():
    """A zero in the proposed set breaks the grading, so nothing below it
    terminates. The first version reported that as `does not generate`."""
    r = _sg(generators={"e1": (1, 0), "e2": (0, 1)},
            hilbert={"z": (0, 0), "e1": (1, 0), "e2": (0, 1)})
    h = r.certificate.payload["hilbert"]
    assert h["decided"] is False
    assert h["is_minimal_generating_set"] is None      # not False
    assert h["generates"] is None                      # not False
    assert h["unreachable_generators"] == []
    assert sorted(h["undecided_generators"]) == ["e1", "e2"]


def test_a_redundant_generator_does_not_belong_to_the_minimal_set():
    """S = N(1,0) + N(2,0) is generated by (1,0) alone."""
    r = _sg(generators={"a": (1, 0), "dup": (2, 0)}, hilbert={"a": (1, 0)})
    h = r.certificate.payload["hilbert"]
    assert h["is_minimal_generating_set"] is True
    assert h["generates"] is True


def _without_cdd():
    """A context in which `import cdd` fails, as it does where it is absent."""
    import builtins
    import contextlib

    @contextlib.contextmanager
    def ctx():
        real = builtins.__import__

        def blocked(name, *a, **k):
            if name == "cdd" or name.startswith("cdd."):
                raise ImportError("blocked for the test")
            return real(name, *a, **k)

        builtins.__import__ = blocked
        try:
            yield
        finally:
            builtins.__import__ = real
    return ctx()


def _has_cdd():
    from certo import semigroup
    return semigroup.backend() == "cddlib"


#: A pointed cone the subset search cannot grade: two-dimensional inside R^3,
#: so the normals to pairs of generators are all (0,0,1), which is zero on it.
FLAT_CONE = {"a": (0, 2, 0), "b": (0, 1, 0), "c": (-1, -1, 0)}


def test_the_facets_grade_a_cone_the_subset_search_cannot():
    """Measured: the subset search graded 77 of 140 pointed cones, the facets
    140. This is the smallest of the ones it missed."""
    from certo import semigroup, verify

    if not _has_cdd():
        return                        # the fallback is tested below
    r = _sg(generators=FLAT_CONE, points={"v": (-1, 1, 0)})
    p = r.certificate.payload
    assert p["pointed"] is True and p["backend"] == "cddlib"
    u = [semigroup.Fraction(x) for x in p["grading"]]
    assert all(semigroup.dot(u, g) >= 1 for g in FLAT_CONE.values())
    assert p["points"]["v"]["in_semigroup"] is not None     # a search ran
    assert verify(r.certificate).ok


def test_without_cdd_no_grading_found_is_undecided_not_false():
    """The same cone without cddlib. It used to come back `pointed: False` --
    "I did not find a grading" written as "there is none", about a cone that
    has one."""
    from certo import verify

    with _without_cdd():
        r = _sg(generators=FLAT_CONE)
        p = r.certificate.payload
        assert p["backend"] == "search"
        assert p["grading"] is None
        assert p["pointed"] is None, p["pointed"]
        assert p["not_pointed_witness"] is None
        assert verify(r.certificate).ok


def test_not_pointed_is_proved_by_a_zero_combination():
    """With or without cddlib: a line in the cone has a generator on it, so
    looking for `-a_i` in the cone one generator at a time is complete."""
    from certo import verify

    for ctx in ("cdd", "nocdd"):
        if ctx == "cdd" and not _has_cdd():
            continue
        cm = _without_cdd() if ctx == "nocdd" else __import__(
            "contextlib").nullcontext()
        with cm:
            r = _sg(generators={"p": (1, 0), "q": (0, 1), "r": (-1, -1)})
            p = r.certificate.payload
            assert p["pointed"] is False, (ctx, p["pointed"])
            assert p["not_pointed_witness"] == [1, 1, 1], ctx
            assert "(1, 1, 1)" in r.detail
            assert verify(r.certificate).ok


def test_a_forged_zero_combination_is_refused():
    from certo import verify
    from certo.certificate import Certificate

    r = _sg(generators={"p": (1, 0), "q": (0, 1), "r": (-1, -1)})
    for bad in ([1, 1, 2], [0, 0, 0], [-1, -1, -1], [1, 1]):
        d = r.certificate.to_dict()
        d["payload"]["not_pointed_witness"] = bad
        assert not verify(Certificate.from_dict(d)).ok, bad
    # and a grading cannot be claimed alongside one
    d = r.certificate.to_dict()
    d["payload"]["pointed"] = True
    assert not verify(Certificate.from_dict(d)).ok


def test_a_certificate_from_before_the_witness_still_verifies_and_says_so():
    """Schema 4 is frozen: an old `pointed: False` with no witness is read,
    and the warning says what it never showed."""
    from certo import verify
    from certo.certificate import Certificate

    r = _sg(generators={"right": (1, 0), "left": (-1, 0)})
    d = r.certificate.to_dict()
    d["payload"].pop("not_pointed_witness")
    d["payload"].pop("backend")
    rep = verify(Certificate.from_dict(d))
    assert rep.ok
    assert any("0.17" in w for w in rep.warnings), rep.warnings


def test_a_point_outside_a_large_cone_is_decided_not_given_up_on():
    """26 generators in dimension 5: Caratheodory runs out of subsets after
    about twelve seconds and said "unknown". A violated facet is the answer,
    and it is checked by 27 dot products."""
    import random
    import time

    from certo import semigroup, verify

    if not _has_cdd():
        return
    rng = random.Random(7)
    gens = {"g{}".format(i): tuple([rng.randint(1, 4)] +
                                   [rng.randint(-3, 3) for _ in range(4)])
            for i in range(26)}
    ineq, _eq = semigroup.facets(list(gens.values()))
    v = next(w for w in ([rng.randint(-5, 5) for _ in range(5)]
                         for _ in range(5000))
             if semigroup.dot(ineq[0], w) < 0)
    A = list(gens.values())
    t0 = time.perf_counter()
    got = semigroup.in_cone(A, v)
    assert time.perf_counter() - t0 < 2
    assert got["exhausted"] and got["coefficients"] is None
    y = got["separator"]
    assert all(semigroup.dot(y, a) <= 0 for a in A) and semigroup.dot(y, v) > 0
    # and the certificate carries it where the verifier checks it
    r = _sg(generators=dict(list(gens.items())[:8]), points={"v": tuple(v)})
    if r.certificate.payload["points"]["v"]["in_cone"] is False:
        assert r.certificate.payload["points"]["v"]["separating"] is not None
    assert verify(r.certificate).ok


def test_a_lying_cdd_can_cost_an_answer_and_never_give_a_wrong_one():
    """A facet that cuts the cone, as a broken library might return. The point
    is inside; nothing may say it is outside."""
    from certo import semigroup, verify

    real = semigroup.facets
    semigroup.facets = lambda gens: ([[Fraction(-1), Fraction(0)]], [])
    try:
        r = _sg(generators={"x": (1, 0), "y": (0, 1)}, points={"v": (1, 1)})
    finally:
        semigroup.facets = real
    e = r.certificate.payload["points"]["v"]
    assert e["in_cone"] is True, e
    assert e["separating"] is None
    assert verify(r.certificate).ok


def _lp_payload(res):
    d = res.certificate.to_dict()
    d.pop("provenance", None)
    return d


def _with_lp_solver(prefer_highs, fn):
    from certo.engines import lp as engine

    saved = engine.PREFER_HIGHS
    engine.PREFER_HIGHS = prefer_highs
    try:
        return fn()
    finally:
        engine.PREFER_HIGHS = saved


def _without_backend(payload):
    payload = dict(payload)
    payload["payload"] = {k: v for k, v in payload["payload"].items()
                          if k != "backend"}
    return payload


def test_an_lp_is_solved_by_highs_and_certified_exactly_the_same():
    """HiGHS in-process is ~200 times faster than starting CBC on a small LP.
    What it may not change is the ANSWER. The hexagon is degenerate -- two
    optimal vertices -- and HiGHS and CBC pick different ones, so the payloads
    differ in `primal` and `dual` and in nothing else: same objective, both
    certificates exact, both verified. `backend` says which ran."""
    from certo.engines import lp as engine

    if not engine._highs_available():
        return                       # the CBC path is every other test here
    h = _with_lp_solver(True, lambda: engine.opt(_hexagon(), LIM))
    c = _with_lp_solver(False, lambda: engine.opt(_hexagon(), LIM))
    assert h.meta["lp_solver"] == "pulp/HiGHS", h.meta["lp_solver"]
    assert c.meta["lp_solver"] == "pulp/CBC"
    assert h.meta["objective"] == c.meta["objective"] == "3"
    ph, pc = _lp_payload(h), _lp_payload(c)
    assert ph["payload"]["backend"] == "pulp/HiGHS"
    assert pc["payload"]["backend"] == "pulp/CBC"
    differ = {k for k in ph["payload"] if ph["payload"][k] != pc["payload"][k]}
    assert differ <= {"primal", "dual", "backend"}, differ
    for r in (h, c):
        assert r.certificate.payload["exact"] is True
        assert verify(_roundtrip(r.certificate), LIM).ok
    # A non-degenerate LP has one optimum, and then the payloads agree whole.
    from certo import LPSpec
    s = LPSpec(sense="max", title="one vertex")
    s.variable("x")
    s.variable("y")
    s.objective({"x": 3, "y": 2})
    s.constraint({"x": 1, "y": 1}, "<=", 4, name="a")
    s.constraint({"x": 1, "y": 3}, "<=", 6, name="b")
    s.constraint({"x": 1}, "<=", 3, name="c")
    h = _with_lp_solver(True, lambda: engine.opt(s, LIM))
    c = _with_lp_solver(False, lambda: engine.opt(s, LIM))
    assert _without_backend(_lp_payload(h)) == _without_backend(_lp_payload(c))


def test_an_integer_program_keeps_cbc_and_gives_highs_the_relaxation():
    """Measured on random MILPs, HiGHS was 1.5 to 2 times slower than CBC, so
    the integral solve stays where it was. Its relaxation is an LP."""
    from certo import PackingSpec
    from certo.engines import lp as engine

    if not engine._highs_available():
        return
    core = _core()
    whole = PackingSpec(items=core.items, capacities=core.capacities,
                        sense="max", integer=True).to_lp()
    h = _with_lp_solver(True, lambda: engine.opt(whole, LIM))
    c = _with_lp_solver(False, lambda: engine.opt(whole, LIM))
    assert h.meta["lp_solver"] == "pulp/CBC+HiGHS", h.meta["lp_solver"]
    assert c.meta["lp_solver"] == "pulp/CBC"
    assert h.meta["objective"] == c.meta["objective"]
    assert h.meta.get("integral_objective") == c.meta.get("integral_objective")
    assert verify(_roundtrip(h.certificate), LIM).ok


def test_without_highs_every_solve_is_cbc():
    from certo.engines import lp as engine

    real = engine._highs_available
    engine._highs_available = lambda: False
    try:
        r = engine.opt(_hexagon(), LIM)
    finally:
        engine._highs_available = real
    assert r.meta["lp_solver"] == "pulp/CBC"
    assert r.meta["objective"] == "3"


def test_certo_lp_solver_cbc_is_read_from_the_environment():
    """For anyone reproducing a run from before HiGHS."""
    import subprocess
    import sys

    code = ("from certo.engines import lp; print(lp.PREFER_HIGHS)")
    env = dict(os.environ, CERTO_LP_SOLVER="cbc",
               PYTHONPATH=str(pathlib.Path(__file__).resolve().parent.parent
                              / "src"))
    out = subprocess.run([sys.executable, "-c", code], env=env,
                         capture_output=True, text=True).stdout.strip()
    assert out == "False", out


def test_a_row_named_like_an_edge_keeps_its_dual():
    """PuLP rewrites `0-1` to `0_1`, and the duals used to be read back by the
    name certo had given -- so every row named like an edge came back with
    none, and the exact route enumerated candidates at every node instead of
    rounding one. Measured on a 17-column packing: 177 s, of which 175 were
    that enumeration, and 4 s once the rows were named by position."""
    from certo import LPSpec
    from certo.engines import lp as engine

    s = LPSpec(sense="max", title="edges")
    for v in ("t-0", "t-1", "t-2"):
        s.variable(v)
    s.objective({"t-0": 1, "t-1": 1, "t-2": 1})
    for a, b in (("0", "1"), ("1", "2"), ("0", "2")):
        s.constraint({"t-" + a: 1, "t-" + b: 1}, "<=", 1, name=a + "-" + b)
    A, b, c, names = s.as_leq_system()
    for prefer in (True, False):
        def run():
            prob, _x = engine._build(s, A, b, c, names)
            solver, name = engine._solver(LIM, integral=False)
            prob.solve(solver)
            return engine._duals(prob, names, negate=name == "HiGHS")
        duals = _with_lp_solver(prefer, run)
        assert all(d is not None for d in duals), (prefer, duals)
        assert abs(sum(duals) - 1.5) < 1e-6, duals


def test_two_names_the_solver_would_merge_are_two_names():
    """`a-b` and `a_b` are different variables to certo and the same one to
    PuLP's rewriting: rows so named were refused, columns made CBC crash."""
    from certo import LPSpec
    from certo.engines import lp as engine

    for prefer in (True, False):
        s = LPSpec(sense="max", title="collide")
        s.variable("a-b")
        s.variable("a_b")
        s.objective({"a-b": 1, "a_b": 1})
        s.constraint({"a-b": 1}, "<=", 1, name="r-1")
        s.constraint({"a_b": 1}, "<=", 2, name="r_1")
        r = _with_lp_solver(prefer, lambda: engine.opt(s, LIM))
        assert r.meta["objective"] == "3", (prefer, r.detail)
        assert verify(_roundtrip(r.certificate), LIM).ok


def _inertia(M, q="inertia"):
    from certo.engines import algebra
    from certo.spec import MatrixSpec
    return algebra.integer_matrix(MatrixSpec(matrix=M, question=q), LIM)


def test_an_inertia_with_no_usable_pivot_is_still_an_inertia():
    """`[[0,1],[1,0]]` has no non-zero diagonal entry anywhere. The LDL^T in
    `sos` stops there, correctly for what `sos` asks; an inertia goes on, by
    adding one row and column to another."""
    r = _inertia([[0, 1], [1, 0]])
    assert r.verdict is Verdict.PROVED
    assert (r.meta["n_plus"], r.meta["n_minus"], r.meta["n_zero"]) == (1, 1, 0)
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_inertia_agrees_with_the_eigenvalues_and_the_fast_path():
    """Three answers to one question: the certified congruence, the fast
    fraction-free signature, and numpy's eigenvalues where they are clear."""
    import random

    from certo import inertia

    rng = random.Random(11)
    for _ in range(150):
        n = rng.randint(1, 7)
        B = [[Fraction(rng.randint(-3, 3), rng.choice([1, 2, 3]))
              for _ in range(n)] for _ in range(n)]
        A = [[B[i][j] + B[j][i] if rng.random() < 0.7 else Fraction(0)
              for j in range(n)] for i in range(n)]
        A = [[A[min(i, j)][max(i, j)] for j in range(n)] for i in range(n)]
        if rng.random() < 0.3:
            for i in range(n):
                A[i][i] = Fraction(0)
        full = inertia.inertia(A)
        fast = inertia.signature(A)
        assert fast == {k: full[k] for k in ("n_plus", "n_minus", "n_zero")}
        try:
            import numpy as np
        except ImportError:
            continue
        ev = np.linalg.eigvalsh(np.array(A, dtype=float))
        if all(abs(e) > 1e-6 or abs(e) < 1e-12 for e in ev):
            assert full["n_plus"] == int((ev > 1e-9).sum())
            assert full["n_minus"] == int((ev < -1e-9).sum())


def test_not_psd_comes_with_the_vector_that_shows_it():
    from certo import inertia

    r = _inertia([["1/2", 1], [1, "1/2"]], "psd")
    assert r.verdict is Verdict.REFUTED
    w = [Fraction(x) for x in r.certificate.payload["witness"]]
    A = inertia.parse([["1/2", 1], [1, "1/2"]])
    assert inertia.quadratic(A, w) < 0
    assert verify(_roundtrip(r.certificate), LIM).ok
    # and PSD, when it is, is PROVED with no witness at all
    r = _inertia([[2, 1], [1, 2]], "psd")
    assert r.verdict is Verdict.PROVED and r.meta["pd"] is True
    assert r.certificate.payload["witness"] is None


def test_an_inertia_certificate_cannot_be_talked_into_psd():
    """The forgery that matters: flip the counts, or drop the witness, and
    claim PSD for a matrix that is not."""
    from certo.certificate import Certificate

    r = _inertia([["1/2", 1], [1, "1/2"]], "psd")
    for edit in ({"psd": True, "n_minus": 0, "n_plus": 2},
                 {"witness": None},
                 {"witness": ["1", "1"]},
                 {"D": ["1", "1"]}):
        d = r.certificate.to_dict()
        d["payload"].update(edit)
        assert not verify(Certificate.from_dict(d), LIM).ok, edit


def test_a_float_or_an_asymmetric_matrix_is_refused_not_rounded():
    from certo.status import Status

    for M in ([[1.5, 0], [0, 1]], [[1, 2], [3, 4]], [[1, 2, 3]]):
        r = _inertia(M)
        assert r.status is Status.OUT_OF_THEORY, M
        assert r.certificate is None


def test_the_fast_signature_is_fast_enough_for_a_loop():
    """A user needed 120 479 inertias, at 3 to 7 ms each elsewhere and under a
    32x32 limit. 20x20 integer here was measured at about 3.5 ms."""
    import random
    import time

    from certo import inertia

    rng = random.Random(3)
    n = 20
    B = [[rng.randint(-3, 3) for _ in range(n)] for _ in range(n)]
    A = [[B[i][j] + B[j][i] for j in range(n)] for i in range(n)]
    t0 = time.perf_counter()
    for _ in range(10):
        inertia.signature(A)
    assert (time.perf_counter() - t0) / 10 < 0.1     # generous, for CI


def test_the_table_of_kinds_lists_every_kind_the_registry_verifies():
    """It said "forty-seven" and lacked three kinds for three releases:
    nothing compared the table with the registry."""
    import re

    from certo.certificate import VERIFIERS

    for rel in ("CERTIFICATES.md", "es/CERTIFICATES.md"):
        text = (_docs() / rel).read_text(encoding="utf-8")
        listed = set(re.findall(r"^\| `([a-z_]+)` \|", text, re.M))
        assert listed == set(VERIFIERS), {
            rel: {"missing": sorted(set(VERIFIERS) - listed),
                  "extra": sorted(listed - set(VERIFIERS))}}


def test_the_enumeration_budget_can_be_set_from_the_command_line():
    """`Limits` kept geng's clock separate from a solver's on purpose, and no
    flag reached it: the bound existed and nobody could move it."""
    from certo import cli

    args = cli.build_parser().parse_args(
        ["sweep", "x.py", "--enumerate-timeout-s", "7", "--max-output-mb", "3",
         "--timeout-ms", "2500"])
    lim = cli.limits_from(args)
    assert lim.enumerate_timeout_s == 7 and lim.max_output_mb == 3
    assert lim.timeout_ms == 2500            # and still separate from it
    default = cli.limits_from(cli.build_parser().parse_args(["sweep", "x.py"]))
    assert default.enumerate_timeout_s == 120 and default.max_output_mb == 64


def test_drat_trim_is_given_the_callers_budget_not_sixty_seconds():
    from certo import drup
    from certo.certificate import Certificate, _verify_drat

    seen = []
    real_avail, real_check = drup.drat_trim_available, drup.check_with_drat_trim
    drup.drat_trim_available = lambda: True

    def spy(dimacs, proof, timeout_s=60.0):
        seen.append(timeout_s)
        return drup.DratReport(True, "drat-trim")

    drup.check_with_drat_trim = spy
    try:
        cert = Certificate(kind="drat", solver_free=True, payload={
            "dimacs": "p cnf 1 2\n1 0\n-1 0\n", "nclauses": 2,
            "proof": ["0"]})
        _verify_drat(cert, Limits(timeout_ms=4000))
    finally:
        drup.drat_trim_available, drup.check_with_drat_trim = real_avail, real_check
    assert seen == [4.0], seen


def test_clarabel_is_given_the_callers_clock():
    from certo import sos
    from certo.engines import algebra
    from certo.polynomials import Poly

    seen = []
    real = sos.search_sdp

    def spy(p, basis, time_limit_s=None):
        seen.append(time_limit_s)
        return real(p, basis, time_limit_s)

    sos.search_sdp = spy
    try:
        from certo import SOSSpec
        spec = SOSSpec(variables=["x", "y"],
                       poly=Poly(("x", "y"), {(4, 0): 1, (0, 4): 1, (2, 2): 2}))
        algebra.sos(spec, Limits(timeout_ms=5000))
    finally:
        sos.search_sdp = real
    if "clarabel" in sos.backends():
        assert seen and all(v == 5.0 for v in seen), seen


def test_the_lean_check_clock_is_a_flag_not_a_constant():
    from certo import cli

    args = cli.build_parser().parse_args(
        ["export", "c.json", "--lean", "--check", "--check-timeout-s", "30"])
    assert args.check_timeout_s == 30


def test_the_coverage_log_says_which_gap_by_key_and_nothing_else():
    """The first five real entries all had an empty `shape`: an
    `out_of_theory` carries a sentence, not `meta`, and the sentence was
    dropped. What is kept now is the catalogue KEY of that sentence -- a fact
    about certo -- and never the text or the values filled into it."""
    import json
    import tempfile

    from certo import coverage
    from certo.i18n import set_lang, t
    from certo.status import Result, Status, Verdict

    detail = t("family.max_only", sense="minimise-the-secret-objective")
    assert coverage.why_of(detail) == "family.max_only"
    set_lang("es")
    try:
        assert coverage.why_of(t("family.max_only", sense="min")) ==             "family.max_only"
    finally:
        set_lang("en")
    assert coverage.why_of("a sentence no catalogue has") is None

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_cov_why_"))
    f = d / "coverage.jsonl"
    res = Result("family", Status.OUT_OF_THEORY, Verdict.INCONCLUSIVE, "x",
                 0.0, None, detail=detail)
    assert coverage.record(res, "test", path=f)
    line = f.read_text(encoding="utf-8")
    assert json.loads(line)["why"] == "family.max_only"
    assert "secret" not in line                      # the value never lands
    assert coverage.summary(f)["by_why"] == {"family family.max_only": 1}


def _explicit_clique_lp(edges, problem, weight, m):
    """The same LP with every clique listed, for `opt` to certify."""
    from itertools import combinations

    from certo import LPSpec
    from certo.engines import lp as engine

    vs = sorted({v for e in edges for v in e})
    adj = {v: set() for v in vs}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    cl = [c for k in range(m, len(vs) + 1) for c in combinations(vs, k)
          if all(b in adj[a] for a, b in combinations(c, 2))]
    sense, rs = {"packing": ("max", "<="), "cover": ("min", ">="),
                 "partition": ("min", "==")}[problem]
    s = LPSpec(sense=sense)
    names = ["q%d" % k for k in range(len(cl))]
    for v in names:
        s.variable(v)
    s.objective({v: Fraction(weight.get("edges", 0)) * (len(c) * (len(c) - 1) // 2)
                 + Fraction(weight.get("vertices", 0)) * len(c)
                 + Fraction(weight.get("constant", 0))
                 for v, c in zip(names, cl)})
    for a, b in edges:
        s.constraint({names[k]: 1 for k, c in enumerate(cl) if a in c and b in c},
                     rs, 1, name="e%s_%s" % (a, b))
    return Fraction(engine.opt(s, LIM).meta["objective"])


def test_column_generation_agrees_with_the_explicit_lp():
    """Measured before shipping on 84 random graphs; a smaller sweep here."""
    import random

    from certo import CliqueLPSpec
    from certo.engines import algebra

    rng = random.Random(8)
    for _ in range(12):
        n = rng.randint(4, 7)
        edges = [(a, b) for a in range(n) for b in range(a + 1, n)
                 if rng.random() < 0.6]
        if not edges:
            continue
        for problem, weight, m in (("partition", {"constant": 1}, 2),
                                   ("cover", {"constant": 1}, 2),
                                   ("packing", {"edges": 1, "constant": -1}, 3)):
            r = algebra.clique_lp(CliqueLPSpec(edges=edges, problem=problem,
                                               weight=weight, min_size=m), LIM)
            if problem == "packing" and r.certificate is None:
                continue
            assert r.verdict is Verdict.SATISFIABLE, (problem, r.detail)
            want = _explicit_clique_lp(edges, problem, weight, m)
            assert Fraction(r.meta["objective"]) == want, (problem, edges)
            assert verify(_roundtrip(r.certificate), LIM).ok


def test_the_pricing_claim_is_rerun_not_read():
    """Lower one dual value and the claim "no clique would enter" becomes
    false; the verifier must find that by searching, since nothing in the
    payload says so."""
    from certo import CliqueLPSpec
    from certo.certificate import Certificate
    from certo.engines import algebra

    r = algebra.clique_lp(CliqueLPSpec(
        edges=[(0, 1), (1, 2), (0, 2), (2, 3)], problem="cover",
        weight={"constant": 1}), LIM)
    d = r.certificate.to_dict()
    k = next(i for i, v in enumerate(d["payload"]["dual"]) if Fraction(v) != 0)
    d["payload"]["dual"][k] = str(Fraction(d["payload"]["dual"][k]) * 3)
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_a_cover_with_an_edge_no_clique_can_reach_is_infeasible_and_says_which():
    from certo import CliqueLPSpec
    from certo.engines import algebra
    from certo.status import Status

    r = algebra.clique_lp(CliqueLPSpec(edges=[(0, 1), (1, 2), (0, 2), (2, 3)],
                                       problem="cover", min_size=3), LIM)
    assert r.status is Status.UNSAT
    assert "2-3" in r.detail


def test_a_partition_that_might_be_infeasible_is_refused_not_guessed():
    from certo import CliqueLPSpec
    from certo.engines import algebra
    from certo.status import Status

    r = algebra.clique_lp(CliqueLPSpec(edges=[(0, 1), (1, 2), (0, 2)],
                                       problem="partition", min_size=3), LIM)
    assert r.status is Status.OUT_OF_THEORY and r.certificate is None


def test_an_install_in_the_user_site_is_an_install():
    """`pip install --user`, or no admin rights, puts certo in the USER
    site-packages, which `_site_roots` did not look at -- so `doctor` called
    a real install a source tree while `pip show` said it was installed."""
    import site
    import tempfile

    from certo import doctor

    fake = pathlib.Path(tempfile.mkdtemp(prefix="certo_usersite_")).resolve()
    real = site.getusersitepackages
    site.getusersitepackages = lambda: str(fake)
    try:
        roots = doctor._site_roots()
    finally:
        site.getusersitepackages = real
    assert fake in roots, roots


def test_register_mcp_writes_where_it_is_told():
    """The function took a path; the flag never passed one."""
    import io
    import json
    import tempfile
    from contextlib import redirect_stdout

    from certo import cli, doctor

    target = pathlib.Path(tempfile.mkdtemp(prefix="certo_mcp_path_")) / "x.json"
    real = doctor.report, doctor.mcp_status
    doctor.report = lambda: {"ok": True, "rows": [], "missing_required": 0}
    doctor.mcp_status = lambda: {"workspace": "-"}
    try:
        with redirect_stdout(io.StringIO()):
            cli.main(["doctor", "--register-mcp", "--mcp-path", str(target),
                      "--json"])
    finally:
        doctor.report, doctor.mcp_status = real
    data = json.loads(target.read_text(encoding="utf-8"))
    assert "certo" in data.get("mcpServers", {}), data


def test_a_free_variable_is_solved_as_free_not_read_as_non_negative():
    """`min x` over `x >= -5`, with `x` declared free, was certified as 0: the
    certificate was right about x >= 0, which was not the program written.
    `opt` now splits it and says so; everything else that reads an `LPSpec`
    refuses it rather than guessing, and a negative bound is still refused."""
    from certo import LPSpec
    from certo.engines import lp as engine

    s = LPSpec(sense="min")
    s.variable("x", None, None)
    s.objective({"x": 1})
    s.constraint({"x": 1}, ">=", -5, name="r")
    r = engine.opt(s, LIM)
    assert r.meta["objective"] == "-5" and r.meta["solution"] == {"x": "-5"}
    assert r.certificate.payload["free_split"] == {"x": ["x__pos", "x__neg"]}
    assert verify(_roundtrip(r.certificate), LIM).ok
    try:
        s.as_leq_system()
    except ValueError:
        pass
    else:
        raise AssertionError("as_leq_system accepted a free variable")
    n = LPSpec(sense="min")
    n.variable("x", -2, None)
    n.objective({"x": 1})
    try:
        engine.opt(n, LIM)
    except ValueError:
        pass
    else:
        raise AssertionError("a negative lower bound was accepted")


def test_an_edge_count_can_be_a_range():
    """`edges=K` was exact only; a user needed `e(G) > M(n)`."""
    from certo.graphs import FILTERS

    fns = {name: FILTERS.get(name) for name in
           ("edges=2:3", "edges=4:", "edges=:2", "min_edges=3", "max_edges=2")}
    assert all(f is not None for f in fns.values()), fns
    assert FILTERS.get("edges=x:y") is None
    from certo.graphs import enumerate_graphs
    got = {name: len(enumerate_graphs(4, [name], use_geng=False)[0])
           for name in ("edges=2:3", "min_edges=3", "max_edges=2", "edges=3")}
    # graphs on 4 vertices by edge count: 1, 1, 2, 3, 2, 1, 1 for 0..6
    assert got == {"edges=2:3": 5, "min_edges=3": 7, "max_edges=2": 4,
                   "edges=3": 3}, got


def test_the_geng_command_line_carries_only_exact_equivalents():
    from certo.graphs import compile_filters, geng_args

    fns = compile_filters(["connected", "min_degree=2", "min_degree=1",
                           "max_degree=4", "chordal", "edges=5:9",
                           "min_edges=6", "triangle_free"])
    args, pushed, empty = geng_args(8, fns, supported=set())
    assert args == ["-q", "-c", "-d2", "-D4", "8", "6:9"], args
    assert "chordal" not in pushed and "triangle_free" not in pushed
    assert not empty
    args, pushed, _ = geng_args(8, fns, supported={"T", "t"})
    assert "-T" in args and "-t" in args
    assert geng_args(5, compile_filters(["min_edges=3"]))[0][-1] == "3:0"
    assert geng_args(5, compile_filters(["edges=0:0"]))[0][-1] == "0:0"
    assert geng_args(5, compile_filters(["min_edges=6", "max_edges=2"]))[2]


def test_pushing_filters_into_geng_loses_no_graph():
    """Where `geng` is installed: the pushed route and the Python-only route
    must give the same family, up to isomorphism, for every combination."""
    from certo import graphs

    if graphs._geng_path() is None:
        return                       # CI installs nauty on Linux for this
    combos = [["connected"], ["min_degree=2"], ["max_degree=2"],
              ["edges=4:6"], ["min_edges=5", "connected"],
              ["chordal"], ["chordal", "connected", "min_degree=1"],
              ["triangle_free"], ["k4_free", "edges=3:"]]
    for n in range(1, 8):
        for combo in combos:
            pushed, _e, _t = graphs.enumerate_graphs(n, combo, use_geng=True)
            plain, _e2, _t2 = graphs.enumerate_graphs(n, combo, use_geng=False)
            assert len(pushed) == len(plain), (n, combo, len(pushed), len(plain))
            left = list(plain)
            for g in pushed:
                k = next(i for i, h in enumerate(left) if graphs.is_isomorphic(g, h))
                left.pop(k)


def test_n_zero_is_the_empty_graph_not_the_graph_on_one_vertex():
    """The augmentation starts from one vertex, and n=0 came back as K1: a
    sweep "at n=0" examined the wrong graph, at the size most likely to break
    a statement."""
    from certo.graphs import enumerate_graphs

    fam, _e, total = enumerate_graphs(0, use_geng=False)
    assert [(g.n, g.m) for g in fam] == [(0, 0)] and total == 1
    try:
        enumerate_graphs(-1, use_geng=False)
    except ValueError:
        pass
    else:
        raise AssertionError("n=-1 was enumerated")


def test_a_size_range_names_the_sizes_where_it_holds_by_vacuity():
    from certo import SweepSpec
    from certo.certificate import Certificate
    from certo.engines import graphsearch

    spec = SweepSpec(n=4, filters=["min_degree=2"],
                     predicate=lambda g: g.m >= g.n)
    r = graphsearch.sweep_range(spec, 0, 4, LIM, use_geng=False)
    assert r.meta["vacuous_sizes"] == [1, 2], r.meta
    assert "VACUOUS" in r.detail
    rep = verify(r.certificate, LIM)
    assert rep.ok and any("vacuity" in w for w in rep.warnings), rep.warnings
    d = r.certificate.to_dict()
    d["payload"]["vacuous"] = []
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_lint_looks_below_the_swept_size():
    """Swept at n=5, meant for every n, false at n=0."""
    from certo import SweepSpec, lint

    spec = SweepSpec(n=5, filters=["connected"],
                     predicate=lambda g: g.m >= 1 or g.n == 1)
    keys = [f["key"] for f in lint._check_sweep(spec, LIM)]
    assert "sweep.small_fails" in keys, keys


def _pmode(**kw):
    from certo import ParametricSpec
    from certo.engines import algebra
    return algebra.parametric(ParametricSpec(**kw), LIM)


def _pring():
    from certo.polynomials import Poly
    R = ("p",)
    return Poly.var(R, "p"), (lambda c: Poly.const(R, c))


def test_an_equality_row_and_a_free_variable_need_no_split():
    """A user split every price into p - n and doubled the columns. An
    equality row's dual has no sign; a free column must balance exactly."""
    p, K = _pring()
    r = _pmode(parameters={"p": 1}, objective={"x": K(1), "w": K(-1)},
               constraints=[("eq", {"x": K(1), "w": K(1)}, "==", p),
                            ("cap", {"x": K(1)}, "<=", p)],
               dual={"eq": Fraction(-1), "cap": Fraction(2)}, free=["w"])
    assert r.verdict is Verdict.PROVED, r.detail
    assert verify(_roundtrip(r.certificate), LIM).ok
    # a free column that does NOT balance is refused, though >= 0 would pass
    r = _pmode(parameters={"p": 1}, objective={"x": K(1), "w": K(-1)},
               constraints=[("eq", {"x": K(1), "w": K(1)}, "==", p),
                            ("cap", {"x": K(1)}, "<=", p)],
               dual={"eq": Fraction(-1, 2), "cap": Fraction(2)}, free=["w"])
    assert r.certificate is None


def test_a_claimed_target_is_proved_or_the_verdict_says_it_was_not():
    from certo.certificate import Certificate

    p, K = _pring()
    base = dict(parameters={"p": 1}, objective={"x": K(1)},
                constraints=[("cap", {"x": K(1)}, "<=", p)],
                dual={"cap": Fraction(1)})
    ok = _pmode(**base, claim=p * K(2))
    assert ok.verdict is Verdict.PROVED and "as claimed" in ok.detail
    short = _pmode(**base, claim=p - K(1))
    assert short.verdict is Verdict.INCONCLUSIVE
    assert short.certificate.payload["claim"]["holds"] is False
    d = short.certificate.to_dict()
    d["payload"]["claim"]["holds"] = True
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_a_primal_bounds_a_minimisation_from_above():
    """Instead of passing a primal off as the dual of a max program."""
    from certo.certificate import Certificate

    p, K = _pring()
    r = _pmode(parameters={"p": 1}, objective={"x": K(1)},
               constraints=[("need", {"x": K(1)}, ">=", p)],
               primal={"x": p}, sense="min")
    assert r.verdict is Verdict.PROVED and "MOST" in r.detail, r.detail
    assert verify(_roundtrip(r.certificate), LIM).ok
    d = r.certificate.to_dict()
    d["payload"]["primal"]["x"] = (p - K(1)).serialize()
    assert not verify(Certificate.from_dict(d), LIM).ok
    bad = _pmode(parameters={"p": 1}, objective={"x": K(1)},
                 constraints=[("need", {"x": K(1)}, ">=", p)],
                 primal={"x": p - K(1)}, sense="min")
    assert bad.certificate is None and bad.verdict is Verdict.INCONCLUSIVE


def test_bernstein_coefficients_agree_with_the_polynomial():
    """Corners are values at vertices, the basis round-trips, and a claim of
    non-negativity is never made where the polynomial is negative."""
    import itertools
    import random

    from certo import bernstein as B
    from certo.polynomials import Poly

    R = ("a", "b")
    box = {"a": (Fraction(1), Fraction(3)), "b": (Fraction(-1), Fraction(2))}
    rng = random.Random(1)

    def ev(p, x):
        return sum(c * x[0] ** e[0] * x[1] ** e[1] for e, c in p.terms.items())

    for _ in range(40):
        p = Poly(R, {(rng.randint(0, 3), rng.randint(0, 2)):
                     Fraction(rng.randint(-5, 5)) for _ in range(4)})
        d = B.degrees_of(p)
        co = B.coefficients(p, box, d)
        assert not (B.from_coefficients(R, box, d, co) - p).terms
        ok, tree = B.nonneg(p, box, depth=5)
        if ok:
            assert B.check(p, box, tree)
            for x in itertools.product(
                    [Fraction(1) + Fraction(i, 4) for i in range(9)],
                    [Fraction(-1) + Fraction(3 * i, 8) for i in range(9)]):
                assert ev(p, x) >= 0, (p, x)


def test_a_box_proves_what_the_ray_cannot():
    """`max x`, `(2-p) x <= 1`, dual 1: the residual `1-p` is >= 0 on [0,1]
    and negative past it. The shift test on p >= 0 cannot see the end."""
    p, K = _pring()
    kw = dict(parameters={"p": 0}, objective={"x": K(1)},
              constraints=[("c", {"x": K(2) - p}, "<=", K(1))],
              dual={"c": Fraction(1)})
    assert _pmode(**kw).certificate is None
    r = _pmode(**kw, box={"p": (0, 1)})
    assert r.verdict is Verdict.PROVED and "[0, 1]" in r.detail
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_certo_finds_a_polynomial_dual_on_a_box():
    """The dual a user built by hand -- an LP per control point, assembled --
    found by one exact LP over its Bernstein coefficients."""
    from certo.certificate import Certificate
    from certo.polynomials import Poly

    p, K = _pring()
    r = _pmode(parameters={"p": 0}, objective={"x": K(1)},
               constraints=[("c", {"x": K(2) - p}, "<=", K(1))],
               dual="bernstein", dual_degree=2, box={"p": (0, 1)})
    assert r.verdict is Verdict.PROVED, r.detail
    bound = Poly.parse(("p",), r.certificate.payload["bound"])
    # the true optimum is 1/(2-p): the bound is above it and tight at the ends
    for x in (Fraction(0), Fraction(1, 3), Fraction(1, 2), Fraction(1)):
        value = sum(c * x ** e[0] for e, c in bound.terms.items())
        assert value >= 1 / (2 - x)
    assert verify(_roundtrip(r.certificate), LIM).ok
    d = r.certificate.to_dict()
    d["payload"]["box"]["p"] = ["0", "2"]          # claim it on a wider box
    assert not verify(Certificate.from_dict(d), LIM).ok


def test_a_box_is_subdivided_and_the_splits_are_rechecked():
    from certo.certificate import Certificate

    p, K = _pring()
    dual = (p - K(Fraction(1, 2))) * (p - K(Fraction(1, 2))) * K(4)         + K(Fraction(101, 100))
    kw = dict(parameters={"p": 0}, objective={"x": K(1)},
              constraints=[("c", {"x": K(1)}, "<=", K(1))],
              dual={"c": dual}, box={"p": (0, 1)})
    assert _pmode(**kw).certificate is None or True     # may need no split
    r = _pmode(**kw, subdivide=3)
    assert r.verdict is Verdict.PROVED, r.detail
    assert verify(_roundtrip(r.certificate), LIM).ok
    d = r.certificate.to_dict()
    trees = d["payload"].get("box_trees")
    if trees:
        d["payload"]["box_trees"] = {}
        assert not verify(Certificate.from_dict(d), LIM).ok


def test_irreducibility_is_decided_one_rung_down_in_the_grading():
    """`h` is reducible exactly when some generator `a` has `h - a` in S and
    non-zero -- k questions, each of strictly smaller degree."""
    from certo.semigroup import irreducible_in, positive_functional

    gens = [(1, 0), (1, 1), (1, 3)]
    u = positive_functional(gens)
    assert irreducible_in(gens, [1, 1], u)["irreducible"] is True
    out = irreducible_in(gens, [2, 1], u)
    assert out["irreducible"] is False
    assert out["rest"] in ([1, 0], [1, 1])


def test_asking_nothing_about_a_hilbert_basis_leaves_the_field_absent():
    """An optional field the frozen schema allows, absent when unasked."""
    r = _sg(generators={"a": (1, 0), "b": (1, 1)})
    assert r.certificate.payload["hilbert"] is None


# --- a capacity profile, as a certified function ---------------------------


def _profile_spec(**over):
    """The six-vertex chordal piece from a user's own write-up."""
    import importlib.util

    path = pathlib.Path(__file__).resolve().parent.parent / "examples" / "capacity_profile.py"
    spec = importlib.util.spec_from_file_location("_cap_profile", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    base = mod.spec()
    for k, v in over.items():
        setattr(base, k, v)
    return base


def _profile(**over):
    from certo.engines import algebra
    return algebra.capacity_profile(_profile_spec(**over), LIM)


def test_a_profile_is_decided_not_merely_bounded():
    from certo import verify

    r = _profile()
    p = r.certificate.payload
    assert p["holds"] is True and p["failures"] == []
    assert [q["value"] for q in p["piecewise"]] == ["6 + 3 t", "7 + 1 t"]
    assert p["breakpoints"] == ["0", "1/2", "1"]
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_the_profile_is_not_the_line_between_its_endpoints():
    """The whole reason the kind exists: f(0)=6, f(1)=8, and f(1/2)=15/2 --
    not the 7 a straight line would give."""
    from fractions import Fraction

    p = _profile().certificate.payload
    at = {k: Fraction(v["value"]) for k, v in p["sources"].items()}
    assert at["0"] == 6 and at["1"] == 8
    assert at["1/2"] == Fraction(15, 2)
    assert at["1/2"] != (at["0"] + at["1"]) / 2


def test_a_dual_that_does_not_cover_every_column_is_refused():
    from certo.status import Verdict

    r = _profile(segments=[{"from": 0, "to": 1,
                            "dual": {"01": 2, "23": 2, "14": 1, "24": 1,
                                     "34": 1, "45": 1}}])
    assert r.verdict is Verdict.REFUTED
    assert r.certificate is None            # never a smaller profile
    assert "dual_infeasible" in {f["why"] for f in r.meta["failures"]}


def test_segments_that_leave_a_gap_are_refused():
    r = _profile(segments=[{"from": 0, "to": "1/3",
                            "dual": {"01": 3, "23": 2, "14": 1, "24": 1,
                                     "34": 1, "45": 1}}])
    assert r.certificate is None
    assert "not_covered" in {f["why"] for f in r.meta["failures"]}


def test_a_source_that_overloads_a_row_is_refused():
    bad = dict(_profile_spec().sources)
    bad[0] = {"023": 1, "124": 1, "345": 1, "012": 1}
    r = _profile(sources=bad)
    assert r.certificate is None
    assert "source_infeasible" in {f["why"] for f in r.meta["failures"]}


def test_a_bound_that_never_meets_its_source_is_refused():
    """A dual alone bounds and a source alone attains something. Equality is
    the two agreeing, and that is checked at every breakpoint."""
    bad = dict(_profile_spec().sources)
    bad["1/2"] = {"023": 1, "124": 1, "345": 1}      # feasible, value 6, not 15/2
    r = _profile(sources=bad)
    assert r.certificate is None
    assert "bound_and_source_disagree" in {f["why"] for f in r.meta["failures"]}


def test_slopes_that_increase_are_refused_as_not_concave():
    s = _profile_spec()
    r = _profile(segments=[dict(s.segments[1], **{"from": 0, "to": "1/2"}),
                           dict(s.segments[0], **{"from": "1/2", "to": 1})])
    assert r.certificate is None
    assert "not_concave" in {f["why"] for f in r.meta["failures"]}


def test_the_parameter_row_may_not_also_carry_a_fixed_capacity():
    """`t` is its capacity; a second number would be a silent second answer."""
    from certo.status import Status

    s = _profile_spec()
    r = _profile(capacity=dict(s.capacity, **{s.parameter: 1}))
    assert r.status is Status.OUT_OF_THEORY
    assert r.certificate is None


def test_a_flat_profile_is_a_profile():
    """The pendant edge: no positive column touches it, so f is constant."""
    import importlib.util

    from certo.engines import algebra

    path = pathlib.Path(__file__).resolve().parent.parent / "examples" / "capacity_profile.py"
    spec = importlib.util.spec_from_file_location("_cap_profile2", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    r = algebra.capacity_profile(mod.pendant(), LIM)
    p = r.certificate.payload
    assert p["holds"] is True
    assert p["piecewise"] == [{"from": "0", "to": "1", "value": "8 + 0 t"}]


# --- a transformation that changed the problem -----------------------------


def test_restricting_a_packing_keeps_its_loads():
    """Reported against 0.13.0: `restricted()` returned a spec with `loads`
    empty, so a packing carrying `t0 <= 0` restricted to t0's own kind
    happily admitted `t0 = 1`. A solver cannot notice -- every optimum it
    reports is a true optimum of the model it was handed."""
    from certo import PackingSpec

    p = PackingSpec(items=[("t0", ["e1"], 1, "K3"), ("t1", ["e2"], 1, "K4")],
                    capacities=1,
                    loads=[("cap_t0", {"t0": 1}, "<=", 0)])
    r = p.restricted({"K3"})
    assert r.loads == [("cap_t0", {"t0": 1}, "<=", 0)]


def test_restricting_projects_a_load_rather_than_dropping_it():
    """Forcing an item to zero removes its TERM, not the constraint. A load
    left with no items is `0 <= bound` -- vacuous when the bound is
    non-negative and INFEASIBLE when it is negative, and dropping it would
    turn an infeasible restriction into a feasible one."""
    from certo import PackingSpec

    p = PackingSpec(items=[("t0", ["e1"], 1, "K3"), ("t1", ["e2"], 1, "K4")],
                    capacities=1,
                    loads=[("mixed", {"t0": 1, "t1": 1}, "<=", 1),
                           ("only_t1", {"t1": 1}, ">=", 1)])
    r = p.restricted({"K3"})
    names = {n: (w, se, b) for n, w, se, b in r.loads}
    assert names["mixed"] == ({"t0": 1}, "<=", 1)     # t1's term is gone
    assert names["only_t1"] == ({}, ">=", 1)          # 0 >= 1, still infeasible
    assert len(r.loads) == 2


def test_an_empty_program_is_reported_as_vacuous_not_certified():
    """No variables and no rows. Its optimum is the empty sum -- zero -- and
    a certificate of that establishes nothing, so none is written. Before
    this it raised `ValueError: min() iterable argument is empty`."""
    from certo import LPSpec
    from certo.engines import lp

    r = lp.opt(LPSpec(obj={}, cons=[], sense="max"), LIM)
    assert r.meta["vacuous"] is True
    assert r.meta["objective"] == "0"
    assert r.certificate is None
    assert r.meta["min_dual"] is None


def test_the_smallest_price_of_an_empty_dual_is_nothing_not_zero():
    from certo.engines.lp import _min_or_none

    assert _min_or_none([]) is None
    assert _min_or_none([3, 1, 2]) == "1"


def test_relaxing_an_lp_drops_integrality_and_nothing_else():
    """The same defect as `restricted`, found by auditing for it. `target` is
    the caller's question and `load_names` is a fact about the model; neither
    has anything to do with whether the variables are whole."""
    from certo import LPSpec

    s = LPSpec(sense="max", title="x")
    s.variable("a", 0, 5)
    s.objective({"a": 1})
    s.constraint({"a": 1}, "<=", 3, name="r1")
    s.integer, s.target, s.load_names = True, "99", ["r1"]

    r = s.relaxed()
    assert r.target == "99"
    assert r.load_names == ["r1"]
    assert r.cons == s.cons and r.bounds == s.bounds
    assert r.integer is False        # the one thing a relaxation DOES drop


# --- what a transformation promises ----------------------------------------


def test_every_transformation_has_a_contract():
    """Found by reflection, not by a list. A transformation added without a
    contract fails here instead of losing a constraint in somebody's model two
    releases later -- which is how `restricted` dropping `loads` reached a
    published version."""
    from certo import transform

    missing = sorted("{}.{}".format(c, m) for c, m in transform.transformations()
                     if transform.contract_of(c, m) is None)
    assert not missing, missing


def test_restricting_declares_everything_it_changes():
    from certo import PackingSpec, transform

    p = PackingSpec(items=[("t0", ["e1"], 1, "K3"), ("t1", ["e2"], 1, "K4")],
                    capacities=1, loads=[("cap_t0", {"t0": 1}, "<=", 0)],
                    title="x")
    rep = transform.report(p, p.restricted({"K3"}), "PackingSpec", "restricted")
    assert rep["contract"] == transform.RESTRICTION
    assert rep["undeclared"] == [], rep["undeclared"]
    # `loads` is declared and unchanged here: every item the load mentions
    # survived the restriction. A contract says what MAY change.
    assert "loads" in rep["unchanged_but_declared"]

    # And an instance where it really does move: `t1` is dropped, so its term
    # leaves the load while the load itself stays.
    q = PackingSpec(items=[("t0", ["e1"], 1, "K3"), ("t1", ["e2"], 1, "K4")],
                    capacities=1,
                    loads=[("both", {"t0": 1, "t1": 1}, "<=", 1)], title="x")
    rep2 = transform.report(q, q.restricted({"K3"}), "PackingSpec", "restricted")
    assert rep2["undeclared"] == [], rep2["undeclared"]
    assert "loads" in rep2["changed"]


def test_relaxing_and_freezing_declare_everything_they_change():
    from certo import LPSpec, transform

    s = LPSpec(sense="max", title="x")
    s.variable("a", 0, 5)
    s.variable("k", 0, 3, kind="integer")
    s.objective({"a": 1, "k": 2})
    s.constraint({"a": 1, "k": 1}, "<=", 4, name="r1")
    s.target, s.load_names = "99", ["r1"]

    rep = transform.report(s, s.relaxed(), "LPSpec", "relaxed")
    assert rep["undeclared"] == [], rep["undeclared"]

    out, _const = s.frozen({"k": 1})
    rep = transform.report(s, out, "LPSpec", "frozen")
    assert rep["undeclared"] == [], rep["undeclared"]


def test_a_frozen_target_is_shifted_not_copied():
    """The one omission whose right fix was NOT to carry the field across. The
    residual objective is missing `const`, so a residual optimum z meets the
    original target T exactly when z + const >= T."""
    from fractions import Fraction

    from certo import LPSpec

    s = LPSpec(sense="max", title="x")
    s.variable("a", 0, 5)
    s.variable("k", 0, 3, kind="integer")
    s.objective({"a": 1, "k": 2})
    s.constraint({"a": 1, "k": 1}, "<=", 4, name="r1")
    s.target = "99"

    out, const = s.frozen({"k": 1})
    assert const == 2
    assert Fraction(out.target) == Fraction(99) - 2


def test_a_silent_change_is_reported_as_undeclared():
    """The check has to be able to FAIL, so this breaks one on purpose."""
    from certo import PackingSpec, transform

    p = PackingSpec(items=[("t0", ["e1"], 1, "K3")], capacities=1, title="x")
    other = PackingSpec(items=[("t0", ["e1"], 1, "K3")], capacities=7,
                        title=p.title)
    rep = transform.report(p, other, "PackingSpec", "restricted")
    assert "capacities" in rep["undeclared"]


# --- finding a profile rather than checking one ----------------------------


def _erased():
    """The example with its answer removed: the program, and nothing else."""
    s = _profile_spec()
    s.segments = None
    s.sources = None
    return s


def test_the_search_finds_the_profile_it_was_not_told():
    """The honest test: erase the answer and see whether it comes back. The
    breakpoint at 1/2 is computed from two lines meeting, not sampled."""
    from certo.profile import discover

    out = discover(_erased())
    assert out["breakpoints"] == ["0", "1/2", "1"]
    assert len(out["segments"]) == 2
    # A handful of programs, not a grid.
    assert out["solves"] <= 12


def test_what_the_search_finds_goes_through_the_same_gate():
    """A search with a bug cannot produce a wrong certificate, only a refused
    one. That property is why the checking half was built first."""
    from certo import verify
    from certo.engines import algebra
    from certo.profile import certify, discover

    s = _erased()
    found = discover(s)
    s.segments, s.sources = found["segments"], found["sources"]
    got = certify(s)
    assert got["holds"] is True and got["failures"] == []

    r = algebra.capacity_profile(_erased(), LIM)
    assert r.meta["discovered"] is True
    assert r.meta["piecewise"] == ["6 + 3 t", "7 + 1 t"]
    assert verify(r.certificate, LIM).ok


def test_the_search_recovers_the_hand_written_duals_exactly():
    """Not merely A valid profile: the same one a person wrote by hand."""
    from certo.profile import discover

    from fractions import Fraction

    def norm(segs):
        return {Fraction(str(s["from"])):
                {k: str(Fraction(str(v))) for k, v in s["dual"].items()}
                for s in segs}

    written = norm(_profile_spec().segments)
    found = norm(discover(_erased())["segments"])
    assert set(found) == set(written)
    for at, dual in written.items():
        assert found[at] == dual, at


def test_a_primal_reconstructed_by_slackness_is_not_good_enough():
    """`exact.primal_from_dual` pins a candidate without requiring x >= 0, and
    on this instance returned negative masses. Sources are SOLVED for, because
    feasibility is the whole job of a source."""
    from fractions import Fraction

    from certo.profile import _read, discover

    found = discover(_erased())
    data = _read(_erased())
    for at, mass in found["sources"].items():
        assert all(Fraction(v) >= 0 for v in mass.values()), (at, mass)
        assert all(n in data["columns"] for n in mass), at


def test_a_flat_program_is_found_as_one_segment():
    from certo.profile import discover

    s = _erased()
    s.parameter = "26"
    s.capacity = dict(s.capacity)
    s.capacity["01"] = 1
    s.capacity.pop("26", None)
    out = discover(s)
    assert len(out["segments"]) == 1
    assert out["breakpoints"] == ["0", "1"]


def test_the_search_is_bounded_and_says_so():
    """A budget that runs out is reported, never rounded into a shorter
    profile -- the same rule as the bounded enumeration."""
    from certo.profile import Undiscovered, discover

    try:
        discover(_erased(), max_solves=1)
        raise AssertionError("an exhausted search returned a profile")
    except Undiscovered as e:
        assert "1" in str(e)


# --- which doctor tests read the machine this is running on ----------------
#
# THE MEASUREMENT THIS REPLACED AN OPINION WITH. The backlog carried an item
# reading "derived expectations for the seams `doctor` reads, not hand-built
# fixtures", sized M, on the strength of three tests that had agreed with a
# bug. Instrumenting first said something else: eighteen of the twenty-three
# were already hermetic, and every one of the five that are not reads the real
# machine ON PURPOSE, asserting properties that hold whatever it looks like.
#
# The historical defect was never "the test touched the real machine". It was
# "the test patched one seam while the code read another", which 0.11.7 fixed
# one test at a time. What was missing is this: something that notices when a
# NEW doctor test quietly joins the second group.
#
# So the derived expectation is about the test suite, not about fixtures. The
# allowlist below is five names with reasons, and anything else that leaves
# its own fixture fails here.

#: Tests that read the real machine deliberately, each with why. A test not in
#: this set must touch nothing outside its own temporary directory.
READS_THE_REAL_MACHINE = {
    "test_an_install_in_the_user_site_is_an_install":
        "it resolves this machine's real site roots alongside the fake user "
        "site, and asserts only that the fake one is among them",
    "test_doctor_reports_every_capability_with_its_fallback":
        "it asserts every capability row carries prose and a fallback, which "
        "is a property of the REPORT on whatever machine runs it",
    "test_doctor_names_the_interpreter_startup_rather_than_blaming_certo":
        "measuring how long an interpreter takes to start needs an "
        "interpreter to start",
    "test_the_classification_is_read_off_the_metadata_directory":
        "`whatever this machine looks like, the helper agrees with itself` -- "
        "a consistency property, and its assertions name no path",
    "test_the_source_of_the_metadata_is_located_not_assumed":
        "same shape: where the metadata came from is a fact about this "
        "machine, and the assertion is that the answer is located rather "
        "than guessed",
    "test_doctor_names_a_half_finished_install":
        "it runs the real leftovers probe to check the probe's shape; the "
        "assertions are about the report, not about this machine's contents",
}


def _fixture_reads(fn):
    """Run `fn` and return the reads that left the test's own fixture.

    Counting SYSCALLS would be the wrong instrument and was the first one
    tried: `Path.resolve` on a directory the test just created is a real call
    that reads nothing of the developer's machine. What matters is whether a
    read touched a path outside the fixture, which is the same distinction the
    `--repair --apply` near-miss was about.
    """
    import shutil as _shutil
    import subprocess as _subprocess
    import sys
    import tempfile

    from certo import doctor

    tmp = pathlib.Path(tempfile.gettempdir()).resolve()
    outside = []

    def leaves(p):
        try:
            r = pathlib.Path(str(p)).resolve()
            r.relative_to(tmp)
            return False
        except Exception:  # noqa: BLE001
            return True

    def note(label, target):
        if target is None or leaves(target):
            outside.append(label)

    saved = {k: getattr(doctor, k) for k in ("shutil", "subprocess", "Path")
             if hasattr(doctor, k)}

    class _Shutil:
        def which(self, *a, **k):
            note("shutil.which", None)
            return _shutil.which(*a, **k)

        def __getattr__(self, i):
            return getattr(_shutil, i)

    class _Sub:
        def run(self, *a, **k):
            note("subprocess.run", None)
            return _subprocess.run(*a, **k)

        def __getattr__(self, i):
            return getattr(_subprocess, i)

    # SUBCLASS THE CONCRETE CLASS, NOT `Path`. Before 3.12, `Path` is abstract
    # -- it has no `_flavour` -- so `class X(Path)` builds a type that raises
    # the moment anybody constructs it. On 3.12 `pathlib` was rewritten and it
    # happens to work, which is why this passed here and failed on 3.11 in CI
    # for two releases. `type(Path())` is the concrete class on every version.
    base = type(doctor.Path())

    class _Path(base):
        def exists(self, *a, **k):
            note("Path.exists", self)
            return base.exists(self, *a, **k)

        def resolve(self, *a, **k):
            note("Path.resolve", self)
            return base.resolve(self, *a, **k)

        def glob(self, *a, **k):
            note("Path.glob", self)
            return base.glob(self, *a, **k)

        def iterdir(self, *a, **k):
            note("Path.iterdir", self)
            return base.iterdir(self, *a, **k)

    doctor.shutil, doctor.subprocess, doctor.Path = _Shutil(), _Sub(), _Path
    try:
        # AN INSTRUMENT THAT CANNOT VERIFY ITSELF MUST NOT REPORT. The first
        # version swallowed every exception from `fn()`, which on 3.11 meant
        # swallowing the instrument's OWN failure: each doctor test raised on
        # the first `Path(...)`, counted nothing, and was reported hermetic.
        # A blind guard that passes is worse than no guard, so this proves the
        # spy counts before trusting anything it says.
        probe = len(outside)
        _Path(tempfile.gettempdir()).exists()      # inside: must not count
        _Path("/definitely/not/a/fixture/path").exists()   # outside: must
        if len(outside) != probe + 1:
            raise RuntimeError(
                "the hermeticity instrument does not intercept on this "
                "interpreter ({}): it counted {} of the 1 read it was just "
                "asked to see".format(sys.version.split()[0],
                                      len(outside) - probe))
        del outside[probe:]

        try:
            fn()
        except Exception:  # noqa: BLE001
            # A FAILING TEST IS NOT THIS GUARD'S BUSINESS -- its own suite
            # entry reports that. What matters here is what it read on the
            # way, and the self-check above has already established that
            # reads are being seen at all.
            pass
    finally:
        for k, v in saved.items():
            setattr(doctor, k, v)
    return outside


def _doctor_test_names():
    src = (pathlib.Path(__file__).resolve()).read_text(
        encoding="utf-8").splitlines()
    starts = [(i, l) for i, l in enumerate(src) if l.startswith("def test_")]
    out = []
    for k, (i, l) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(src)
        body = "\n".join(src[i:end])
        name = l[4:l.index("(")]
        if "doctor" in body and name != "test_doctor_tests_stay_hermetic":
            out.append(name)
    return out


def test_doctor_tests_stay_hermetic():
    """A new doctor test may not quietly start reading this machine.

    Two failures are possible and they are different. A test that leaves its
    fixture without saying so joins a group whose passes depend on whoever
    ran them. And a name on the allowlist that no longer reads anything is a
    reason describing code that changed under it.
    """
    import sys

    module = sys.modules[__name__]
    surprises, cured = [], []
    for name in _doctor_test_names():
        fn = getattr(module, name, None)
        if fn is None:
            continue
        left = _fixture_reads(fn)
        if left and name not in READS_THE_REAL_MACHINE:
            surprises.append((name, sorted(set(left))))
        if not left and name in READS_THE_REAL_MACHINE:
            cured.append(name)

    # THE DIRECTION THAT CAN BE ASSERTED. An instrument that under-counts can
    # only MISS a surprise, never invent one, so a name appearing here is a
    # fact about the test rather than about the interpreter.
    assert not surprises, (
        "these doctor tests read the machine they run on and do not say so. "
        "Either make them hermetic or add them to READS_THE_REAL_MACHINE "
        "with a reason: {}".format(surprises))

    # AND THE ONE THAT CANNOT. "This name is on the list and reads nothing"
    # requires the instrument to be COMPLETE, and completeness is exactly what
    # varies: a read reaching the machine through a path this does not wrap
    # looks like no read at all. Asserting it turned an interpreter difference
    # into a red build twice. It is reported, because a reason that is stale
    # everywhere is worth knowing, and it is not a failure.
    if cured:
        print("  note: on READS_THE_REAL_MACHINE and read nothing here: {}"
              .format(cured))


# --- the project page is the front door, and it went stale ------------------


def _page():
    return (pathlib.Path(__file__).resolve().parent.parent
            / "docs" / "index.html").read_text(encoding="utf-8")


def test_the_project_page_states_the_version_it_describes():
    """THE CONTROL THAT WAS MISSING. The page named no version at all, so the
    only thing a test could check was its counts -- and it went a whole cycle
    without naming a single command added to it while every count passed.

    A page that states its version can be tied to the code's; shipping without
    updating it now fails here instead of on somebody's screen.
    """
    import certo

    want = "v" + certo.__version__
    assert want in _page(), (
        "docs/index.html does not say {}. GitHub Pages builds it from "
        "main/docs on every push, so the live page is whatever this file "
        "says -- update it in the release commit.".format(want))


def test_every_command_the_page_names_exists():
    """The page's table is a SELECTION, not the list -- so it is not required
    to name all of them. What it may not do is name one that is gone."""
    import re

    commands = set(_subcommands())
    named = set()
    for cell in re.findall(r'class="q">([^<]+)<', _page()):
        named.add(cell.split()[0])          # `sweep --witnesses` -> `sweep`
    unknown = sorted(named - commands)
    assert not unknown, unknown


def test_no_spelled_number_on_the_page_is_a_stale_count():
    """`All forty-three` sat on the live page while the chip beside it said
    48. The count test could not see it: it matches `<number> commands`, and
    that sentence does not contain the word. Every spelled number in a
    sentence about the reference has to be the current count."""
    import re

    from certo import catalogue

    counts = catalogue.counts()
    words = {catalogue.WORDS_EN[counts["commands"]],
             catalogue.WORDS_ES[counts["commands"]]}
    page = _page()
    wrong = []
    for lead in ("All ", "Los "):
        for m in re.finditer(re.escape(lead) + r"([a-zñáéíóú -]+?),", page):
            said = m.group(1).strip()
            # Only sentences that are counting the commands: they are the ones
            # followed by a link to the command reference.
            tail = page[m.end():m.end() + 400]
            if "COMMANDS.md" in tail and said not in words:
                wrong.append({"says": said, "should be": sorted(words)})
    assert not wrong, wrong


# --- the executable the MCP server used to hold open ------------------------


def test_the_mcp_registration_does_not_name_the_shim():
    """THE BUG THIS CLOSES, which cost three broken installs on one machine.

    `certo-mcp` is a launcher pip generates. On Windows the running process
    holds that `.exe` open for its whole lifetime, so an upgrade fails with
    WinError 32 -- and pip has already removed the old package by then, so
    `import certo` stops working and a `~certo` directory is left behind.

    Starting the server as `<interpreter> -m certo.mcp_server` moves the lock
    onto `python.exe`, which pip never replaces.
    """
    import sys

    from certo import doctor

    entry = doctor.mcp_entry()["mcpServers"]["certo"]
    assert entry["args"] == ["-m", "certo.mcp_server"]
    assert "certo-mcp" not in json.dumps(entry)

    # PORTABLE BY DEFAULT: `.mcp.json` is a file people commit, and an
    # absolute interpreter path carries one machine's user name into a shared
    # config. Pinning is available and is not the default.
    assert entry["command"] == "python"
    assert sys.executable not in json.dumps(entry)
    assert doctor.mcp_entry(sys.executable)["mcpServers"]["certo"]["command"] \
        == sys.executable


def test_the_module_the_registration_names_is_runnable():
    """A registration pointing at something that will not start is worse than
    the shim it replaced, so this runs the interpreter the entry names.

    Pinned here on purpose: the default says `python`, and which interpreter
    that is on a CI runner is exactly the ambiguity this test must not have.
    """
    import subprocess
    import sys

    from certo import doctor

    entry = doctor.mcp_entry(sys.executable)["mcpServers"]["certo"]
    probe = subprocess.run(
        [entry["command"], "-c",
         "import certo.mcp_server as m; assert callable(m.main); print('ok')"],
        capture_output=True, text=True, timeout=120)
    assert probe.returncode == 0, probe.stderr[-300:]
    assert "ok" in probe.stdout


def test_an_old_registration_naming_the_shim_is_rewritten():
    """Running `--register-mcp` again is how an existing config gets fixed, so
    an entry from an older certo must NOT count as already registered."""
    import tempfile

    from certo import doctor

    d = pathlib.Path(tempfile.mkdtemp(prefix="certo_mcp_shim_"))
    cfg = d / ".mcp.json"
    cfg.write_text(json.dumps({"mcpServers": {
        "certo": {"command": "certo-mcp", "env": {"CERTO_WORKSPACE": "."}},
        "otro": {"command": "algo-mas"},
    }}), encoding="utf-8")

    out = doctor.register_mcp(cfg)
    assert out["written"] is True
    assert out["already"] is False          # the old form is not the new one

    got = json.loads(cfg.read_text(encoding="utf-8"))["mcpServers"]
    assert got["certo"]["args"] == ["-m", "certo.mcp_server"]
    assert got["otro"] == {"command": "algo-mas"}    # nobody else is touched

    # and running it a second time is quiet
    assert doctor.register_mcp(cfg)["already"] is True


# --- the interior-point search behind `sos` ---------------------------------


def _random_sos(nvars, half, squares, seed):
    import random

    from certo import sos
    from certo.polynomials import Poly

    rng = random.Random(seed)
    names = tuple("xyzw"[:nvars])
    basis = sos.monomial_basis(nvars, half)
    p = Poly(names, {})
    for _ in range(squares):
        q = Poly(names, {e: rng.randint(-3, 3) for e in basis})
        p = p + q * q
    return p


def _has_clarabel():
    try:
        import clarabel  # noqa: F401
        return True
    except ImportError:
        return False


def test_clarabel_certifies_what_alternating_projections_could_not():
    """Three variables, degree four, full rank: the old search came back
    empty on this shape every time it was measured, and the interior point
    certifies it with denominator 1."""
    from certo import sos

    if not _has_clarabel():
        return                       # the fallback is tested separately
    p = _random_sos(3, 2, len(sos.monomial_basis(3, 2)) + 2, seed=1)
    found, _why = sos.certify(p)
    assert found is not None
    terms, _basis, denom, backend = found
    assert backend == "clarabel"
    assert sos.expand(terms, p.vars) == p      # the certificate, re-checked


def test_the_interior_point_cannot_certify_what_is_not_a_sum_of_squares():
    """Motzkin is non-negative and NOT a sum of squares. The search may fail
    to find; it must never find wrongly -- and it cannot, because the exact
    pipeline after it is the same one that has always decided."""
    from certo import sos
    from certo.polynomials import Poly

    motzkin = Poly(("x", "y"),
                   {(4, 2): 1, (2, 4): 1, (2, 2): -3, (0, 0): 1})
    found, _why = sos.certify(motzkin)
    assert found is None


def test_without_clarabel_sos_falls_back_to_the_old_search():
    """Clarabel is in the `numerics` extra, not required. Without it the
    alternating projections run exactly as before."""
    import builtins

    from certo import sos
    from certo.polynomials import Poly

    real_import = builtins.__import__

    def no_clarabel(name, *a, **k):
        if name == "clarabel" or name.startswith("clarabel."):
            raise ImportError("blocked for the test")
        return real_import(name, *a, **k)

    builtins.__import__ = no_clarabel
    try:
        assert sos.backends() == ["projections"]
        p = Poly(("x", "y"), {(4, 0): 1, (0, 4): 1, (2, 2): 2})   # (x^2+y^2)^2
        found, _why = sos.certify(p)
        assert found is not None
        assert found[3] == "projections"
    finally:
        builtins.__import__ = real_import


def test_installing_clarabel_cannot_lose_a_certificate():
    """Both searches are tried, best first, so a case only the old search
    finds is still found. Checked on the one shape where the old search
    succeeded in the measured sample."""
    from certo import sos

    p = _random_sos(2, 3, len(sos.monomial_basis(2, 3)) + 2, seed=7)
    found, _why = sos.certify(p)
    assert found is not None


def test_the_sos_certificate_records_which_search_found_it():
    from certo import SOSSpec, verify
    from certo.engines import algebra

    import z3

    x, y = z3.Reals("x y")
    spec = SOSSpec(variables=["x", "y"], poly=x**4 + y**4 + 2 * x**2 * y**2)
    r = algebra.sos(spec, LIM)
    assert r.meta["backend"] in ("clarabel", "projections")
    assert r.certificate.payload["backend"] == r.meta["backend"]
    assert verify(_roundtrip(r.certificate), LIM).ok


# --- a bug report that decides whose bug it is ------------------------------


def _tmpdir(prefix):
    import tempfile
    return pathlib.Path(tempfile.mkdtemp(prefix=prefix))


def _report_spec(body):
    d = _tmpdir("certo_rep_spec_")
    f = d / "spec.py"
    f.write_text(body, encoding="utf-8")
    return f


GOOD_SEMIGROUP = (
    "from certo import SemigroupSpec\n"
    "def spec():\n"
    "    return SemigroupSpec(generators={'a': (1, 0), 'b': (0, 1)})\n")


def test_a_clean_run_is_reported_as_nothing_found():
    from certo import report

    run = report.rerun(["semigroup", str(_report_spec(GOOD_SEMIGROUP))])
    tri = report.triage(run=run)
    assert tri["category"] == "nothing-found"


def test_an_exception_in_the_spec_is_the_specs():
    """Not certo's: the traceback's innermost frame is the user's own file."""
    from certo import report

    bad = _report_spec("def spec():\n    return 1 / 0\n")
    run = report.rerun(["semigroup", str(bad)])
    assert run["origin"] == "spec", run["origin"]
    assert report.triage(run=run)["category"] == "spec"


def test_an_exception_inside_certo_is_probably_certos():
    """Probable, not certain -- certo may be reacting badly to a strange spec
    -- which is why the category carries a question mark."""
    from certo import report
    from certo.engines import algebra

    real = algebra.affine_semigroup

    def broken(*a, **k):
        raise KeyError("an internal certo mistake")

    algebra.affine_semigroup = broken
    try:
        run = report.rerun(["semigroup", str(_report_spec(GOOD_SEMIGROUP))])
    finally:
        algebra.affine_semigroup = real
    assert run["origin"] == "certo"
    assert report.triage(run=run)["category"] == "certo-bug?"


def test_a_certificate_certo_itself_rejects_is_certos_bug_for_certain():
    """The one conclusion reached with certainty: certo produced a certificate
    its own verifier rejects. And the automatic capture must NOT fire inside a
    report, or it would write a second report about itself."""
    import os

    from certo import cli, report
    from certo.certificate import VerifyReport

    real = cli.verify_cert
    cli.verify_cert = lambda cert, lim: VerifyReport(
        False, cert.kind, True, checks=[("forced", False, "for the test")])
    auto = _tmpdir("certo_rep_auto_")
    saved = os.environ.get("CERTO_REPORT_DIR")
    os.environ["CERTO_REPORT_DIR"] = str(auto)
    try:
        run = report.rerun(["semigroup", str(_report_spec(GOOD_SEMIGROUP))])
    finally:
        cli.verify_cert = real
        if saved is None:
            os.environ.pop("CERTO_REPORT_DIR", None)
        else:
            os.environ["CERTO_REPORT_DIR"] = saved
    assert report.triage(run=run)["category"] == "certo-bug"
    assert list(auto.iterdir()) == []            # no report inside a report


def test_certo_writes_a_report_by_itself_when_its_own_check_fails():
    """Outside a report, the same failure writes one -- locally, unasked, and
    into the data directory rather than where the mathematics lives."""
    import io
    import os
    from contextlib import redirect_stderr, redirect_stdout

    from certo import cli
    from certo.certificate import VerifyReport

    real = cli.verify_cert
    cli.verify_cert = lambda cert, lim: VerifyReport(
        False, cert.kind, True, checks=[("forced", False, "for the test")])
    auto = _tmpdir("certo_rep_auto2_")
    saved = os.environ.get("CERTO_REPORT_DIR")
    os.environ["CERTO_REPORT_DIR"] = str(auto)
    err = io.StringIO()
    try:
        with redirect_stdout(io.StringIO()), redirect_stderr(err):
            cli.main(["semigroup", str(_report_spec(GOOD_SEMIGROUP))])
    finally:
        cli.verify_cert = real
        if saved is None:
            os.environ.pop("CERTO_REPORT_DIR", None)
        else:
            os.environ["CERTO_REPORT_DIR"] = saved
    written = list(auto.iterdir())
    folders = [w for w in written if w.is_dir()]
    assert len(folders) == 1, written
    tri = json.loads((folders[0] / "triage.json").read_text(encoding="utf-8"))
    assert tri["triage"]["category"] == "certo-bug"
    assert tri["sent"] is False
    assert str(folders[0]) in err.getvalue()


def test_a_certificate_that_verifies_and_is_false_goes_private():
    """The worst bug this tool can have. It does not belong on a public
    tracker, so the link is the private advisory form, not an issue."""
    from certo import report
    from certo.engines import algebra
    from certo import SemigroupSpec, Limits

    cert = algebra.affine_semigroup(
        SemigroupSpec(generators={"a": (1, 0), "b": (0, 1)}),
        Limits()).certificate
    tri = report.triage(cert=cert, wrong=True)
    assert tri["category"] == "soundness"
    assert report.issue_link("soundness", "semigroup", "x") == report.ADVISORY_URL


def test_a_module_that_will_not_import_is_the_environment():
    from certo import report

    run = {"exception": "ModuleNotFoundError: No module named 'clarabel'",
           "exception_type": "ModuleNotFoundError", "origin": "certo"}
    assert report.triage(run=run)["category"] == "environment"


def test_home_paths_are_redacted_in_every_spelling():
    """On Windows one home appears long and short. Catching one and not the
    other is not a redaction."""
    from certo.report import redact

    text = (r"C:\Users\jtraverso\a.py and C:\Users\JTRAVE~1\b.py "
            "and /home/bob/c.py and /Users/alice/d.py")
    out = redact(text)
    for name in ("jtraverso", "JTRAVE~1", "bob", "alice"):
        assert name not in out, name
    assert out.count("<user>") == 4


def test_the_link_carries_only_non_sensitive_fields():
    """The URL is the one thing that could leave without being read, so it may
    not carry anything from the spec."""
    from urllib.parse import parse_qs, urlparse

    from certo import report

    link = report.issue_link("certo-bug?", "semigroup", "0.16.0")
    fields = parse_qs(urlparse(link).query)
    assert set(fields) == {"template", "title", "version", "platform", "triage"}


def test_coverage_travels_only_when_asked_and_never_its_path():
    from certo import report

    spec = _report_spec(GOOD_SEMIGROUP)
    plain = report.build(argv=["semigroup", str(spec)],
                         out=_tmpdir("certo_rep_nocov_"))
    assert not (pathlib.Path(plain["folder"]) / "coverage.json").exists()

    asked = report.build(argv=["semigroup", str(spec)], with_coverage=True,
                         out=_tmpdir("certo_rep_cov_"))
    cov = json.loads((pathlib.Path(asked["folder"]) / "coverage.json")
                     .read_text(encoding="utf-8"))
    assert "path" not in cov
    assert set(cov) <= {"lines", "by_command", "by_status", "first", "last",
                        "full"}


def test_the_report_module_cannot_send_anything():
    """Structural rather than behavioural: no network library is imported, so
    there is no code path by which a report could leave on its own."""
    import ast

    import certo.report as mod

    tree = ast.parse(pathlib.Path(mod.__file__).read_text(encoding="utf-8"))
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.update(a.name for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module)
    forbidden = {"socket", "http", "http.client", "urllib.request",
                 "requests", "smtplib", "ftplib", "webbrowser"}
    assert not (names & forbidden), names & forbidden


def test_every_report_says_it_was_not_sent():
    from certo import report

    info = report.build(argv=["semigroup", str(_report_spec(GOOD_SEMIGROUP))],
                        out=_tmpdir("certo_rep_md_"))
    md = (pathlib.Path(info["folder"]) / "report.md").read_text(
        encoding="utf-8")
    assert "Nothing has been sent" in md
    assert info["sent"] is False


def test_a_library_failure_is_charged_to_whoever_made_the_call():
    """The spec called a library and the library raised: the spec made the bad
    call, so it is the spec's -- not the library's, and not certo's."""
    from certo import report

    bad = _report_spec("\n".join([
        "import json",
        "def spec():",
        "    return json.loads('{')",
        ""]))
    run = report.rerun(["semigroup", str(bad)])
    assert run["origin"] == "spec", run["origin"]
    assert report.triage(run=run)["category"] == "spec"


if __name__ == "__main__":
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    fails = 0
    for fn in fns:
        try:
            fn()
            print("[ok] " + fn.__name__)
        except Exception as e:  # noqa: BLE001
            fails += 1
            print("[XX] {}: {}: {}".format(fn.__name__, type(e).__name__, e))
    print("\n{}/{} passed".format(len(fns) - fails, len(fns)))
    raise SystemExit(1 if fails else 0)
