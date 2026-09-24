"""Smoke tests. Run with pytest, or standalone: `python tests/test_smoke.py`."""
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
from itertools import combinations

import z3

from certo import Limits, LPSpec, Spec, SweepSpec, SynthSpec, verify
from certo.certificate import Certificate
from certo.engines import cegis, graphsearch, lp, smt
from certo.graphs import Graph, canonical_form, enumerate_graphs, is_chordal
from certo.status import Status, Verdict

LIM = Limits(timeout_ms=20_000)


def _roundtrip(cert):
    return Certificate.from_dict(json.loads(json.dumps(cert.to_dict())))


# --- prove / core ----------------------------------------------------------


def test_prove_true_statement_and_drops_noise():
    a, b, c, t = z3.Reals("a b c t")
    s = Spec()
    s.assume("a_pos", a > 0)
    s.assume("b_pos", b > 0)
    s.assume("c_pos", c > 0)
    s.assume("ruido", t == 42)
    s.claim((a + b) * (b + c) * (a + c) >= 8 * a * b * c)
    r = smt.prove(s, LIM)
    assert r.verdict is Verdict.PROVED
    assert "ruido" in r.meta["hypotheses_dropped"]
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_prove_false_statement_gives_verifiable_counterexample():
    a = z3.Real("a")
    s = Spec()
    s.assume("a_pos", a > 0)
    s.claim(a * a >= a)  # false on (0,1)
    r = smt.prove(s, LIM)
    assert r.verdict is Verdict.REFUTED
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free


# --- synth (CEGIS) ---------------------------------------------------------


def test_synth_finds_and_certifies():
    a, b, x = z3.Int("a"), z3.Int("b"), z3.Int("x")
    sp = SynthSpec(
        impl_vars=[a, b], input_vars=[x],
        impl_constraints=z3.And(a >= 0, a <= 40, b >= 0, b <= 40),
        behavior=z3.And(x >= 1, x <= 20),
        correctness=(a * x + b >= x * x),
    )
    r = cegis.synth(sp, LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["counterexamples"] >= 1
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_synth_reports_impossible_spec():
    a, x = z3.Int("a"), z3.Int("x")
    sp = SynthSpec(
        impl_vars=[a], input_vars=[x],
        impl_constraints=z3.And(a >= 0, a <= 3),
        behavior=z3.And(x >= 1, x <= 10),
        correctness=(a > x * x),  # impossible with a <= 3 and x up to 10
    )
    r = cegis.synth(sp, LIM)
    assert r.verdict is Verdict.UNSATISFIABLE
    assert r.status is Status.UNSAT


# --- opt -------------------------------------------------------------------


def test_lp_dual_certificate_is_sound_and_tamper_evident():
    n = 6
    lps = LPSpec(sense="max", title="K6")
    tris = list(combinations(range(n), 3))
    quads = list(combinations(range(n), 4))
    name = lambda p, s: p + "".join(map(str, s))  # noqa: E731
    for t in tris:
        lps.variable(name("T", t))
    for q in quads:
        lps.variable(name("Q", q))
    lps.objective({**{name("T", t): 2 for t in tris},
                   **{name("Q", q): 5 for q in quads}})
    for e in combinations(range(n), 2):
        se = set(e)
        co = {name("T", t): 1 for t in tris if se <= set(t)}
        co.update({name("Q", q): 1 for q in quads if se <= set(q)})
        lps.constraint(co, "<=", 1, name="e{}{}".format(*e))

    r = lp.opt(lps, LIM)
    # exact: 5*n*(n-1)/12 = 25/2, not 12.500000250000001
    assert r.meta["exact"] is True
    assert Fraction(r.meta["objective"]) == Fraction(5 * n * (n - 1), 12)
    assert r.meta["objective"] == "25/2"

    cert = _roundtrip(r.certificate)
    rep = verify(cert, LIM)
    assert rep.ok and rep.solver_free
    assert all(k[1] for k in rep.checks)
    cert.payload["objective"] = "13"          # tamper
    assert not verify(cert, LIM).ok           # caught


def test_lp_keeps_exact_rationals_end_to_end():
    """Exact coefficients go in and come out exact, never through a float."""
    lps = LPSpec(sense="max")
    lps.variable("x")
    lps.variable("y")
    lps.objective({"x": Fraction(7, 12), "y": "1/3"})
    lps.constraint({"x": 1, "y": 1}, "<=", Fraction(1, 2), name="cap")

    r = lp.opt(lps, LIM)
    assert r.meta["exact"] is True
    # all the weight goes to x, which pays more: (7/12)*(1/2) = 7/24
    assert Fraction(r.meta["objective"]) == Fraction(7, 24)
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free and not rep.warnings


def test_lp_float_mode_verifies_but_warns_that_it_is_not_citable():
    lps = LPSpec(sense="max")
    lps.variable("x")
    lps.objective({"x": 3})
    lps.constraint({"x": 1}, "<=", 1, name="c")

    r = lp.opt(lps, LIM, use_exact=False)
    assert r.meta["exact"] is False
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok
    assert any("FLOATING" in w for w in rep.warnings)


def test_synth_puts_the_object_in_meta_not_only_in_the_certificate():
    a, b, x = z3.Int("a"), z3.Int("b"), z3.Int("x")
    sp = SynthSpec(
        impl_vars=[a, b], input_vars=[x],
        impl_constraints=z3.And(a >= 0, a <= 40, b >= 0, b <= 40),
        behavior=z3.And(x >= 1, x <= 20),
        correctness=(a * x + b >= x * x),
    )
    r = cegis.synth(sp, LIM)
    assert set(r.meta["implementation"]) == {"a", "b"}
    assert "x >= 1" in r.meta["domain"] or "1 <= x" in r.meta["domain"]


def test_provenance_flags_a_spec_that_changed():
    import tempfile
    from pathlib import Path as _P

    a = z3.Real("a")
    s = Spec()
    s.assume("pos", a > 0)
    s.claim(a * a >= 0)

    with tempfile.TemporaryDirectory() as d:
        f = _P(d) / "s.py"
        f.write_text("original", encoding="utf-8")
        cert = smt.prove(s, LIM).certificate.stamp(f)
        assert verify(_roundtrip(cert), LIM).ok
        assert not any("has changed" in w for w in verify(cert, LIM).warnings)

        f.write_text("modificado", encoding="utf-8")
        rep = verify(_roundtrip(cert), LIM)
        assert rep.ok                                   # still valid
        assert any("has changed" in w for w in rep.warnings)   # but warns


# --- sweep with a predicate certificate -----------------------------------


def _conn5(pred):
    return SweepSpec(n=5, filters=["connected"], predicate=pred)


def test_storing_every_certificate_is_what_reaches_the_certified_level():
    """The predicate certifying each answer is not enough on its own.

    With cert_mode="failures" only the counterexample's certificate is kept,
    so the certificate carries one out of twenty-one -- and it says so. A
    certificate can only attest what it actually contains.
    """
    from certo import Outcome

    lps = LPSpec(sense="max")
    lps.variable("x")
    lps.objective({"x": 1})
    lps.constraint({"x": 1}, "<=", Fraction(1, 3), name="c")
    sub = lp.opt(lps, LIM).certificate

    def pred(g):
        return Outcome(ok=g.m < 10, cert=sub, detail="m={}".format(g.m))

    kept = graphsearch.sweep(_conn5(pred), LIM, use_geng=False)
    assert kept.verdict is Verdict.REFUTED           # K5 has 10 edges
    assert kept.meta["predicate_certified"] == 1
    assert kept.meta["predicate_uncertified"] == kept.meta["evaluations"] - 1
    assert kept.meta["level"] == "reproducible"

    everything = graphsearch.sweep(_conn5(pred), LIM, use_geng=False,
                                   cert_mode="all")
    assert everything.meta["level"] == "certified"
    assert everything.meta["predicate_uncertified"] == 0

    rep = verify(_roundtrip(everything.certificate), LIM)
    assert rep.ok and rep.solver_free
    assert not any("carry no certificate" in w for w in rep.warnings)


def test_a_bare_bool_predicate_never_reads_as_certified():
    """The P0 case: a PASSING sweep must warn exactly like a refuted one."""
    passing = graphsearch.sweep(_conn5(lambda g: g.m >= 4), LIM, use_geng=False)
    refuted = graphsearch.sweep(_conn5(lambda g: g.m < 10), LIM, use_geng=False)
    assert passing.verdict is Verdict.PROVED
    assert refuted.verdict is Verdict.REFUTED

    for r in (passing, refuted):
        assert r.meta["level"] == "reproducible"
        assert r.meta["predicate_uncertified"] == r.meta["evaluations"] > 0
        assert r.meta["banner_key"] == "scope.sweep.reproducible"
        rep = verify(_roundtrip(r.certificate), LIM)
        assert any("carry no certificate" in w for w in rep.warnings)
        assert "NOT certified" in rep.detail


def test_a_broken_predicate_no_longer_kills_the_whole_sweep():
    def pred(g):
        if g.m == 7:
            raise RuntimeError("boom")
        return True

    r = graphsearch.sweep(_conn5(pred), LIM, use_geng=False)
    assert r.verdict is Verdict.INCONCLUSIVE       # before: ERROR for everything
    assert r.meta["errors"] >= 1
    assert r.meta["examined"] == r.meta["in_family"] - r.meta["errors"]


def test_a_counterexample_refutes_even_if_other_graphs_failed():
    def pred(g):
        if g.m == 7:
            raise RuntimeError("boom")
        return g.m < 10

    r = graphsearch.sweep(_conn5(pred), LIM, use_geng=False)
    assert r.verdict is Verdict.REFUTED            # the refutation still stands
    assert r.meta["errors"] >= 1


def test_sweep_reports_the_count_before_filtering():
    r = graphsearch.sweep(_conn5(lambda g: True), LIM, use_geng=False)
    assert r.meta["enumerated"] == 34              # every graph on n=5
    assert r.meta["in_family"] == 21               # the connected ones


# --- collect / calibracion -------------------------------------------------


def test_sweep_collects_exact_statistics_and_the_argmin():
    from fractions import Fraction as F

    def densidad(g):
        return F(g.m, g.n * (g.n - 1) // 2)

    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], collect=densidad, worst="min"),
        LIM, use_geng=False)
    cal = r.meta["calibration"]
    assert cal["count"] == 21
    assert cal["min"] == "2/5" and cal["max"] == "1"      # exact, not 0.4
    assert F(cal["mean"]) == F(13, 21)
    assert cal["argbest"] == "D~{"                        # K5 is the densest
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_calibration_works_without_a_predicate():
    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], collect=lambda g: g.m), LIM,
        use_geng=False)
    assert r.verdict is Verdict.SATISFIABLE                # does not refute: it measures
    assert r.meta["calibration"]["min"] == "4"             # the tree
    assert r.meta["calibration"]["max"] == "10"            # K5


def test_tampered_statistics_are_caught():
    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], collect=lambda g: g.m), LIM,
        use_geng=False)
    cert = _roundtrip(r.certificate)
    assert verify(cert, LIM).ok
    cert.payload["stats"]["mean"] = "999"
    assert not verify(cert, LIM).ok


def test_worst_max_flips_the_ordering():
    r = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], collect=lambda g: g.m,
                  worst="max"), LIM, use_geng=False)
    assert r.meta["calibration"]["worst"][0]["value"] == "10"


# --- prove-candidate -------------------------------------------------------


def _identity_spec(universal=True):
    A, B, x = z3.Int("A"), z3.Int("B"), z3.Int("x")

    def uni(vals):
        xr = z3.Real("x")
        s = Spec()
        s.claim((xr - 1) * (xr - 2) + z3.RealVal(vals["A"]) * xr
                + z3.RealVal(vals["B"]) == xr * xr - xr)
        return s

    return SynthSpec(
        impl_vars=[A, B], input_vars=[x],
        impl_constraints=z3.And(A >= -10, A <= 10, B >= -10, B <= 10),
        behavior=z3.And(x >= 1, x <= 20),
        correctness=((x - 1) * (x - 2) + A * x + B == x * x - x),
        universal=uni if universal else None,
    )


def test_synth_then_prove_candidate_closes_the_manual_step():
    from certo.certificate import synth_proved_certificate

    sp = _identity_spec()
    r = cegis.synth(sp, LIM)
    assert r.meta["implementation"] == {"A": 2, "B": -2}

    uni = cegis.prove_candidate(sp, r.certificate.payload["implementation"], LIM)
    assert uni.verdict is Verdict.PROVED          # and now it is universal
    assert uni.meta["candidate"] == {"A": 2, "B": -2}

    combo = synth_proved_certificate(
        r.meta["implementation"], r.certificate.to_dict(), uni.certificate.to_dict())
    rep = verify(_roundtrip(combo), LIM)
    assert rep.ok and len(rep.checks) == 2


def test_prove_candidate_says_what_to_add_when_the_spec_lacks_it():
    sp = _identity_spec(universal=False)
    r = cegis.synth(sp, LIM)
    try:
        cegis.prove_candidate(sp, r.certificate.payload["implementation"], LIM)
        raise AssertionError("deberia haber pedido la obligacion universal")
    except AssertionError:
        raise
    except ValueError as e:
        assert "universal_behavior" in str(e) and "universal=" in str(e)


def test_universal_behavior_is_the_simple_path():
    a, x = z3.Int("a"), z3.Int("x")
    sp = SynthSpec(
        impl_vars=[a], input_vars=[x],
        impl_constraints=z3.And(a >= 0, a <= 5),
        behavior=z3.And(x >= 1, x <= 10),
        correctness=(a * x == x + x),          # a = 2
        universal_behavior=z3.BoolVal(True),   # vale para todo entero x
    )
    r = cegis.synth(sp, LIM)
    assert r.meta["implementation"] == {"a": 2}
    uni = cegis.prove_candidate(sp, r.certificate.payload["implementation"], LIM)
    assert uni.verdict is Verdict.PROVED


# --- grafos ----------------------------------------------------------------


def test_graph6_roundtrip_and_canonical_form():
    g = Graph.from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])
    assert Graph.from_graph6(g.to_graph6()) == g
    relabeled = g.permuted([2, 3, 4, 0, 1])
    assert canonical_form(g) == canonical_form(relabeled)


def test_enumeration_counts_match_known_sequences():
    # non-isomorphic graphs: 1, 2, 4, 11, 34, 156
    assert len(enumerate_graphs(4, use_geng=False)[0]) == 11
    assert len(enumerate_graphs(5, use_geng=False)[0]) == 34
    # connected: 1, 2, 6, 21, 112
    assert len(enumerate_graphs(5, ["connected"], use_geng=False)[0]) == 21
    # connected chordal: 1, 2, 5, 15, 58
    assert len(enumerate_graphs(5, ["chordal", "connected"], use_geng=False)[0]) == 15
    assert len(enumerate_graphs(6, ["chordal", "connected"], use_geng=False)[0]) == 58


def test_chordality_detects_the_4_cycle():
    c4 = Graph.from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    assert not is_chordal(c4)
    assert is_chordal(Graph.from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]))


def test_sweep_proves_and_refutes():
    def simplicial(g):
        return g.n == 0 or any(
            all(g.has_edge(a, b) for a, b in combinations(sorted(g.neighbors(v)), 2))
            for v in range(g.n)
        )

    ok = graphsearch.sweep(
        SweepSpec(n=5, filters=["chordal", "connected"], predicate=simplicial),
        LIM, use_geng=False)
    assert ok.verdict is Verdict.PROVED

    bad = graphsearch.sweep(
        SweepSpec(n=5, filters=["connected"], predicate=is_chordal),
        LIM, use_geng=False)
    assert bad.verdict is Verdict.REFUTED
    assert bad.meta["failures"] == 21 - 15


# --- cases: SAT + prueba DRAT ---------------------------------------------


def _ramsey(n):
    from certo import CNF, CNFSpec

    cnf = CNF(title="R33 K{}".format(n))

    def x(i, j):
        return cnf.var("e{}_{}".format(min(i, j), max(i, j)))

    for i, j in combinations(range(n), 2):
        x(i, j)
    for t in combinations(range(n), 3):
        a, b, c = x(t[0], t[1]), x(t[0], t[2]), x(t[1], t[2])
        cnf.add(-a, -b, -c)
        cnf.add(a, b, c)
    return CNFSpec(cnf=cnf)


def test_cases_unsat_emits_verified_drat_proof():
    from certo.engines import sat

    r = sat.cases(_ramsey(6), LIM)          # R(3,3) <= 6
    assert r.verdict is Verdict.PROVED and r.status is Status.UNSAT
    assert r.meta["proof_check"]["drup-python"]["ok"]
    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free       # verificable sin ningun solver


def test_cases_sat_witness_is_a_five_cycle():
    from certo.engines import sat

    r = sat.cases(_ramsey(5), LIM)          # R(3,3) > 5
    assert r.verdict is Verdict.SATISFIABLE
    red = [k for k, v in r.meta["witness"].items() if v]
    assert len(red) == 5                     # the pentagon
    assert verify(_roundtrip(r.certificate), LIM).ok


def test_drat_proof_is_tamper_evident():
    from certo.engines import sat

    cert = _roundtrip(sat.cases(_ramsey(6), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["proof"][0] = "1 2 3 4 5 0"   # a step that is not RUP
    assert not verify(cert, LIM).ok


def test_drup_checker_rejects_a_fake_proof():
    from certo import drup

    clauses = [[1, 2], [-1, 2]]              # satisfiable: there is no refutation
    assert not drup.check(clauses, ["0"]).ok


def test_cdcl_agrees_with_z3_on_random_cnfs():
    import random

    import z3

    from certo import cdcl

    rng = random.Random(7)
    for _ in range(25):
        nv = rng.randint(4, 12)
        clauses = [
            [rng.choice([1, -1]) * rng.randint(1, nv) for _ in range(3)]
            for _ in range(int(nv * 4.3))
        ]
        mine = cdcl.solve(nv, [c[:] for c in clauses]).status
        V = {v: z3.Bool("v%d" % v) for v in range(1, nv + 1)}
        s = z3.Solver()
        for c in clauses:
            s.add(z3.Or(*[V[abs(l)] if l > 0 else z3.Not(V[abs(l)]) for l in c]))
        theirs = "sat" if s.check() == z3.sat else "unsat"
        assert mine == theirs, (nv, clauses, mine, theirs)


def test_cnf_dimacs_roundtrip_and_symmetry_breaking():
    from certo import CNF
    from certo.cnf import CNF as _C
    from certo.engines import sat

    spec = _ramsey(5)
    back = _C.from_dimacs(spec.cnf.to_dimacs())
    assert [sorted(c) for c in back.clauses] == [sorted(c) for c in spec.cnf.clauses]

    # romper simetrias no puede volver insatisfacible algo satisfacible
    sym = _ramsey(5)
    sym.cnf.break_vertex_symmetry(
        lambda i, j: sym.cnf.var("e{}_{}".format(min(i, j), max(i, j))), 5)
    assert sat.cases(sym, LIM).verdict is Verdict.SATISFIABLE
    assert isinstance(CNF(), _C)


# --- shrink ----------------------------------------------------------------


def test_shrink_graph_strips_a_pendant_down_to_the_four_cycle():
    from certo.engines import shrink
    from certo.graphs import Graph, is_chordal

    spec = SweepSpec(n=7, filters=["connected"], predicate=is_chordal)
    # C4 with a pendant vertex: the pendant can be removed
    start = Graph.from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4)])
    r = shrink.shrink_graph(spec, start, LIM,
                            spec_path="examples/shrink_nonchordal.py")
    assert r.verdict is Verdict.REFUTED
    assert (r.meta["n"], r.meta["m"]) == (4, 4)          # C4
    minimal = Graph.from_graph6(r.meta["minimal"])
    assert not is_chordal(minimal) and all(minimal.degree(v) == 2 for v in range(4))


def test_shrink_is_one_minimal_not_minimum():
    """C6 is a LOCAL minimum: removing a vertex gives a path, which IS chordal.

    Documents the honest limitation of the method: 1-minimal, not minimum.
    """
    from certo.engines import shrink
    from certo.graphs import Graph, is_chordal

    spec = SweepSpec(n=7, filters=["connected"], predicate=is_chordal)
    c6 = Graph.from_edges(6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])
    r = shrink.shrink_graph(spec, c6, LIM,
                            spec_path="examples/shrink_nonchordal.py")
    assert r.meta["steps"] == 0 and r.meta["n"] == 6     # cannot be reduced
    assert verify(_roundtrip(r.certificate), LIM).ok     # and the certificate backs that


def test_shrink_graph_rejects_a_non_counterexample():
    from certo.engines import shrink
    from certo.graphs import Graph, is_chordal

    spec = SweepSpec(n=5, filters=["connected"], predicate=is_chordal)
    tree = Graph.from_edges(4, [(0, 1), (1, 2), (2, 3)])   # cordal: no vale
    assert shrink.shrink_graph(spec, tree, LIM).verdict is Verdict.ERROR


def test_mus_on_ramsey_k7_rediscovers_that_six_vertices_suffice():
    from certo.engines import shrink

    r = shrink.shrink_cnf(_ramsey(7), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["mus_clauses"] < r.meta["original_clauses"]

    cert = _roundtrip(r.certificate)
    rep = verify(cert, LIM)
    assert rep.ok and rep.solver_free          # insatisfacibilidad Y minimalidad

    names = cert.payload["var_names"]
    verts = set()
    for c in cert.payload["mus"]:
        for lit in c:
            i, j = names[abs(lit) - 1][1:].split("_")
            verts |= {int(i), int(j)}
    assert len(verts) == 6                     # R(3,3) <= 6


def test_mus_certificate_is_tamper_evident():
    from certo.engines import shrink

    cert = _roundtrip(shrink.shrink_cnf(_ramsey(6), LIM).certificate)
    assert verify(cert, LIM).ok
    cert.payload["mus"] = cert.payload["mus"][:-1]   # remove a clause
    assert not verify(cert, LIM).ok                  # the proof no longer closes


# --- bisect ----------------------------------------------------------------


def _ramsey_bisect(lo, hi):
    from certo import BisectSpec

    return BisectSpec(build=lambda n: _ramsey(n), lo=lo, hi=hi,
                      direction="min_true", integer=True)


def test_bisect_computes_ramsey_three_three():
    from certo.engines import bisect

    r = bisect.bisect(_ramsey_bisect(3, 8), LIM)
    assert r.verdict is Verdict.PROVED
    assert r.meta["threshold"] == 6 and r.meta["fails_at"] == 5

    rep = verify(_roundtrip(r.certificate), LIM)
    assert rep.ok and rep.solver_free      # DRAT at n=6, model at n=5


def test_bisect_refuses_a_bracket_that_does_not_contain_the_threshold():
    from certo.engines import bisect

    r = bisect.bisect(_ramsey_bisect(3, 4), LIM)   # K4 is still satisfiable
    assert r.verdict is Verdict.ERROR
    assert "endpoint" in r.detail


def test_bisect_finds_the_sharp_real_constant():
    import z3

    from certo import BisectSpec
    from certo.engines import bisect

    def build(c):
        a, b = z3.Reals("a b")
        s = Spec()
        s.claim((a + b) * (a + b) <= z3.RealVal(c) * (a * a + b * b))
        return s

    r = bisect.bisect(BisectSpec(build=build, lo=0.0, hi=10.0, tol=1e-6), LIM)
    assert r.verdict is Verdict.PROVED
    assert abs(r.meta["threshold"] - 2.0) < 1e-5     # the exact constant is 2
    assert verify(_roundtrip(r.certificate), LIM).ok


# --- estados ---------------------------------------------------------------


def test_six_states_are_distinguished():
    from certo.status import classify_unknown

    assert classify_unknown("timeout") is Status.TIMEOUT
    assert classify_unknown("canceled") is Status.TIMEOUT
    assert classify_unknown("max. resource limit exceeded") is Status.RESOURCE_EXHAUSTED
    assert classify_unknown("(incomplete quantifiers)") is Status.OUT_OF_THEORY
    assert classify_unknown("vete a saber") is Status.UNKNOWN_SOLVER


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
