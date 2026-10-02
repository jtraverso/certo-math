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


#: STRUCTURAL forgeries that survive and are BENIGN, per kind, by label
#: (`certo.tamper.forgeries`; `*` for any list position). Every other survivor
#: fails the kind's test, so a new hole shows up as a new label here rather
#: than in an audit. The audit of 0.20.0 is why this exists: each of its ten
#: forgeries was coherent and structural, and `probe` above could reach none.
#: Three things put a label on this list, and nothing else:
#:
#:   - the field carries no claim: provenance, `declared` (recomputed when
#:     present), names and labels, counts, the `dropped` and `sorts` of a
#:     core, the residual `rows` a parametric bound recomputes, `kinds` where
#:     no rounding reads them;
#:   - the order is not part of the claim: the edges of a graph, the parts of
#:     a cover, the factors of a Pratt tree, the pieces of an atlas;
#:   - the forgery is ANOTHER TRUE STATEMENT the same evidence proves, which
#:     `verify` rightly accepts: a constraint with dual 0 removed, a region
#:     condition the tree never used dropped, the objective emptied, an
#:     instance relabelled coherently, an empty DRAT proof for a formula unit
#:     propagation already refutes.
#:
#: Found and FIXED by this battery, so not here: a branch-and-bound tree with
#: no root or a branch missing a value; a `mixed` residual compared over its
#: own (emptied) columns, with extra rows and an unchecked `conditional`; a
#: parametric bound whose `variables` list, emptied, left every column
#: unchecked; semigroup vectors read with `zip` at the wrong length, and a
#: Hilbert entry's evidence compared with nothing; a proof's `bridges`,
#: `used`, `unused` and hypothesis labels; a core's names; polynomial
#: exponents read in a ring of the wrong size; duplicated variable names.
STRUCTURAL_BENIGN = {
    # the evaluations are the search's trace; the ends are what is checked
    'bisect': {
        '=5:coherent', 'bad_cert.provenance:dropkey',
        'bad_cert.provenance:empty', 'evaluations.*:dropkey',
        'evaluations.*:empty', 'evaluations:dup', 'evaluations:empty',
        'evaluations:reversed', 'evaluations:short',
        'good_cert.payload:dropkey', 'good_cert.provenance:dropkey',
        'good_cert.provenance:empty',
    },
    # a nested certificate's `declared`, `kinds` and provenance carry no claim
    'branch_frontier': {
        'incumbent_cert.payload.relaxation.payload.declared:dropkey',
        'incumbent_cert.payload.relaxation.payload.declared:empty',
        'incumbent_cert.payload.relaxation.payload.kinds:dropkey',
        'incumbent_cert.payload.relaxation.payload.kinds:empty',
        'incumbent_cert.payload.relaxation.provenance:dropkey',
        'incumbent_cert.payload.relaxation.provenance:empty',
        'incumbent_cert.payload.residual.payload.declared:dropkey',
        'incumbent_cert.payload.residual.payload.declared:empty',
        'incumbent_cert.payload.residual.provenance:dropkey',
        'incumbent_cert.payload.residual.provenance:empty',
        'incumbent_cert.provenance:dropkey',
        'incumbent_cert.provenance:empty', 'nodes.*.values:reversed',
        'nodes.*:dropkey', 'open:reversed', 'order:empty', 'order:reversed',
        'order:short', 'system.cons:reversed',
    },
    # the counterexamples are the loop's history; the object is re-checked on the domain
    'cegis': {
        'counterexamples.*.x:dup', 'counterexamples.*.x:empty',
        'counterexamples.*.x:reversed', 'counterexamples.*.x:short',
        'counterexamples.*:dropkey', 'counterexamples.*:empty',
        'counterexamples:dup', 'counterexamples:empty',
        'counterexamples:reversed', 'counterexamples:short',
    },
    # a core's `dropped`, `sorts` and provenance are labels; the cores are re-solved
    'core_matrix': {
        '=5:coherent', 'cores.identity.payload.dropped:dup',
        'cores.identity.payload.dropped:empty',
        'cores.identity.payload.dropped:reversed',
        'cores.identity.payload.dropped:short',
        'cores.identity.payload:dropkey', 'cores.identity.provenance:dropkey',
        'cores.identity.provenance:empty',
        'cores.ordering.payload.dropped:dup',
        'cores.ordering.payload.dropped:empty',
        'cores.ordering.payload.dropped:reversed',
        'cores.ordering.payload.dropped:short',
        'cores.ordering.payload.multipliers:empty',
        'cores.ordering.payload.sorts:dropkey',
        'cores.ordering.payload.sorts:empty',
        'cores.ordering.payload:dropkey', 'cores.ordering.provenance:dropkey',
        'cores.ordering.provenance:empty',
        'cores.positivity.payload.dropped:dup',
        'cores.positivity.payload.dropped:empty',
        'cores.positivity.payload.dropped:reversed',
        'cores.positivity.payload.dropped:short',
        'cores.positivity.payload.names:reversed',
        'cores.positivity.payload:dropkey',
        'cores.positivity.provenance:dropkey',
        'cores.positivity.provenance:empty', 'cores:dropkey', 'cores:empty',
        'goals:dup', 'goals:empty', 'goals:reversed', 'goals:short',
        'hypotheses:dup', 'hypotheses:empty', 'hypotheses:reversed',
        'hypotheses:short',
    },
    # `classes` are declared (and said to be), `cycle` names the chain
    'dependency_cycle': {
        '=-2:coherent', 'classes.delta:dropkey', 'classes.delta:empty',
        'classes.k:dropkey', 'classes.k:empty', 'classes.rho:dropkey',
        'classes.rho:empty', 'classes:dropkey', 'classes:empty', 'cycle:dup',
        'cycle:empty', 'cycle:reversed', 'cycle:short', 'steps:dup',
    },
    # a column bound `[0, None]` emptied is the default bound
    'equitable_quotient': {
        'bounds.k3_002001:empty', 'bounds.k3_002010:empty',
        'bounds.k3_002100:empty', 'bounds.k3_003000:empty',
        'bounds.k3_011010:empty', 'bounds.k3_011100:empty',
        'bounds.k3_012000:empty', 'bounds.k3_020010:empty',
        'bounds.k3_020100:empty', 'bounds.k3_021000:empty',
        'bounds.k3_030000:empty', 'bounds.k3_101001:empty',
        'bounds.k3_101100:empty', 'bounds.k3_102000:empty',
        'bounds.k3_110100:empty', 'bounds.k3_111000:empty',
        'bounds.k3_120000:empty', 'bounds.k3_200001:empty',
        'bounds.k3_200100:empty', 'bounds.k3_201000:empty',
        'bounds.k3_210000:empty', 'bounds.k4_003001:empty',
        'bounds.k4_003010:empty', 'bounds.k4_003100:empty',
        'bounds.k4_004000:empty', 'bounds.k4_012010:empty',
        'bounds.k4_012100:empty', 'bounds.k4_013000:empty',
        'bounds.k4_021010:empty', 'bounds.k4_021100:empty',
        'bounds.k4_022000:empty', 'bounds.k4_030010:empty',
        'bounds.k4_030100:empty', 'bounds.k4_031000:empty',
        'bounds.k4_040000:empty', 'bounds.k4_102001:empty',
        'bounds.k4_102100:empty', 'bounds.k4_103000:empty',
        'bounds.k4_111100:empty', 'bounds.k4_112000:empty',
        'bounds.k4_120100:empty', 'bounds.k4_121000:empty',
        'bounds.k4_130000:empty', 'bounds.k4_201001:empty',
        'bounds.k4_201100:empty', 'bounds.k4_202000:empty',
        'bounds.k4_210100:empty', 'bounds.k4_211000:empty',
        'bounds.k4_220000:empty', 'bounds:dropkey', 'bounds:empty',
        'column_classes.k3_002001:reversed',
        'column_classes.k3_002010:reversed',
        'column_classes.k3_002100:reversed',
        'column_classes.k3_003000:reversed',
        'column_classes.k3_011010:reversed',
        'column_classes.k3_011100:reversed',
        'column_classes.k3_012000:reversed',
    },
    # the order of a range is not its content
    'family_extremum': {
        'bounds.*.*:reversed', 'bounds:reversed',
    },
    # the ray is about the system the payload states; names are labels
    'farkas_ray': {
        '=1/2:coherent', 'A:reversed', 'b:reversed', 'names:dup',
        'names:empty', 'names:reversed', 'names:short',
    },
    # a half's `declared`, `kinds` and provenance carry no claim
    'gap': {
        'fractional.payload.declared:dropkey',
        'fractional.payload.declared:empty',
        'fractional.payload.kinds:dropkey', 'fractional.payload.kinds:empty',
        'fractional.provenance:dropkey', 'fractional.provenance:empty',
    },
    # fewer filters is a weaker claim about the same graphs
    'graph_set': {
        'filters:dup', 'filters:empty', 'filters:short', 'graph6:reversed',
    },
    # the counts are recomputed; the order of rows is not content
    'hypothesis_audit': {
        'counts:dropkey', 'rows:reversed',
    },
    # a link is checked by entailment, which re-proves the statement itself
    'induction': {
        'base.*.cert.payload.multipliers:empty',
        'base.*.cert.payload.multipliers:short',
        'base.*.cert.payload:dropkey', 'base.*.cert.provenance:dropkey',
        'base.*.cert.provenance:empty', 'base.*.cert<->base.*.cert:swap',
        'base.*.cert<->step:swap', 'base.*:dropkey',
        'step.payload.dropped:dup', 'step.payload.dropped:empty',
        'step.payload.dropped:reversed', 'step.payload.dropped:short',
        'step.payload:dropkey', 'step.provenance:dropkey',
        'step.provenance:empty',
    },
    # the fingerprint recipe is prose
    'integer_matrix': {
        'fingerprint_recipe:dropkey', 'fingerprint_recipe:empty',
    },
    # the spec record and a source's labels carry no claim
    'lean_binding': {
        'source.payload.dropped:dup', 'source.payload.dropped:empty',
        'source.payload.dropped:short', 'source.payload:dropkey',
        'source.provenance:dropkey', 'spec:dropkey', 'spec:empty',
    },
    # the order of a clause's literals
    'mus': {
        'mus.*:reversed',
    },
    # an orbit's `members` is a sample of at most five, for reading
    'orbit_witnesses': {
        'sweep.payload.counts:dropkey', 'sweep.payload.counts:empty',
        'sweep.payload.entries.*:dropkey', 'sweep.payload.entries.*:empty',
        'sweep.payload.entries:dup', 'sweep.payload.entries:empty',
        'sweep.payload.entries:reversed', 'sweep.payload.entries:short',
        'sweep.payload.orbits.*.members:dup',
        'sweep.payload.orbits.*.members:empty',
        'sweep.payload.orbits.*.members:reversed',
        'sweep.payload.orbits.*.members:short',
        'sweep.payload.orbits.*:dropkey', 'sweep.payload.orbits:reversed',
        'sweep.payload:dropkey', 'sweep.provenance:dropkey',
        'sweep.provenance:empty',
        'witnesses.*.cert.payload.blocked.*:dropkey',
        'witnesses.*.cert.payload.blocked.*:empty',
        'witnesses.*.cert.payload.blocked:dup',
        'witnesses.*.cert.payload.blocked:empty',
        'witnesses.*.cert.payload.blocked:reversed',
        'witnesses.*.cert.payload.blocked:short',
        'witnesses.*.cert.payload:dropkey', 'witnesses:dup',
        'witnesses:empty', 'witnesses:reversed', 'witnesses:short',
    },
    # a point's order, and a point's own labels
    'parametric_symmetry': {
        'points.*:dropkey', 'points:reversed',
    },
    # a coherent rewrite of an index the trace records
    'shrink_domain': {
        '=1:coherent',
    },
    # the blocked moves are recomputed; fewer filters is a weaker claim
    'shrink_graph': {
        'blocked.*:dropkey', 'blocked.*:empty', 'blocked:reversed',
        'filters:dup', 'filters:empty', 'filters:short',
    },
    # a size's sweep: counts, statistics and order carry no claim
    'sweep_range': {
        '=0:coherent', '=11:coherent', 'entries.*.cert.note_args:dropkey',
        'entries.*.cert.note_args:empty',
        'entries.*.cert.payload.counts:dropkey',
        'entries.*.cert.payload.counts:empty',
        'entries.*.cert.payload.family_graph6:reversed',
        'entries.*.cert.payload.stats:dropkey',
        'entries.*.cert.payload.stats:empty',
        'entries.*.cert.payload.values.*:dropkey',
        'entries.*.cert.payload.values:empty',
        'entries.*.cert.payload.values:reversed',
        'entries.*.cert.payload.values:short',
        'entries.*.cert.payload:dropkey', 'entries.*.cert.provenance:dropkey',
        'entries.*.cert.provenance:empty',
        'entries.*.cert<->entries.*.cert:swap', 'entries:reversed',
    },
    # a partial permutation is another symmetry, and the quotient follows it
    'symmetry_reduction': {
        'generators.swap01:dropkey', 'orbits.*:reversed',
        'quotient.cons.*:dup', 'quotient.kinds:dropkey',
        'quotient.kinds:empty', 'quotient.var_names:dup', 'system.cons:dup',
        'system.cons:reversed',
    },
    # the counterexamples are history; the universal proof is re-tied
    'synth_proved': {
        '=3:coherent', '=5:coherent', 'synth.payload.counterexamples.*.x:dup',
        'synth.payload.counterexamples.*.x:empty',
        'synth.payload.counterexamples.*.x:reversed',
        'synth.payload.counterexamples.*.x:short',
        'synth.payload.counterexamples.*:dropkey',
        'synth.payload.counterexamples.*:empty',
        'synth.payload.counterexamples:dup',
        'synth.payload.counterexamples:empty',
        'synth.payload.counterexamples:reversed',
        'synth.payload.counterexamples:short', 'synth.provenance:dropkey',
        'synth.provenance:empty', 'universal.payload:dropkey',
        'universal.provenance:dropkey', 'universal.provenance:empty',
    },
    # `used` lists are labels; a row with multiplier 0 does not matter
    'variable_range': {
        'lower.used:dup', 'lower.used:empty', 'lower.used:short',
        'rows.*.coeffs:dropkey', 'rows.*.coeffs:empty', 'rows.*:dropkey',
        'rows:dup', 'rows:reversed', 'upper.used:dup', 'upper.used:empty',
        'upper.used:short', 'variables:empty', 'variables:reversed',
        'variables:short',
    },
    # an edge list is a set of unordered pairs: order and repeats say nothing
    'pinned_value': {
        'edges.*:reversed', 'edges:dup', 'edges:reversed',
        'lower.payload.columns.*.clique:reversed', 'lower.payload.columns:reversed',
        'lower.payload.edges.*:reversed', 'lower.payload.edges:dup',
        'lower.payload.edges:reversed',
    },
    'affine_semigroup': {
        'points.outside:dropkey', 'points.reachable:dropkey',
        'points.w.group_coefficients:negative', 'points:dropkey',
    },
    'asymptotic': {
        '=2:coherent', 'collected.*:dropkey', 'collected.*:empty',
        'collected:dup', 'collected:empty', 'collected:short',
        'laurent.*.monomial:empty', 'laurent.*.monomial:reversed',
        'laurent:dup', 'terms.*:dropkey', 'terms.*:empty', 'terms:dup',
        'terms:empty', 'terms:short',
    },
    'branch_bound': {
        'incumbent_cert.payload.relaxation.payload.declared:dropkey',
        'incumbent_cert.payload.relaxation.payload.declared:empty',
        'incumbent_cert.payload.relaxation.payload.kinds:dropkey',
        'incumbent_cert.payload.relaxation.payload.kinds:empty',
        'incumbent_cert.payload.relaxation.provenance:dropkey',
        'incumbent_cert.payload.relaxation.provenance:empty',
        'incumbent_cert.payload.residual.payload.declared:dropkey',
        'incumbent_cert.payload.residual.payload.declared:empty',
        'incumbent_cert.payload.residual.provenance:dropkey',
        'incumbent_cert.payload.residual.provenance:empty',
        'incumbent_cert.provenance:dropkey',
        'incumbent_cert.provenance:empty', 'nodes.*.values:reversed',
        'nodes.*:dropkey', 'nodes:reversed',
    },
    'capacity_profile': {
        'columns.*:dropkey', 'segments:reversed',
    },
    'clique_lp': {
        '=3:coherent', '=5:coherent', 'columns.*.clique:reversed',
        'columns:reversed', 'edges.*:reversed', 'edges:dup', 'edges:reversed',
        'pricing:dropkey', 'vertices:reversed',
    },
    'cnf_model': {
        'true_vars:dup',
    },
    'domain_sweep': {
        '=0:coherent', '=16:coherent', 'counts:dropkey', 'counts:empty',
        'ids:reversed',
    },
    'drat': {
        'proof:dup', 'proof:empty', 'proof:short',
    },
    'exact_cover': {
        'part_report.*.vertices:reversed', 'parts.*.*:reversed',
        'parts.*:reversed', 'universe.*:reversed', 'universe:reversed',
    },
    'farkas': {
        'multipliers:dup', 'rows:dup', 'rows:reversed', 'sorts:dropkey',
        'sorts:empty',
    },
    'first_moment': {
        'terms:reversed',
    },
    'ideal': {
        'variables:reversed',
    },
    'integer_peak': {
        '=1/2:coherent',
    },
    'lp_dual': {
        # with cuts: a bound row reversed is another true program (binaries
        # need no bound row); a cut's variable order is not its content; and
        # with `cuts` dropped the row is one more constraint of the program
        # the payload states -- true of THAT program, and claimed of no other
        'A.*:reversed', 'cuts.*.vars:reversed', 'cuts:empty', 'cuts:short',
        # another optimal integral point, by symmetry of the instance
        'integral_point:reversed',
        '=3:coherent', 'declared:dropkey', 'declared:empty', 'kinds:dropkey',
        'kinds:empty', 'names:dup', 'names:empty', 'names:short',
        'primal:reversed', 'var_names:empty', 'var_names:reversed',
        'var_names:short',
    },
    'mixed_design': {
        '=5:coherent', 'relaxation.payload.declared:dropkey',
        'relaxation.payload.declared:empty',
        'relaxation.payload.kinds:dropkey', 'relaxation.payload.kinds:empty',
        'relaxation.provenance:dropkey', 'relaxation.provenance:empty',
        'residual.payload.declared:dropkey',
        'residual.payload.declared:empty', 'residual.payload.kinds:dropkey',
        'residual.payload.kinds:empty', 'residual.provenance:dropkey',
        'residual.provenance:empty',
    },
    'number': {
        'tree.factors.*.cert.factors.*.cert.factors.*.cert.factors:dup',
        'tree.factors.*.cert.factors.*.cert.factors:dup',
        'tree.factors.*.cert.factors.*.cert.factors:reversed',
        'tree.factors.*.cert.factors:dup',
        'tree.factors.*.cert.factors:reversed', 'tree.factors:dup',
        'tree.factors:reversed',
    },
    'parametric_atlas': {
        'pieces.*.cert.payload.rows.*.negative:dup',
        'pieces.*.cert.payload.rows.*.negative:empty',
        'pieces.*.cert.payload.rows.*.negative:short',
        'pieces.*.cert.payload.rows.*.residual:dropkey',
        'pieces.*.cert.payload.rows.*.residual:empty',
        'pieces.*.cert.payload.rows.*.shifted:dropkey',
        'pieces.*.cert.payload.rows.*.shifted:empty',
        'pieces.*.cert.payload.rows.*:dropkey',
        'pieces.*.cert.payload.rows.*:empty',
        'pieces.*.cert.payload.rows:dup', 'pieces.*.cert.payload.rows:empty',
        'pieces.*.cert.payload.rows:short',
        'pieces.*.cert.provenance:dropkey', 'pieces.*.cert.provenance:empty',
        'pieces:dup', 'pieces:reversed',
    },
    'parametric_bound': {
        '=1/2:coherent', '=3:coherent', 'constraints.*.*.a:dropkey',
        'constraints.*.*.a:empty', 'constraints.*.*.b:dropkey',
        'constraints.*.*.b:empty', 'constraints.*.*.c:dropkey',
        'constraints.*.*.c:empty', 'constraints.*.*.e:dropkey',
        'constraints.*.*.e:empty', 'constraints.*.*.x:dropkey',
        'constraints.*.*.x:empty', 'constraints.*.*.y:dropkey',
        'constraints.*.*.y:empty', 'constraints.*.*:dropkey',
        'constraints.*.*:empty', 'constraints:dup', 'constraints:reversed',
        'constraints:short', 'dual_poly:dropkey', 'objective.a:dropkey',
        'objective.a:empty', 'objective.b:dropkey', 'objective.b:empty',
        'objective.e:dropkey', 'objective.x:dropkey', 'objective.y:dropkey',
        'objective:dropkey', 'objective:empty', 'region.r_within:dropkey',
        'rows.*.residual:dropkey', 'rows.*.residual:empty',
        'rows.*.shifted:dropkey', 'rows.*.shifted:empty', 'rows.*:dropkey',
        'rows.*:empty', 'rows:dup', 'rows:empty', 'rows:reversed',
        'rows:short', 'variables:reversed',
    },
    'polynomial_nonneg': {
        '=-1:coherent', 'poly:empty', 'region.r:dropkey', 'tree.deg:beyond',
        'tree.deg:dup',
    },
    'proof': {
        '=5:coherent', 'lemmas.*.cert.payload.multipliers:empty',
        'lemmas.*.cert.payload.sorts:dropkey',
        'lemmas.*.cert.payload.sorts:empty', 'lemmas.*.cert.payload:dropkey',
        'lemmas.*.cert.provenance:dropkey', 'lemmas.*.cert.provenance:empty',
        'lemmas.*:dropkey', 'lemmas:reversed', 'step.payload.dropped:dup',
        'step.payload.dropped:empty', 'step.payload.dropped:reversed',
        'step.payload.dropped:short', 'step.payload.multipliers:empty',
        'step.payload.sorts:dropkey', 'step.payload.sorts:empty',
        'step.payload:dropkey', 'step.provenance:dropkey',
        'step.provenance:empty', 'used:dup', 'used:reversed',
    },
    'resultant': {
        'lead_f:dropkey', 'lead_f:empty', 'lead_g:dropkey', 'lead_g:empty',
    },
    'sweep': {
        '=0:coherent', '=11:coherent', 'counts:dropkey', 'counts:empty',
        'family_graph6:reversed',
    },
    'symmetric_inertia': {
        'witness:reversed',
    },
    'unsat_core': {
        'multipliers:empty', 'sorts:dropkey', 'sorts:empty',
    },
}


def probe(cert, skip=()):
    """Mutate each payload field in turn. Returns {field: caught}.

    The suite wants a flat verdict per field; `certo.tamper.probe` reports
    lists so a person can read it. Same run, different shape. The STRUCTURAL
    forgeries run beside it, and any survivor not recorded as benign above
    fails here, by label.
    """
    out = _probe(cert, LIM, skip=skip)
    assert out["original_ok"], "the original must pass"
    from certo.tamper import _general, probe_structural

    st = probe_structural(cert, LIM)
    benign = STRUCTURAL_BENIGN.get(st["kind"], set())
    new = sorted({lab for lab in st["survived"]
                  if lab not in benign and _general(lab) not in benign})
    assert not new, ("{}: structural forgeries {} were accepted. Either a "
                     "check is missing, or the forgery is benign and belongs "
                     "in STRUCTURAL_BENIGN with its reason.".format(
                         st["kind"], ", ".join(new[:6])))
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


def test_lp_dual_rounded():
    """`opt --round`: the integer bound rides on `lp_dual` as `rounded`, and
    is recomputed from the dual bound and the objective's integrality."""
    from certo import LPSpec
    from certo.engines import lp

    s = LPSpec(sense="max")
    s.variable("x", 0, None, kind="integer")
    s.variable("y", 0, None, kind="integer")
    s.objective({"x": 2, "y": 3})
    s.constraint({"x": 2, "y": 2}, "<=", 5, name="cap")
    cert = lp.opt(s, LIM, round=True).certificate
    assert cert.payload["rounded"] == {"bound": "7"}
    _report("lp_dual (rounded)", probe(cert))
    # a continuous variable in the objective makes rounding invalid
    forged = Certificate.from_dict(json.loads(json.dumps(cert.to_dict())))
    forged.payload["kinds"]["y"] = "continuous"
    assert not verify(forged, LIM).ok


def test_lp_dual_with_clique_cuts():
    """`opt --cuts clique`: every cut re-derived from the rows that force its
    pairs; one nothing forces would be a constraint added to lower a bound."""
    from itertools import combinations

    from certo import LPSpec
    from certo.engines import lp

    s = LPSpec(sense="max")
    for i in range(4):
        s.variable("x%d" % i, 0, 1, kind="binary")
    s.objective({"x%d" % i: 1 for i in range(4)})
    for i, j in combinations(range(4), 2):
        s.constraint({"x%d" % i: 1, "x%d" % j: 1}, "<=", 1, name="c%d%d" % (i, j))
    s.constraint({"x%d" % i: 1 for i in range(4)}, "<=", 3, name="loose")
    cert = lp.opt(s, LIM, round=True, cuts="clique").certificate
    assert cert.payload["rounded"] == {"bound": "1"}
    # `cuts` is skipped by name: with one cut, `mutate` empties the list, and
    # the row then stands as a constraint of the program the payload states
    # (see STRUCTURAL_BENIGN). The forgeries below are the ones that matter.
    _report("lp_dual (cuts)", probe(cert, skip=("cuts",)))
    d = json.loads(json.dumps(cert.to_dict()))
    first = next(iter(d["payload"]["cuts"][0]["why"]))
    d["payload"]["cuts"][0]["why"][first] = "loose"      # forces nothing
    _refused(Certificate.from_dict(d))
    d = json.loads(json.dumps(cert.to_dict()))
    d["payload"]["kinds"]["x0"] = "continuous"           # 1/2 + 1/2 is fine
    _refused(Certificate.from_dict(d))


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


def test_parametric_atlas():
    """One statement from several certificates: every field -- a piece's box,
    the domain, the region, the claim, the program, the covering tally -- has
    to change a check, embedded pieces included."""
    import importlib.util
    import pathlib as _p

    from certo.engines import algebra

    path = _p.Path(__file__).resolve().parent.parent / "examples" / "parametric_atlas.py"
    spec = importlib.util.spec_from_file_location("_adv_atlas", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    cert = algebra.atlas(mod.spec(), LIM).certificate
    _report("parametric_atlas", probe(cert))


def test_polynomial_nonneg():
    from fractions import Fraction as F

    from certo import NonnegSpec
    from certo.engines import algebra
    from certo.polynomials import Poly

    x = Poly.var(("x",), "x")
    proved = algebra.nonneg(NonnegSpec(
        poly=F(3, 10) - x, box={"x": (0, F(1, 2))},
        region=[("r", F(3, 40) - x ** 2)]), LIM).certificate
    # `poly` IS the statement, and `mutate` adds 1 to a coefficient: here a
    # weaker statement, still true on the box, which the tree still proves.
    # Excusing the field everywhere would excuse `sos` too, where it is
    # caught; so it is skipped here, and a polynomial made FALSE is tried below.
    _report("polynomial_nonneg", probe(proved, skip=("poly",)))
    forged = Certificate.from_dict(json.loads(json.dumps(proved.to_dict())))
    forged.payload["poly"] = (F(1, 4) - x).serialize()   # < 0 near sqrt(3/40)
    assert not verify(forged, LIM).ok
    refuted = algebra.nonneg(NonnegSpec(
        poly=x ** 3 - x + F(1, 4), box={"x": (0, 1)}), LIM).certificate
    assert refuted.payload["holds"] is False
    _report("polynomial_nonneg (refuted)", probe(refuted))


def test_pinned_value():
    """`pin`: both halves tied to ONE graph and ONE quantity before their
    numbers are compared -- the lesson of the 0.20.0 audit, built in."""
    from itertools import combinations

    from certo import CoverSpec, PinSpec
    from certo.engines import algebra
    from certo.spec import CliqueLPSpec

    E = list(combinations(range(7), 2))
    fano = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1),
            (6, 0, 2)]

    def make(edges=E, lower_max=3, upper_edges=E, upper_parts=fano):
        return algebra.pin(PinSpec(
            edges=edges, max_size=3,
            upper=CoverSpec(universe=upper_edges, parts=upper_parts,
                            cliques=True, max_size=3),
            lower=CliqueLPSpec(edges=E, problem="partition",
                               weight={"constant": 1}, max_size=lower_max)), LIM)

    r = make()
    assert r.verdict.value == "proved" and r.meta["value"] == 7
    _report("pinned_value", probe(r.certificate))
    # an LP that allows only edges has a LARGER optimum, and bounds nothing
    # about triangles: refused by name, not compared
    assert make(lower_max=2).certificate is None
    # a cover of another graph
    K6 = list(combinations(range(6), 2))
    assert make(upper_edges=K6, upper_parts=[tuple(e) for e in K6]).certificate is None
    # the bounds, edited
    d = json.loads(json.dumps(r.certificate.to_dict()))
    d["payload"]["bounds"]["lower"] = "8"
    _refused(Certificate.from_dict(d))


def test_clique_lp_bounded_and_infeasible():
    """The two shapes 0.19 adds: a family bounded above by `max_size`, and an
    infeasible partition carried by a Farkas vector and its pricing."""
    from certo import CliqueLPSpec
    from certo.engines import algebra

    k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    cert = algebra.clique_lp(CliqueLPSpec(edges=k4, problem="packing",
                                          weight={"edges": 1}, max_size=3),
                             LIM).certificate
    _report("clique_lp (max_size)", probe(cert))
    cert = algebra.clique_lp(CliqueLPSpec(
        edges=[(0, 1), (0, 2), (1, 2), (0, 3), (1, 3)], problem="partition",
        min_size=3), LIM).certificate
    _report("clique_lp (farkas)", probe(cert))


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


def _chain(cite):
    """A composed proof: a derived lemma, a hypothesis the final step does
    not use, and one more link -- assumed, or cited with a source."""
    import z3

    from certo.engines import compose
    from certo.spec import ProofSpec, Spec

    V, G, b, s = z3.Reals("V G b s")
    p = ProofSpec(title="chain")
    lem = Spec(title="V <= G")
    lem.assume("h", V <= G - 1)
    lem.claim(V <= G)
    p.lemma("VG", proves=lem)
    p.assume("VG_premise", V <= G - 1)
    if cite:
        p.cite("sec16", states=G <= b * s, source="Section 16")
    else:
        p.assume("sec16_h", G <= b * s)
    p.assume("pos", s >= 0)
    p.conclude(V <= b * s)
    return compose.compose(p, LIM).certificate


def test_proof():
    """The kind was not in this suite, and its first run found a hole: a
    hypothesis the final step does not name could lose its name while its
    formula still went into the step."""
    _report("proof", probe(_chain(cite=False)))
    _report("proof (cited)", probe(_chain(cite=True)))


# ---------------------------------------------------------------------------
# certificates written by hand, not mutated: the external audit of 0.20.0
# ---------------------------------------------------------------------------
#
# Mutating one field of a valid certificate cannot find a sub-certificate that
# verifies but is about something else, nor an empty list the verifier walks
# over without complaint. The audit wrote such certificates from scratch; each
# one below verified in 0.20.0 and states something false.


def _refused(cert):
    rep = verify(cert, LIM)
    assert not rep.ok, [c for c in rep.checks]
    return rep


def test_a_prime_tree_is_about_the_factors_it_names():
    """CM-03: 9 'prime', its one factor q=8 carried a certificate of 2."""
    _refused(Certificate("number", True, {
        "n": 9, "question": "prime", "tree": {"n": 9, "witness": 8, "factors": [
            {"q": 8, "cert": {"n": 2, "base_case": True}}]}}))
    _refused(Certificate("number", True, {
        "n": 9, "question": "factor", "tree": {"n": 9, "factors": [
            {"p": 9, "e": 1, "cert": {"n": 2, "base_case": True}}]}}))


def test_a_global_optimum_is_the_relaxation_it_carries():
    """CM-04: editing `bound`, `globally_optimal` and `level` made a design
    worth 1 globally optimal where 3 is attainable."""
    from certo import LPSpec, api

    s = LPSpec(sense="max")
    s.variable("x", kind="binary")
    s.variable("y", hi=1)
    s.objective({"x": 2, "y": 1})
    s.constraint({"x": 1, "y": 1}, "<=", 2, name="cap")
    r = api.run("mixed", s, freeze={"x": 0})
    assert verify(r.certificate, LIM).ok
    d = r.certificate.to_dict()
    d["payload"].update(bound=d["payload"]["achieved"], globally_optimal=True,
                        level="global_optimum")
    _refused(Certificate.from_dict(d))


def test_a_gap_is_the_difference_of_what_its_halves_certify():
    """CM-05: mu=100, nu=1, gap=99 beside two halves that both said 1."""
    from certo import PackingSpec, packing

    gap, _meta = packing.gap(PackingSpec(items=[("item", {"r"}, 1)],
                                         capacities=1))
    assert verify(gap, LIM).ok
    d = gap.to_dict()
    d["payload"].update(mu="100", nu="1", gap="99")
    _refused(Certificate.from_dict(d))


def test_a_resultant_is_the_sylvester_determinant():
    """CM-06: A = B = resultant = 0 is a Bezout identity, 0 = 0, and not the
    resultant of t and t - 1, which is -1 or 1."""
    import z3

    from certo import EliminateSpec, api

    t = z3.Real("t")
    r = api.run("eliminate", EliminateSpec(variables=["t"],
                                           equations=[t, t - 1], eliminate="t"))
    assert verify(r.certificate, LIM).ok
    d = r.certificate.to_dict()
    for f in ("A", "B", "resultant"):
        d["payload"][f] = {}
    _refused(Certificate.from_dict(d))


def test_a_hermite_pivot_is_a_row_of_the_matrix():
    """CM-07: pivot -1 let [[0,1],[1,0]] pass as Hermite with det 0."""
    base = {"question": "det", "matrix": [[0, 1], [1, 0]], "h": [[0, 1], [1, 0]],
            "u": [[1, 0], [0, 1]], "u_inv": [[1, 0], [0, 1]],
            "det_u": 1, "rank": 2, "det": 0}
    for pivots in ([-1, 0], [0, 2], [True, 0], ["0", 1]):
        _refused(Certificate("integer_matrix", True, dict(base, pivots=pivots)))


def test_an_induction_step_holds_from_where_the_chain_needs_it():
    """CM-08: a step proved under k >= 10 joined a base at 0 and 'proved'
    P(1) for P(k) = (k = 0 or k >= 10)."""
    import z3

    from certo import InductSpec, Spec, api

    k = z3.Int("k")

    def pred(k):
        return z3.Or(k == 0, k >= 10)

    step = (Spec().assume("from10", k >= 10).assume("induction", pred(k))
            .claim(pred(k + 1)))
    r = api.run("induct", InductSpec(k0=0, base_upto=0, step_from=0,
                                     base=lambda n: Spec().claim(pred(n)),
                                     step=step))
    assert r.verdict.value != "proved" and r.certificate is None

    # and a true induction still proves, and still verifies
    def double(k):
        return 2 * k >= k + 3

    n = z3.Int("n")
    good = (Spec().assume("from", n >= 3).assume("ih", double(n))
            .claim(double(n + 1)))
    r = api.run("induct", InductSpec(k0=3, base_upto=4, step_from=3,
                                     base=lambda m: Spec().claim(
                                         double(z3.IntVal(m))),
                                     step=good))
    assert r.verdict.value == "proved", r.detail
    assert verify(r.certificate, LIM).ok


def test_a_bisection_has_a_proof_on_one_side_and_a_refutation_on_the_other():
    """CM-09: the same proof of True at both ends certified a threshold."""
    import z3

    from certo import Spec, api
    from certo.certificate import bisect_certificate

    truth = api.run("prove", Spec().claim(z3.BoolVal(True))).certificate.to_dict()
    _refused(bisect_certificate("min_true", True, 1, 5, 4, truth, truth, []))


def test_a_bisection_end_is_about_its_own_query():
    """CM-09: a proof and a counterexample, each of the wrong question."""
    import z3

    from certo import Spec, api
    from certo.certificate import bisect_certificate
    from certo.engines.bisect import instance

    x = z3.Real("x")

    def at(c):
        return Spec().assume("dom", z3.And(x >= 0, x <= 2)).claim(x * x <= c)

    proof = api.run("prove", at(4)).certificate.to_dict()
    cex = api.run("prove", at(1)).certificate.to_dict()
    assert proof["kind"] == "unsat_core" and cex["kind"] == "model"
    # the ends as asked at 4 and 1, but filed as if asked at 0 and 5
    forged = bisect_certificate("min_true", False, 3.5, 4, 1, proof, cex, [],
                                good_instance=instance(at(0)),
                                bad_instance=instance(at(5)))
    _refused(forged)
    honest = bisect_certificate("min_true", False, 3.5, 4, 1, proof, cex, [],
                                good_instance=instance(at(4)),
                                bad_instance=instance(at(1)))
    assert verify(honest, LIM).ok


def test_a_mixed_residual_is_the_problem_frozen_at_its_design():
    """Found by the structural battery: the residual LP was compared over its
    own `var_names` -- emptied, no coefficient was compared -- and a row it
    did not know about was never read. A constraint added to SHRINK the
    residual made "optimal given the discrete part" false. And `conditional`
    was read, not derived."""
    from certo import LPSpec
    from certo.engines import mixed

    s = LPSpec(sense="max")
    s.variable("a", 0, 1, kind="binary")
    s.variable("w", 0, None)
    s.objective({"a": 3, "w": 1})
    s.constraint({"w": 6}, "<=", 1, name="cap")
    s.constraint({"a": 1}, "<=", 1, name="one")
    good = mixed.mixed(s, LIM).certificate.to_dict()
    assert verify(Certificate.from_dict(good), LIM).ok
    d = json.loads(json.dumps(good))
    rp = d["payload"]["residual"]["payload"]
    rp["A"].append(["1"] * len(rp["A"][0]))
    rp["b"].append("0")
    rp["names"].append("shrink")
    rp["dual"].append("0")
    _refused(Certificate.from_dict(d))
    d = json.loads(json.dumps(good))
    d["payload"]["conditional"] = "99"
    _refused(Certificate.from_dict(d))


def _from_example(name, command, *flags):
    """The certificate an example produces, by the CLI, in this process."""
    import contextlib
    import io
    import tempfile
    from pathlib import Path

    from certo import cli, store

    root = Path(__file__).resolve().parent.parent
    out = Path(tempfile.mkdtemp(prefix="certo_adv_")) / "cert.json"
    with contextlib.redirect_stdout(io.StringIO()):
        cli.main([command, str(root / "examples" / name), *flags,
                  "--cert", str(out)])
    return store.read_json(str(out))


#: The kinds with no hand-built fixture above, each from the example that
#: produces it -- so every kind the registry verifies is in the battery, and
#: a kind added later without one fails `test_every_kind_is_in_the_battery`.
EXAMPLE_FIXTURES = [
    ("bisect_constant.py", "bisect", ()),
    ("synth_constant.py", "synth", ()),
    ("core_matrix.py", "core", ()),
    ("dependency_cycle.py", "cycle", ()),
    ("equitable_quotient.py", "quotient", ()),
    ("family_max.py", "family", ()),
    ("walkthrough.py", "opt", ("--gap",)),
    ("hypothesis_audit.py", "audit", ()),
    ("induct_sum.py", "induct", ()),
    ("integer_matrix.py", "matrix", ()),
    ("lean_binding.py", "bind", ()),
    ("linear_system.py", "solve", ()),
    ("mus_ramsey.py", "shrink", ()),
    ("setfamily_sweep.py", "sweep", ("--witnesses",)),
    ("parametric_symmetry.py", "reduce", ("--parametric",)),
    ("shrink_nonchordal.py", "shrink", ()),
    ("sweep_range_nested.py", "sweep", ("--n-range", "3..4")),
    ("symmetry_reduction.py", "reduce", ()),
    ("synth_prove_identity.py", "synth", ("--prove-candidate",)),
    ("toric_cone.py", "cone", ()),
    ("variable_range.py", "range", ("--var", "a")),
]


def _built_fixtures() -> list:
    """The four kinds no example produces, built here."""
    import tempfile
    from pathlib import Path

    from certo import LPSpec, PackingSpec
    from certo.engines import bb, graphsearch, lp, shrink
    from certo.spec import load_spec

    out = []
    s = LPSpec(sense="max")
    s.variable("x")
    s.objective({"x": 1})
    s.constraint({"x": 1}, "<=", 1, name="hi")
    s.constraint({"x": -1}, "<=", -2, name="lo")
    out.append(lp.infeasible_certificate(s, LIM).to_dict())
    items = [("e{}".format(i), ("v{}".format(i), "v{}".format((i + 1) % 5)), 1)
             for i in range(5)]
    spec = PackingSpec(items=items, capacities=1, integer=True).to_lp()
    out.append(bb.prove_optimal(spec, LIM, max_nodes=1).certificate.to_dict())
    out.append(graphsearch.enum(5, ["connected"], LIM).certificate.to_dict())
    src = Path(tempfile.mkdtemp(prefix="certo_adv_dom_")) / "dom.py"
    src.write_text(
        "from fractions import Fraction\nfrom certo import DomainSpec\n"
        "def spec():\n    return DomainSpec(\n"
        "        items=[(s, r) for s in range(2, 7) for r in range(2, 7)],\n"
        "        predicate=lambda p: p[0] * p[1] >= 12,\n"
        "        reduce=lambda p: ([(p[0] - 1, p[1]), (p[0], p[1] - 1)]\n"
        "                          if p[0] > 1 and p[1] > 1 else []),\n"
        "        key=lambda p: 's={},r={}'.format(*p))\n", encoding="utf-8")
    dspec = load_spec(src)
    start = next(i for i in dspec.enumerate() if dspec.id_of(i) == "s=2,r=2")
    out.append(shrink.shrink_domain(dspec, start, LIM,
                                    spec_path=str(src)).certificate.to_dict())
    return out


#: Fields of the example-built kinds that carry no claim, so `probe` -- one
#: field at a time -- skips them for that kind only, each with its reason.
EXAMPLE_SKIPS = {
    "dependency_cycle": ("classes",   # declared, and the warning says so
                         "cycle",     # the chain's names, for reading
                         "empty"),    # True -> False only weakens the claim
    "integer_matrix": ("fingerprint_recipe",),   # prose
    "lean_binding": ("certificate", "declaration", "spec"),  # path, Lean name, record
    "orbit_witnesses": ("sweep",),    # `mutate` reaches the nested title
    "branch_frontier": ("reason",),   # why the search stopped
}

#: The kinds the hand-built fixtures above cover; with EXAMPLE_FIXTURES and
#: `_built_fixtures`, every kind the registry verifies.
HANDBUILT_KINDS = {
    "unsat_core", "model", "farkas", "lp_dual", "mixed_design", "exact_cover",
    "resultant", "branch_bound", "first_entry", "first_moment", "ratio_bound",
    "integer_peak", "parametric_bound", "ideal", "sos", "number", "asymptotic",
    "ball", "sweep", "domain_sweep", "drat", "cnf_model", "symmetric_inertia",
    "clique_lp", "parametric_atlas", "affine_semigroup", "capacity_profile",
    "proof", "polynomial_nonneg", "pinned_value",
}


def test_every_kind_is_in_the_battery():
    """Both batteries -- one field at a time, and the structural forgeries --
    over a certificate of EVERY kind. Run over the 25 kinds that had no
    fixture, they found nine more conclusions nothing recomputed, among them
    `toric_cone`'s `regular`, `height_one` and `crepant`, `linear_system`'s
    `status`, and a branch frontier with no root."""
    from certo.certificate import VERIFIERS

    certs = ([_from_example(n, c, *f) for n, c, f in EXAMPLE_FIXTURES]
             + _built_fixtures())
    kinds = {d["kind"] for d in certs}
    assert kinds | HANDBUILT_KINDS == set(VERIFIERS), sorted(
        set(VERIFIERS) - kinds - HANDBUILT_KINDS)
    for d in certs:
        _report(d["kind"], probe(Certificate.from_dict(d),
                                 skip=EXAMPLE_SKIPS.get(d["kind"], ())))


def test_the_structural_battery_found_these_in_kinds_it_had_not_reached():
    """Run over the examples of kinds with no fixture above, the battery
    found five more claims nothing re-checked. Each is pinned here."""
    # hypothesis_audit: a NEEDED hypothesis relabelled REDUNDANT -- a positive
    # claim, and the reader drops the hypothesis. It was never asked again.
    d = _from_example("hypothesis_audit.py", "audit")
    assert verify(d, LIM).ok
    row = next(r for r in d["payload"]["rows"] if r["verdict"] == "needed")
    row.update(verdict="redundant", witness=None)
    d["payload"]["counts"] = {k: sum(1 for r in d["payload"]["rows"]
                                     if r["verdict"] == k)
                              for k in d["payload"]["counts"]}
    _refused(Certificate.from_dict(d))
    # ... and a hypothesis removed from the formulas, its row left behind.
    d = _from_example("hypothesis_audit.py", "audit")
    d["payload"]["hypotheses_smt2"].pop(next(iter(d["payload"]["hypotheses_smt2"])))
    _refused(Certificate.from_dict(d))

    # dependency_cycle: the closing comparison read its two classes from the
    # payload, so the steps -- emptied -- decided nothing.
    d = _from_example("dependency_cycle.py", "cycle")
    assert verify(d, LIM).ok
    d["payload"]["steps"] = []
    _refused(Certificate.from_dict(d))

    # synth_proved: the candidate shown was not tied to the one found.
    d = _from_example("synth_prove_identity.py", "synth", "--prove-candidate")
    assert verify(d, LIM).ok
    d["payload"]["candidate"] = {k: v + 1 for k, v in d["payload"]["candidate"].items()}
    _refused(Certificate.from_dict(d))

    # sweep_range: no entry per size, so `entries: []` checked nothing.
    d = _from_example("sweep_range_nested.py", "sweep", "--n-range", "3..4")
    assert verify(d, LIM).ok
    d["payload"]["entries"] = []
    _refused(Certificate.from_dict(d))

    # linear_system / toric_cone: vectors read with `zip` at the wrong length.
    d = _from_example("linear_system.py", "solve")
    assert verify(d, LIM).ok
    d["payload"]["matrix"][0] = d["payload"]["matrix"][0] + ["7"]
    _refused(Certificate.from_dict(d))
    d = _from_example("toric_cone.py", "cone")
    assert verify(d, LIM).ok
    first = next(iter(d["payload"]["rays"]))
    d["payload"]["rays"][first] = d["payload"]["rays"][first][:-1]
    _refused(Certificate.from_dict(d))


def test_a_bisection_end_is_the_family_at_its_t_when_the_spec_is_there():
    """CM-09: a proof at t=4 still closes the query at t=5, so only the
    family, rebuilt from the spec, says that the end was not asked at 5.
    And z3 prints one formula differently depending on how it was built:
    the rebuilt query is compared as a formula, not as text."""
    import tempfile
    from pathlib import Path

    from certo import api
    from certo.engines.bisect import instance
    from certo.spec import load_spec

    src = Path(tempfile.mkdtemp(prefix="certo_bisect_")) / "family.py"
    src.write_text(
        "import z3\nfrom certo import BisectSpec, Spec\n"
        "def build(c):\n"
        "    x = z3.Real('x')\n"
        "    s = Spec().assume('dom', z3.And(x >= 0, x <= 2))\n"
        "    return s.claim(x * x <= z3.RealVal(c))\n"
        "def spec():\n"
        "    return BisectSpec(build=build, lo=0, hi=8, integer=True)\n",
        encoding="utf-8")
    r = api.run("bisect", load_spec(src), spec_path=str(src))
    assert r.verdict.value == "proved", r.detail
    rep = verify(r.certificate, LIM)
    assert rep.ok and not rep.warnings, (rep.checks, rep.warnings)
    d = r.certificate.to_dict()
    p = d["payload"]
    p["good_instance"] = instance(load_spec(src).build(p["good_t"] + 1))
    _refused(Certificate.from_dict(d))


def test_the_solver_s_indicator_names_cannot_collide_with_a_user_s():
    """CM-01: a Bool named like certo's own indicator was 'proved', and the
    claim is false."""
    import z3

    from certo import Spec, api

    q = z3.Bool("__p___goal__")
    r = api.run("prove", Spec().claim(q))
    assert r.verdict.value != "proved", r.verdict
    # the same name in a TRUE claim still proves, and verifies
    r = api.run("prove", Spec().assume("h", q).claim(q))
    assert r.verdict.value == "proved" and verify(r.certificate, LIM).ok


def test_a_mus_names_every_clause_it_keeps():
    """CM-02: `mus_indices: []` and no witnesses passed a non-minimal MUS."""
    _refused(Certificate("mus", True, {
        "original": [[1], [-1], [2]], "mus": [[1], [-1], [2]], "proof": ["0"],
        "mus_indices": [], "witnesses": {}}))


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
