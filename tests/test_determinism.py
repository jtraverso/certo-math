"""The same question, twice, gives the same answer -- byte for byte.

The value of this tool in a loop with a model is that it is DETERMINISTIC: ask
whether a case holds, get a verdict, and get the same verdict tomorrow on
another machine. Everything else is downstream of that. A tool that answers
PROVED on one run and UNKNOWN on the next does not accelerate an exploration,
it poisons it -- the model cannot tell a real boundary from a flaky one, and
will build on the difference.

It holds. Nothing was testing that it does, which is the whole problem with a
property like this: it survives until one `set()` of strings leaks its
iteration order into a payload, and then it is quietly gone.

TWO PROPERTIES, TESTED SEPARATELY, because they fail for different reasons and
cost different amounts to check.

  SAME PROCESS, TWICE. Catches a clock reaching a payload, an unseeded
  sampler, state left behind by a previous run. Cheap, so every engine family
  gets a turn.

  DIFFERENT PROCESS, DIFFERENT `PYTHONHASHSEED`. Python randomises the hash of
  strings per process, so a set or dict whose iteration order reaches an
  output changes between runs and nowhere else. This is the failure that does
  not reproduce when you go looking for it. It needs real subprocesses, so it
  runs over a small fast subset rather than everything.

WHAT IS COMPARED is the payload, not the verdict. Two runs agreeing on PROVED
while disagreeing about the dual is still a drift: the certificate is the
artefact, and an artefact whose bytes move cannot be compared, deduplicated or
cited.

PROVENANCE IS STRIPPED AT EVERY LEVEL. A timestamp is legitimately per-run --
and for a certificate that embeds sub-certificates it sits INSIDE the payload,
which is how it used to move the digest of two identical runs.

WHAT IS NOT TESTED, and is a real limit: a wall-clock timeout. A run that
finishes on a fast machine and expires on a slow one gives two answers, and no
seeding fixes it. `rlimit` -- z3's deterministic work unit -- is the budget
without that problem, and `Limits` carries both.

`python tests/test_determinism.py`, or with pytest.
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
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"

from certo import Limits  # noqa: E402

LIM = Limits(timeout_ms=120_000)


def _strip(value):
    """Every `provenance` block gone, at every level."""
    if isinstance(value, dict):
        return {k: _strip(v) for k, v in value.items() if k != "provenance"}
    if isinstance(value, list):
        return [_strip(v) for v in value]
    return value


def _body(cert) -> str:
    return json.dumps(_strip(cert.to_dict()["payload"]), sort_keys=True,
                      ensure_ascii=False)


def _load(name):
    from certo.spec import load_spec

    return load_spec(str(EXAMPLES / name))


#: One per engine family, because the risks differ: z3 cores, SAT with a
#: proof, sweeps that sample, orbit decompositions, a float LP reconstructed
#: exactly, an SDP rounded to rationals. Each is ROUTED BY ITS OWN TYPE rather
#: than by a table written here -- the same dispatch `certo ask` uses, so this
#: cannot drift away from what the tool actually does.
IN_PROCESS = [
    "amgm.py", "ramsey.py", "sweep_orbits.py", "setfamily_sweep.py",
    "sos_quartic.py", "parametric_orbits.py",
    "first_moment.py", "first_entry.py", "ratio_window.py", "walkthrough.py",
    # `reduce` walks a dict of generators and `matrix` builds transforms whose
    # row order depends on which pivot came first; both are places where an
    # iteration order that follows string hashing would show up here.
    "symmetry_reduction.py", "integer_matrix.py",
    # the parametric quotient walks a dict of orbits and a dict of
    # generators per window point: plenty of places for an iteration
    # order that follows string hashing to reach a payload.
    "parametric_symmetry.py", "linear_system.py",
]


def _answer(name):
    """Run whatever answers this spec, the way `ask` picks it."""
    from certo.routing import runner_for

    from certo.routing import prepared

    spec = _load(name)
    command, fn = runner_for(spec)
    assert fn is not None, "{}: no runner for {}".format(
        name, type(spec).__name__)
    return fn(prepared(spec), LIM)


def test_the_same_question_twice_gives_the_same_bytes():
    """Same process, twice. A clock or an unseeded sampler shows up here."""
    drifted = []
    for name in IN_PROCESS:
        seen = set()
        for _ in range(2):
            res = _answer(name)
            assert res.certificate is not None, name
            seen.add(_body(res.certificate))
        if len(seen) != 1:
            drifted.append(name)
    assert not drifted, (
        "these payloads change between runs, so the certificate cannot be "
        "compared or cited: " + ", ".join(drifted))


def test_the_digest_survives_nested_certificates():
    """Where it used to move, and the reason it mattered.

    A certificate that embeds sub-certificates -- a branch-and-bound tree, an
    `opt --gap`, a composed proof -- carries THEIR provenance inside its own
    payload, so its digest differed between two identical runs. Citing a
    result by id did not work for exactly the certificates most worth citing.
    """
    from certo.engines import mixed

    seen = {_answer("walkthrough.py").certificate.digest() for _ in range(2)}
    assert len(seen) == 1, "walkthrough: {}".format(seen)

    spec = _load("mixed_design.py")
    lp_spec = spec.to_lp(integral=True) if hasattr(spec, "to_lp") else spec
    seen = {mixed.mixed(lp_spec, LIM).certificate.digest() for _ in range(2)}
    assert len(seen) == 1, "mixed_design: {}".format(seen)


def test_the_refutation_engines_are_deterministic_too():
    """`exists` is asked by name rather than routed to, because a CoverSpec
    answers two different questions. Its DRAT proof must still not move."""
    from certo.engines import algebra

    seen = set()
    for _ in range(2):
        res = algebra.exists(_load("no_decomposition.py"), LIM)
        assert res.certificate is not None
        seen.add(_body(res.certificate))
    assert len(seen) == 1, "the refutation moved between runs"


def test_a_sampling_command_seeds_from_limits_and_not_from_the_clock():
    """Spot checks sample. The seed is what makes that reproducible, and the
    default is zero rather than absent."""
    assert Limits().seed == 0
    src = ROOT / "src" / "certo" / "engines"
    for mod in ("domain.py", "graphsearch.py"):
        text = (src / mod).read_text(encoding="utf-8")
        # a bare `random.sample` would be seeded by the clock
        assert "random.Random((limits or Limits()).seed or 0)" in text, mod


# --- the one property that genuinely needs separate processes ---------------

#: Small and fast, because each is a real interpreter start. String hashing is
#: what varies here, so what matters is COVERAGE OF SHAPES -- names, ids,
#: dictionaries keyed by strings -- not coverage of engines.
CROSS_PROCESS = [
    ("amgm.py", "prove", []),
    ("setfamily_sweep.py", "sweep", ["--witnesses"]),
    ("parametric_orbits.py", "parametric", []),
    ("integer_matrix.py", "matrix", []),
]


class Stalled(RuntimeError):
    """The run produced nothing. NOT a determinism failure, and not reported
    as one: a test that cries wolf about the property it guards gets ignored,
    and then the property goes unguarded."""


def _run(command, name, flags, out, hashseed, attempts=3):
    env = dict(os.environ, PYTHONHASHSEED=str(hashseed))
    env.pop("CERTO_LANG", None)
    last = ""
    for _ in range(attempts):
        try:
            proc = subprocess.run(
                [sys.executable, "-m", "certo.cli", command,
                 str(EXAMPLES / name), *flags, "--cert", str(out)],
                cwd=str(ROOT), env=env, capture_output=True, text=True,
                timeout=300)
        except subprocess.TimeoutExpired:
            last = "timed out"
            continue
        if proc.returncode in (0, 1) and out.exists():
            return
        last = (proc.stderr or proc.stdout)[-200:] or "no certificate written"
    raise Stalled("{} {}: {}".format(command, name, last))


def test_string_hash_randomisation_does_not_reach_a_payload():
    """Different processes, different `PYTHONHASHSEED`, same bytes."""
    drifted, stalled = [], []
    with tempfile.TemporaryDirectory() as tmp:
        for name, command, flags in CROSS_PROCESS:
            got = []
            for seed in (0, 12345):
                out = Path(tmp) / "{}_{}.json".format(name, seed)
                try:
                    _run(command, name, flags, out, seed)
                except Stalled as e:
                    stalled.append(str(e))
                    break
                got.append(json.dumps(
                    _strip(json.loads(out.read_text(encoding="utf-8"))
                           ["payload"]), sort_keys=True))
            if len(got) == 2 and got[0] != got[1]:
                drifted.append(name)
    assert not drifted, ("hash order reaches the payload of: "
                         + ", ".join(drifted))
    # Reported separately, and loudly, because "we could not check" must never
    # render as "we checked and it was fine".
    assert not stalled, ("COULD NOT CHECK (environment, not determinism): "
                         + "; ".join(stalled))


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
