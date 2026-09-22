"""Search with floating point, certify with certo, in ONE run.

THE MISREADING THIS ANSWERS. A user reported that certo "is not a sweep
engine: its spec is a `.py` with `spec()` per instance", and went outside to
compute an invariant over thousands of chordal graphs with `scipy.milp`
before deciding what to certify. The conclusion -- fast floating point to find
the statement, exact arithmetic to prove it -- is right. The premise is not:
the predicate is ordinary Python, so the fast solver goes INSIDE it.

WHAT THAT BUYS OVER A HAND-WRITTEN LOOP:

  * the family comes out ALREADY up to isomorphism and already filtered;
    `chordal` is a built-in filter, not something to reimplement;
  * `collect` turns the sweep into a calibration -- min, max, the mean as an
    EXACT RATIONAL, and the extremal graphs named in graph6. That is the
    conjecture-finding output, and it arrives from the same run as the
    verdict, so nothing has to be lined up afterwards;
  * the level is reported honestly. A scipy-backed predicate is not certified
    per instance, and the banner says `reproducible` rather than `certified`
    and counts the uncertified evaluations. `verify` re-runs the predicate and
    names the first item that disagrees;
  * `cert_mode="failures"` certifies only the counterexamples -- barrer
    barato, certify what matters.

WHAT IS SWEPT HERE. Chordal graphs are perfect, so `alpha(G) * omega(G) >= n`.
That is a real statement with content, and it is the kind of thing you would
arrive at by collecting `alpha` over a family and staring at the extremes --
which is exactly what the calibration prints.

AND THE MEASUREMENT THAT SURPRISED ME, which is why both paths are here.
`scipy.milp` is the SLOWER of the two at these sizes, by an order of
magnitude, computing the same numbers:

    n=7    272 graphs     scipy 0.19 s     exhaustion 0.01 s
    n=8   1614 graphs     scipy 3.99 s     exhaustion 0.42 s

Nothing is wrong with scipy. A `milp` call costs about 2.5 ms of setup before
HiGHS sees anything -- numpy arrays, a `LinearConstraint`, the crossing into
the solver -- and an independence number on eight vertices is a quarter of a
millisecond of Python. Per-call overhead dominates until the instance is big
enough to amortise it. So "go outside for the fast solver" is worth measuring
before it is worth doing: over thousands of SMALL instances the obvious loop
wins, and over a few large ones it does not.

The pattern this example is really about survives either way. Whatever
computes the invariant fastest goes inside the predicate, and certo does the
enumeration, the calibration and the artefact.

WHY n = 7 AND NOT 9. This runs in the examples suite, so it is sized to be
polite: 272 connected chordal graphs, about two seconds, nearly all of it the
enumeration. The interesting sizes are larger and the shape of the spec does
not change -- only `N` does:

    n=7     272 graphs     ~2 s
    n=8    1614 graphs     ~50 s without nauty, seconds with it
    n=9          more      needs `geng` on PATH to be sensible at all

Install nauty and `certo doctor` will find `geng`; the enumeration then runs
outside Python and the whole cost moves into the predicate, which is where it
belongs. certo bounds that enumeration -- `Limits.enumerate_timeout_s` and
`max_output_mb` -- and a run that hits a bound is REFUSED rather than
returning a shorter family, because a prefix of the graphs looks exactly like
all of them.

SCIPY IS OPTIONAL and is not a certo dependency. Without it this falls back to
the exhaustion above, which gives the same calibration down to the exact
rational mean; `describe` prints which one actually ran, so the example never
claims to have used something it did not.

    $ certo sweep examples/sweep_with_scipy.py
"""
from itertools import combinations

from certo import Outcome, SweepSpec

N = 7

try:
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    HAVE_SCIPY = True
except ImportError:                      # pragma: no cover - depends on env
    HAVE_SCIPY = False


def _alpha_scipy(g) -> int:
    """Independence number, by floating-point MILP. Fast, not certified."""
    rows = [[1.0 if v in (i, j) else 0.0 for v in range(g.n)]
            for i, j in g.edges()]
    cons = [LinearConstraint(np.array(rows), -np.inf, 1.0)] if rows else []
    r = milp(c=-np.ones(g.n), constraints=cons,
             integrality=np.ones(g.n), bounds=Bounds(0, 1))
    return int(round(-r.fun))


def _alpha_exact(g) -> int:
    """The same number, by exhaustion. Only sensible because n is small."""
    best = 0
    for size in range(g.n, best, -1):
        for s in combinations(range(g.n), size):
            if not any(g.has_edge(a, b) for a, b in combinations(s, 2)):
                return size
    return best


#: `alpha` is asked for twice per graph -- once by the predicate, once by
#: `collect` -- so it is cached. `Graph` is a frozen dataclass and hashes on
#: `(n, bits)`, which is the cheap key; the first version of this keyed on
#: `to_graph6()` and came out SLOWER than recomputing, because building the
#: graph6 string costs more than the search does at this size.
_ALPHA: dict = {}
_OMEGA: dict = {}


def alpha(g) -> int:
    if g not in _ALPHA:
        _ALPHA[g] = _alpha_scipy(g) if HAVE_SCIPY else _alpha_exact(g)
    return _ALPHA[g]


def omega(g) -> int:
    """Clique number, by exhaustion: it is the cheap half at this size."""
    if g not in _OMEGA:
        _OMEGA[g] = next(
            (size for size in range(g.n, 0, -1)
             for s in combinations(range(g.n), size)
             if all(g.has_edge(a, b) for a, b in combinations(s, 2))), 0)
    return _OMEGA[g]


def spec():
    """Perfection, as a finite case: `alpha * omega >= n` on chordal graphs."""
    return SweepSpec(
        n=N,
        filters=["connected", "chordal"],
        predicate=lambda g: Outcome(alpha(g) * omega(g) >= g.n),
        # The conjecture-finding half: min, max, exact mean, and the graphs
        # that attain the extremes -- from the same run as the verdict.
        collect=alpha,
        describe=lambda g: "alpha={} omega={} via {}".format(
            alpha(g), omega(g), "scipy.milp" if HAVE_SCIPY else "exhaustion"),
        title="alpha * omega >= n on connected chordal graphs, n={}".format(N),
    )
