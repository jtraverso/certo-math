"""What survives when only a FRACTION of the shared resource is available.

THE QUESTION A SINGLE OPTIMUM CANNOT ANSWER. Two chordal pieces are glued
along one edge. Each piece has the same gap. Repeat one of them `b` times and
the gap stays bounded; repeat the other and it grows like `b`. The pieces are
the same graph. What differs is the shape of

    f_e(t) = max { gain : load on e <= t, every other load <= 1 }

near `t = 0` -- and `f_e(1)`, the ordinary optimum, is identical in both.

THE PIECE. `J` is the path of maximal cliques `0123`, `1234`, `2345`, with a
pendant vertex `6` attached at `2`. Thirteen columns of positive gain: ten
triangles and three `K4`s. Its profile along the edge `01` is

    f_01(t) = min{6 + 3t, 7 + t},   0 <= t <= 1

which is NOT a straight line between its endpoints: the line from `f(0) = 6`
to `f(1) = 8` would give `7` at `t = 1/2`, and the true value is `15/2`. That
half is exactly the information a single optimum throws away.

WHAT IS SUPPLIED AND WHAT IS CHECKED. The breakpoints, one dual per segment
and one source per breakpoint are INPUT -- finding them is parametric
programming, and SciPy, HiGHS or a pencil may do it. certo recomputes every
number from the columns: each dual's feasibility against all thirteen columns,
each source's loads and value, the segment arithmetic, the agreement at the
breakpoints, and the coverage of `[0, 1]`.

WHY THIS DECIDES A CONTINUUM FROM FINITE DATA, which is the point of the kind:

  * a dual's feasibility is `A^T y >= c` and never mentions a capacity, so ONE
    dual bounds every `t` in its segment at once;
  * two sources at a segment's ends attain the whole segment, because
    interpolating them is feasible at the interpolated capacity and its value
    is the interpolation;
  * sorted segments sharing endpoints tile the domain.

Bound plus attainment plus coverage is an EQUALITY on `[0, 1]`.

    $ certo profile examples/capacity_profile.py
"""
from itertools import combinations

from certo import ProfileSpec

#: The thirteen columns of positive gain in J. A clique on `q` vertices gains
#: `C(q,2) - 1`; anything smaller gains nothing and is left out.
TRIANGLES = ["012", "013", "023", "123", "124", "134", "234", "235", "245",
             "345"]
K4S = ["0123", "1234", "2345"]

PARAMETER = "01"


def _edges(clique):
    vs = sorted(clique)
    return ["".join(pair) for pair in combinations(vs, 2)]


def _program():
    columns = {c: {e: 1 for e in _edges(c)} for c in TRIANGLES + K4S}
    gain = {c: len(_edges(c)) - 1 for c in columns}
    rows = sorted({e for usage in columns.values() for e in usage})
    # Every edge has capacity one except the parameter, whose capacity IS `t`.
    capacity = {e: 1 for e in rows if e != PARAMETER}
    return columns, gain, capacity


def spec():
    """`f_01(t) = min{6 + 3t, 7 + t}` on `[0, 1]`, decided."""
    columns, gain, capacity = _program()
    return ProfileSpec(
        columns=columns,
        gain=gain,
        capacity=capacity,
        parameter=PARAMETER,
        domain=(0, 1),
        segments=[
            # f(t) <= 6 + 3t. The price of `01` is the slope.
            {"from": 0, "to": "1/2",
             "dual": {"01": 3, "23": 2, "14": 1, "24": 1, "34": 1, "45": 1}},
            # f(t) <= 7 + t. A different dual, cheaper on the interface and
            # dearer elsewhere -- which is why the profile bends.
            {"from": "1/2", "to": 1,
             "dual": {"01": 1, "12": 1, "13": 1, "23": 2, "24": 1, "34": 1,
                      "45": 1}},
        ],
        sources={
            # t = 0: three disjoint triangles avoiding the interface.
            0: {"023": 1, "124": 1, "345": 1},
            # t = 1/2: the bend. Six columns at half mass.
            "1/2": {"124": "1/2", "134": "1/2", "235": "1/2", "245": "1/2",
                    "345": "1/2", "0123": "1/2"},
            # t = 1: the ordinary fractional optimum, 8.
            1: {"012": "1/2", "134": "1/2", "245": "1/2", "0123": "1/2",
                "2345": "1/2"},
        },
        title="f_01 of the six-vertex chordal piece: not a straight line",
    )


def pendant():
    """The same graph along its pendant edge `26`, where nothing happens.

    No column of positive gain uses `26`, so the profile is constant. Worth
    keeping beside the other: same piece, same D(J) = 1, and gluing copies
    along THIS edge accumulates the gap while gluing along `01` does not.
    """
    columns, gain, _ = _program()
    rows = sorted({e for usage in columns.values() for e in usage})
    return ProfileSpec(
        columns=columns,
        gain=gain,
        capacity={e: 1 for e in rows},
        parameter="26",
        domain=(0, 1),
        # `26` prices at zero: no positive column touches it, so the bound is
        # flat and one segment covers everything.
        segments=[{"from": 0, "to": 1,
                   "dual": {"01": 1, "12": 1, "13": 1, "23": 2, "24": 1,
                            "34": 1, "45": 1}}],
        sources={
            0: {"012": "1/2", "134": "1/2", "245": "1/2", "0123": "1/2",
                "2345": "1/2"},
            1: {"012": "1/2", "134": "1/2", "245": "1/2", "0123": "1/2",
                "2345": "1/2"},
        },
        title="f_26: constant, because no positive column uses the edge",
    )
