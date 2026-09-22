"""The gap between a cone and the semigroup inside it.

`certo cone` answers questions about the RATIONAL cone over a set of
generators. An affine semigroup is what you can actually reach by ADDING
them, and the difference between the two is exactly where normality lives.

The textbook instance, and it fits on one line:

    S = N.(1,0) + N.(1,1) + N.(1,3)

The point (1,2) is in the cone over those generators -- it sits between (1,0)
and (1,3). It is in the GROUP they generate, which is all of Z^2, since
(1,1) - (1,0) = (0,1). And it is not in the semigroup: a non-negative integer
combination summing to (1,2) would need first coordinates adding to 1, so
exactly one generator, and none of the three is (1,2).

Those three facts together REFUTE normality, and each of them is arithmetic:
coefficients for the first two, and for the third a bound. The grading
u = (1,0) pairs to 1 with every generator, so any representation of a point of
degree d uses at most d generators in total -- here d = 1, which is why the
search is over three candidates rather than over an infinite set.

WHAT THIS DOES NOT DO is tell you a semigroup IS normal. That is a decision
about every lattice point of the cone, it is what Normaliz is for, and asking
gets an honest "not mine" rather than a silence.

    $ certo semigroup examples/affine_semigroup.py
"""
from certo import SemigroupSpec


def spec():
    """Not normal, and the witness says so."""
    return SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        points={
            "witness": (1, 2),      # in the cone, in the group, not in S
            "reachable": (2, 1),    # a + b
            "outside": (1, -1),     # not even in the cone: separated
        },
        # A PROPOSED minimal generating set, checked rather than computed --
        # and unlike normality, this one is DECIDED. See `hilbert_basis`
        # below for what the three questions are.
        hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        title="N(1,0) + N(1,1) + N(1,3): not normal",
    )


def orthant():
    """The free semigroup on the axes. Normal, and nothing here says so."""
    return SemigroupSpec(
        generators={"e1": (1, 0), "e2": (0, 1)},
        points={"v": (3, 4), "negative": (-1, 2)},
        title="the first quadrant",
    )


def redundant():
    """`dup` is twice `a`, so the generating set is not minimal."""
    return SemigroupSpec(
        generators={"a": (1, 0), "dup": (2, 0)},
        title="a generating set that is not minimal",
    )


def a_line():
    """Not pointed: no grading exists, so no search here terminates, and the
    command says that instead of looking for a while."""
    return SemigroupSpec(
        generators={"right": (1, 0), "left": (-1, 0)},
        points={"x": (5, 0)},
        title="a semigroup that is a whole line",
    )


def hilbert_basis():
    """A PROPOSED minimal generating set, checked rather than computed.

    This is the one claim here that is DECIDED rather than only refuted. For a
    pointed semigroup the minimal generating set is unique and is exactly the
    set of irreducible non-zero elements, so three bounded questions settle
    it: each element is in S, each is irreducible, and every generator is
    reachable from the proposed set. Computing such a set is Normaliz's job.
    """
    return SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        title="the generators are already minimal",
    )


def hilbert_with_something_reducible():
    """`extra` is `a + b`, so it is not irreducible and the set is not the
    minimal one -- and the decomposition that reduces it comes back with the
    answer."""
    return SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        hilbert={"a": (1, 0), "b": (1, 1), "c": (1, 3), "extra": (2, 1)},
        title="a proposed set with a reducible element",
    )


def hilbert_missing_one():
    """Drop `c` and the set no longer generates: `c` is named as unreachable
    rather than the answer being a bare no."""
    return SemigroupSpec(
        generators={"a": (1, 0), "b": (1, 1), "c": (1, 3)},
        hilbert={"a": (1, 0), "b": (1, 1)},
        title="a proposed set that does not generate",
    )
