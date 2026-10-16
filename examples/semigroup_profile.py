"""semigroup profiles: the least number of cliques for a number of edges.

S_m = N{(1, binom(s, 2)) : 2 <= s <= m}: a clique of size s counts one clique
and binom(s, 2) edges. For m = 11 and q = m (m - 2) = 99 edges, the least k
with (k, 99) in S is asked as a PROFILE: every smaller k is excluded (each a
search the verifier redoes), and the least one is a membership with its
coefficients. These are COUNTS -- that physical cliques with these counts fit
in a graph is not said here.

    certo semigroup examples/semigroup_profile.py
    certo verify out/semigroup_profile.json
"""
from math import comb

from certo import SemigroupSpec


def spec():
    m = 11
    return SemigroupSpec(
        title="the least number of cliques for {} edges, m = {}".format(m * (m - 2), m),
        generators={"s{}".format(s): (1, comb(s, 2)) for s in range(2, m + 1)},
        points={"two": (2, m * (m - 2))},
        profiles={"q": {"point": [None, m * (m - 2)], "up_to": 12}},
    )
