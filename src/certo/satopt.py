"""The optimum of a cover, partition or packing, by SAT -- with a proof.

`cover --minimum` tabulates a recurrence over masks: complete and
solver-free, and bounded by the number of subsets it reaches. Past that, the
same question has a second answer with the same strength:

    the optimum k is ATTAINED     -- the chosen candidates, checked by counting;
    and k - 1 (or k + 1) is NOT   -- a DRUP refutation of the encoding of
                                     "at most k - 1 parts" ("at least k + 1"),

the encoding being `existence.encode` (or `encode_packing` here), which
`verify` runs again, deterministically, before checking the proof by unit
propagation. A solver SEARCHES for k -- pysat when it is installed, the
internal CDCL otherwise -- and is trusted for nothing: the model is counted
and the refutation is re-checked.

The problems, over a universe and candidate subsets of it:

    cover        fewest candidates, every element in AT LEAST one
    partition    fewest candidates, every element in EXACTLY one
    packing      most candidates, pairwise DISJOINT (a hypergraph matching)
"""
from __future__ import annotations

from .i18n import t as _t

ENCODING = "certo-exists-1"
PROBLEMS = ("cover", "partition", "packing")


def encode_packing(vertices, hyperedges, at_least):
    """CNF: at least `at_least` of the hyperedges, pairwise disjoint."""
    from .cnf import CNF

    cnf = CNF(title="packing")
    var = [cnf.var("part_{}".format(i)) for i in range(len(hyperedges))]
    index = {_k(v): [] for v in vertices}
    for i, e in enumerate(hyperedges):
        for v in e:
            index.setdefault(_k(v), []).append(var[i])
    for v in vertices:
        lits = index.get(_k(v)) or []
        if len(lits) > 1:
            cnf.at_most_one(lits)
    n = len(var)
    if at_least > n:
        u = cnf.var("too_many")
        cnf.add(u)
        cnf.add(-u)
    elif at_least > 0:
        # at least k of n  <=>  at most n - k of their negations
        cnf.at_most_k([-x for x in var], n - at_least)
    return cnf


def _k(x):
    if isinstance(x, (list, tuple)):
        return tuple(sorted(_k(v) for v in x))
    return x


def bound_cnf(problem, universe, candidates, k):
    """The CNF whose UNSATISFIABILITY bounds the optimum: at most `k` parts
    (cover, partition) or at least `k` (packing)."""
    from .existence import encode

    if problem == "packing":
        return encode_packing(universe, candidates, k)
    cnf, _parts = encode(universe, candidates, exact=(problem == "partition"),
                         max_parts=k)
    return cnf


def valid(problem, universe, candidates, chosen) -> bool:
    """Does `chosen` (candidate indices) solve the problem? By counting."""
    if len(set(chosen)) != len(chosen) or any(
            not (0 <= j < len(candidates)) for j in chosen):
        return False
    count = {}
    for j in chosen:
        for v in candidates[j]:
            count[_k(v)] = count.get(_k(v), 0) + 1
    keys = {_k(u) for u in universe}
    if any(k not in keys for k in count):
        return False
    if problem == "packing":
        return all(c <= 1 for c in count.values())
    if problem == "partition":
        return all(count.get(k, 0) == 1 for k in keys)
    return all(count.get(k, 0) >= 1 for k in keys)


def _solve(cnf, timeout_s, proof):
    """`(status, model, proof_lines)`. pysat for a model when it is there;
    the internal CDCL whenever a PROOF is needed."""
    if not proof:
        try:
            from pysat.solvers import Solver

            with Solver(name="g4", bootstrap_with=cnf.clauses) as s:
                ok = s.solve()
                return ("sat", s.get_model(), None) if ok else ("unsat", None, None)
        except Exception:  # noqa: BLE001 -- absent or broken: the internal one
            pass
    from . import cdcl

    r = cdcl.solve(cnf.nvars, [c[:] for c in cnf.clauses], timeout_s=timeout_s,
                   emit_proof=proof)
    return r.status, r.model, r.proof


def optimum(problem, universe, candidates, timeout_s=60.0):
    """`{"k", "chosen", "proof", "bound"}` or raises `RuntimeError` with why.

    Search on k by satisfiability, then ONE refutation with a proof at the
    bound. For a minimum the search starts from all the candidates (or
    fails: no cover at all); for a maximum, from zero."""
    if problem not in PROBLEMS:
        raise ValueError(_t("satopt.bad_problem", problem=problem,
                            known=", ".join(PROBLEMS)))
    n = len(candidates)

    def chosen_of(model):
        true = {v for v in (model or []) if v > 0}
        return [i for i in range(n) if (i + 1) in true]

    if problem == "packing":
        k, best = 0, []
        while k < n:
            st, model, _p = _solve(bound_cnf(problem, universe, candidates, k + 1),
                                   timeout_s, False)
            if st != "sat":
                break
            got = chosen_of(model)
            best, k = got, len(got)
        bound = k + 1
    else:
        st, model, _p = _solve(bound_cnf(problem, universe, candidates, n),
                               timeout_s, False)
        if st != "sat":
            raise RuntimeError(_t("satopt.none", problem=problem))
        best = chosen_of(model)
        k = len(best)
        while k > 0:
            st, model, _p = _solve(bound_cnf(problem, universe, candidates, k - 1),
                                   timeout_s, False)
            if st != "sat":
                break
            best = chosen_of(model)
            k = len(best)
        bound = k - 1
    proof = []
    # A minimum of 0 needs no refutation: no count is below it.
    if problem == "packing" or bound >= 0:
        st, _m, proof = _solve(bound_cnf(problem, universe, candidates, bound),
                               timeout_s, True)
        if st != "unsat":
            raise RuntimeError(_t("satopt.no_proof", status=st))
    return {"k": k, "chosen": best, "proof": list(proof or []), "bound": bound}
