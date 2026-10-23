"""Is this certificate about THIS obligation?

A certificate verifies on its own terms: the cofactors expand to ITS claim,
the proof refutes ITS formula. Whether that claim is the one a consumer meant
is a different question, and `verify` cannot answer it alone. A user's
auditor caught the case this module is for: an obligation replaced by the
identity `0 = 0`, whose certificate is perfectly valid -- and certifies
nothing anybody needed.

`same_obligation(cert, spec)` reads the spec the way the engine reads it --
the same normalisation, the same cleared denominators, the same expansion of
cliques -- and compares it with what the certificate is about, part by part,
naming what differs. `fingerprint(obj)` is a canonical digest of either side.

Families, by certificate kind:

    ideal                      IdealSpec: variables, equations, claim, nonzero
    polynomial_nonneg          NonnegSpec: the polynomial, the box, the region
    sos                        SOSSpec: the variables and the polynomial
    cegis, cegis_none,         SynthSpec: the implementation's constraints, the
    synth_optimum,             domain, the correctness (and the objective and
    synth_proved               its sense, for an optimum)
    ratio_bound                RatioSpec: parameters, both sides, relation, region
    resultant                  EliminateSpec: variables, the two equations, the
                               variable eliminated
    integer_peak               PeakSpec: parameters, the integer variable, objective
    bound_step                 StepSpec: box, bound, substitutions, conclusion,
                               conditions
    parametric_bound           ParametricSpec: parameters, objective, constraints
    exact_cover, sat_optimum,  CoverSpec or HypergraphSpec: the universe, the
    recurrence_table           candidates (or parts), exact or not
    drat, cnf_model            CNFSpec: the clauses
    lp_dual, gap               LPSpec, PackingSpec, HypergraphSpec, CoverSpec:
                               the normalised program (`same_program`)
    unsat_core, model,         Spec: each named hypothesis and the claim
    propositional_refutation

For the first five the certificate carries the WHOLE obligation, and the two
fingerprints are equal exactly when the obligations are. A proof by `prove`
keeps only the hypotheses it used: its comparison is name by name, and
hypotheses the core did not need are not a difference.
"""
from __future__ import annotations

import contextvars
import hashlib
import json
from fractions import Fraction

from .i18n import t

#: certificate kind -> family
FAMILIES = {
    "ideal": "ideal",
    "polynomial_nonneg": "nonneg",
    "exact_cover": "cover", "sat_optimum": "cover", "recurrence_table": "cover",
    "drat": "cnf", "cnf_model": "cnf",
    "lp_dual": "lp", "gap": "lp",
    "unsat_core": "smt", "model": "smt", "propositional_refutation": "smt",
    "parametric_atlas": "atlas", "conditioned_cover": "covering",
    "role_transport": "roles", "farkas_ray": "system",
    "sos": "sos",
    # 0.35.1: the families a user bound by hand, session after session
    "cegis": "synth", "cegis_none": "synth", "synth_optimum": "synth",
    "synth_proved": "synth",
    "ratio_bound": "ratio", "resultant": "resultant", "integer_peak": "peak",
    "bound_step": "step", "parametric_bound": "parametric",
}

#: families whose certificate carries the whole obligation
WHOLE = ("ideal", "nonneg", "cover", "cnf", "lp", "atlas", "covering", "roles",
         "system", "sos", "synth", "ratio", "resultant", "peak", "step",
         "parametric")


# --- canonical pieces ---------------------------------------------------------

def _poly_key(p) -> list:
    """A polynomial independent of the ring's ORDER: `[[monomial, coef]]`
    with monomials spelled by variable name, sorted."""
    out = []
    for e, c in p.terms.items():
        mono = "*".join("{}^{}".format(v, k) if k > 1 else v
                        for v, k in sorted(zip(p.vars, e)) if k) or "1"
        out.append([mono, str(Fraction(c))])
    return sorted(out)


def _claim_text(v) -> str:
    """A claim as `_differences` shows it: a polynomial key, or -- an atlas,
    a parametric bound -- `[relation, key]`, whose relation is said first.
    0.36 read the pair as a key and raised instead of naming the change."""
    if v is None:
        return t("obligation.inconsistent")
    if isinstance(v, list) and len(v) == 2 and (v[0] is None or isinstance(v[0], str)):
        rel, key = v
        if key is None:
            return t("obligation.no_claim")
        body = _poly_text(key) if isinstance(key, list) else _short(key)
        return "{} {}".format(rel, body) if rel else body
    return _poly_text(v) if isinstance(v, list) else _short(v)


def _poly_text(key) -> str:
    if not key:
        return "0"
    return " + ".join("{}*{}".format(c, m) if m != "1" else c for m, c in key)[:160]


def _elem(x):
    """A cover element as `cover._key` identifies it, JSON-able."""
    from .cover import _key

    k = _key(x)
    return list(k) if isinstance(k, tuple) else k


def _family_sorted(parts) -> list:
    return sorted((sorted((_elem(e) for e in part), key=json.dumps)
                   for part in parts), key=json.dumps)


def _fraction(v) -> str:
    from .exact import to_fraction

    return str(to_fraction(v))


# --- the certificate's side --------------------------------------------------

def _of_cert(cert) -> dict:
    from .polynomials import Poly

    p, kind = cert.payload, cert.kind
    fam = FAMILIES.get(kind)
    if fam == "ideal":
        vs = tuple(p["variables"])
        return {"variables": sorted(vs),
                "equations": [_poly_key(Poly.parse(vs, g)) for g in p["equations"]],
                "claim": None if p.get("inconsistent")
                else _poly_key(Poly.parse(vs, p["claim"])),
                "nonzero": sorted((_poly_key(Poly.parse(vs, z))
                                   for z in p.get("nonzero") or []), key=json.dumps)}
    if fam == "atlas":
        vs = tuple(p["parameters"])
        cl = p.get("claim") or {}
        return {"variables": sorted(vs),
                "domain": {n: [_fraction(lo), None if hi is None else _fraction(hi)]
                           for n, (lo, hi) in p["domain"].items()},
                "region": {n: _poly_key(Poly.parse(vs, g))
                           for n, g in (p.get("region") or {}).items()},
                "claim": [cl.get("relation"),
                          _poly_key(Poly.parse(vs, cl["target"]))
                          if cl.get("target") is not None else None]}
    if fam == "system":
        # A standalone Farkas ray is about the system in its payload; this
        # says whether that system is YOUR program's `A x <= b, x >= 0`.
        return {"A": [[_fraction(v) for v in row] for row in p["A"]],
                "b": [_fraction(v) for v in p["b"]],
                "names": list(p.get("names") or [])}
    if fam == "roles":
        return {"edges": [list(e) for e in p["edges"]], "roles": p["roles"],
                "roles_after": p["roles_after"], "properties": p["properties"]}
    if fam == "covering":
        vs = tuple(p["parameters"])
        return {"variables": sorted(vs),
                "domain": {n: [_fraction(lo), _fraction(hi)]
                           for n, (lo, hi) in p["domain"].items()},
                "conditions": {n: _poly_key(Poly.parse(vs, g))
                               for n, g in (p.get("conditions") or {}).items()},
                "obligations": {n: [o["relation"], _poly_key(Poly.parse(vs, o["poly"]))]
                                for n, o in (p.get("obligations") or {}).items()}}
    if fam == "sos":
        vs = tuple(p["variables"])
        return {"variables": sorted(vs), "poly": _poly_key(Poly.parse(vs, p["poly"]))}
    if fam == "synth":
        if kind == "synth_proved":
            from .certificate import Certificate

            return _of_cert(Certificate.from_dict(p["synth"]))
        if kind == "synth_optimum":
            found = (p.get("found") or {}).get("payload") or {}
            sm = found.get("smt2") or {}
            return {"impl_constraints": _canon_smt2(p.get("base_smt2")),
                    "behavior": _canon_smt2(sm.get("behavior")),
                    "correctness": _canon_smt2(sm.get("correctness")),
                    "objective": [p.get("sense"), _canon_smt2(p.get("value_smt2"))]}
        sm = p.get("smt2") or {}
        return {"impl_constraints": _canon_smt2(sm.get("impl_constraints")),
                "behavior": _canon_smt2(sm.get("behavior")),
                "correctness": _canon_smt2(sm.get("correctness")),
                "objective": None}
    if fam == "ratio":
        return {"parameters": {n: _fraction(v) for n, v in p["parameters"].items()},
                "left": p["left"], "right": p["right"], "relation": p["relation"],
                "region": p.get("region") or {}}
    if fam == "resultant":
        return {"variables": list(p["variables"]), "eliminated": p["eliminated"],
                "equations": [p["f"], p["g"]]}
    if fam == "peak":
        return {"parameters": {n: _fraction(v) for n, v in p["parameters"].items()},
                "variable": p["variable"], "objective": p["objective"]}
    if fam == "step":
        return {"parameters": list(p["parameters"]), "box": p["box"],
                "conditions": p.get("conditions") or {}, "bound": p["bound"],
                "substitutions": [[s["var"], s["upper"]] for s in p.get("steps") or []],
                "conclude": p["conclude"]}
    if fam == "parametric":
        out = {"parameters": {n: _fraction(v) for n, v in p["parameters"].items()},
               "objective": p["objective"], "constraints": p["constraints"]}
        if _LEGACY.get():
            return out
        # 0.36 compared only the three above: a certificate of a minimisation,
        # of another region or box, or of no claim at all, was "the same"
        claim = p.get("claim") or None
        out.update({
            "sense": p.get("sense", "max"),
            "witness": "primal" if p.get("witness") == "primal" else "dual",
            "free": sorted(p.get("free") or []),
            "region": dict(p.get("region") or {}),
            "box": None if p.get("box") is None else
            {n: [_fraction(lo), _fraction(hi)] for n, (lo, hi) in p["box"].items()},
            "claim": None if claim is None else [claim.get("relation"), claim.get("target")]})
        return out
    if fam == "nonneg":
        vs = tuple(p["parameters"])
        return {"variables": sorted(vs),
                "poly": _poly_key(Poly.parse(vs, p["poly"])),
                "box": {n: [_fraction(lo), None if hi is None else _fraction(hi)]
                        for n, (lo, hi) in p["box"].items()},
                "region": {n: _poly_key(Poly.parse(vs, g))
                           for n, g in (p.get("region") or {}).items()}}
    if fam == "cover":
        if kind == "exact_cover":
            pool, how = p["parts"], ("partition" if p.get("exact") else "cover")
        elif kind == "sat_optimum":
            pool, how = p["candidates"], p["problem"]
        else:
            pool, how = p["candidates"], ("partition" if p.get("exact") else "cover")
        return {"universe": sorted((_elem(u) for u in p["universe"]), key=json.dumps),
                "candidates": _family_sorted(pool), "problem": how}
    if fam == "cnf":
        from .cnf import CNF

        cnf = CNF.from_dimacs(p["dimacs"])
        return {"clauses": sorted(sorted(c) for c in cnf.clauses)}
    if fam == "lp":
        q = p
        if kind == "gap":
            q = (p.get("relaxation") or {}).get("payload", p)
        return {"sense": q.get("sense", "max"),
                "A": [[_fraction(v) for v in row] for row in q.get("A") or []],
                "b": [_fraction(v) for v in q.get("b") or []],
                "c": [_fraction(v) for v in q.get("c") or []],
                "names": list(q.get("names") or [])}
    if fam == "smt":
        return {"formulas": _cert_formulas(cert),
                "dropped": list(p.get("dropped") or [])}
    return None


def _canon_smt2(text):
    """An SMT-LIB formula in a form two processes -- and two calls in one
    process -- agree on: parsed back here and printed by `_canon_term`."""
    import z3

    if text is None:
        return None
    fs = list(z3.parse_smt2_string(text))
    return _one(fs[0] if len(fs) == 1 else z3.And(*fs))


#: 0.36 canonicalised by printing through z3, which names its `let`s by
#: internal ids. Equal formulas printed alike only while one of them was
#: alive to be shared; freed, the ids were recycled and the same contract
#: read as another (a false "differs", reported in use). Set only by
#: `fingerprints`, to recompute what a 0.36 construction recorded.
_LEGACY = contextvars.ContextVar("certo_obligation_legacy", default=False)


def _one(f) -> str:
    if _LEGACY.get():
        from . import z3util

        return z3util.smt2(f)
    return _canon_term(f)


def _canon_term(f) -> str:
    """The formula as a DAG with its shared subterms named `$1, $2, ...` in
    the order a left-to-right traversal completes them: nothing in it comes
    from z3's ids, so the same formula prints alike whenever it is built.
    The uninterpreted symbols are declared first, sorted, so `x` Int and
    `x` Real differ."""
    import z3

    def kids(e):
        if z3.is_quantifier(e):
            return [e.body()]
        if z3.is_app(e):
            return e.children()
        return []

    count = {f.get_id(): 1}
    seen, post = {f.get_id()}, []
    stack = [(f, kids(f), 0)]
    while stack:
        e, ks, j = stack[-1]
        if j < len(ks):
            stack[-1] = (e, ks, j + 1)
            c = ks[j]
            ci = c.get_id()
            count[ci] = count.get(ci, 0) + 1
            if ci not in seen:
                seen.add(ci)
                stack.append((c, kids(c), 0))
        else:
            stack.pop()
            post.append(e)
    decls, text, lets = set(), {}, []
    for e in post:
        ks = kids(e)
        if z3.is_var(e):
            s = "(:var {})".format(z3.get_var_index(e))
        elif z3.is_quantifier(e):
            bound = " ".join("({} {})".format(e.var_name(i), e.var_sort(i).sexpr())
                             for i in range(e.num_vars()))
            s = "({} ({}) {})".format("forall" if e.is_forall() else
                                      "exists" if e.is_exists() else "lambda",
                                      bound, text[ks[0].get_id()])
        else:
            d = e.decl()
            if d.kind() == z3.Z3_OP_UNINTERPRETED:
                decls.add(d.sexpr())
            if not ks:
                s = e.sexpr()
            else:
                op = d.name()
                if d.params():
                    op = "(_ {} {})".format(op, " ".join(str(x) for x in d.params()))
                s = "({} {})".format(op, " ".join(text[k.get_id()] for k in ks))
        if ks and count[e.get_id()] > 1:
            lets.append("(${} {})".format(len(lets) + 1, s))
            s = "${}".format(len(lets))
        text[e.get_id()] = s
    body = text[f.get_id()]
    if lets:
        body = "(let* ({}) {})".format(" ".join(lets), body)
    return " ".join(sorted(decls) + [body])


def _cert_formulas(cert) -> dict:
    """`{name: smt2}` of what the proof is about; a model's formulas, which
    carry no names, keyed by position."""
    import z3

    p = cert.payload
    if cert.kind == "propositional_refutation":
        out = {}
        for name, smt2 in p.get("core") or []:
            fs = list(z3.parse_smt2_string(smt2))
            out[name] = _one(z3.And(*fs) if len(fs) != 1 else fs[0])
        return out
    if cert.kind == "unsat_core":
        fs = list(z3.parse_smt2_string(p["core_smt2"]))
        return {n: _one(f) for n, f in zip(p.get("names") or [], fs)}
    fs = list(z3.parse_smt2_string(p["smt2"]))
    return {"#{}".format(i): _one(f) for i, f in enumerate(fs)}


# --- the spec's side ---------------------------------------------------------

def _of_spec(spec, family, cert=None) -> dict:
    name = type(spec).__name__
    if family == "ideal":
        from .engines.algebra import ideal_polynomials

        vs = tuple(spec.variables)
        gs, claim, nonzero, _cleared = ideal_polynomials(spec, vs)
        return {"variables": sorted(vs),
                "equations": [_poly_key(g) for g in gs],
                "claim": None if claim is None else _poly_key(claim),
                "nonzero": sorted((_poly_key(z) for z in nonzero), key=json.dumps)}
    if family == "system":
        lp = _as_lp(spec)
        A, b, _c, names = lp.as_leq_system()
        return {"A": [[str(v) for v in row] for row in A],
                "b": [str(v) for v in b], "names": list(names)}
    if family == "roles":
        from . import roles as R

        E, V, before, after, sigma, props = R.normalise(
            spec.edges, spec.vertices, spec.roles, spec.roles_after,
            spec.mapping, spec.properties)
        if after is None and cert is not None:
            after = cert.payload.get("roles_after")
        return {"edges": sorted(sorted(e) for e in E), "roles": before,
                "roles_after": after, "properties": props}
    if family in ("atlas", "covering"):
        from .polynomials import Poly

        ring = tuple(spec.domain)

        def P(x):
            if isinstance(x, Poly):
                return x
            if isinstance(x, (int, Fraction)):
                return Poly.const(ring, x)
            return Poly.from_z3(x, ring)

        dom = {n: [_fraction(spec.domain[n][0]),
                   None if spec.domain[n][1] is None else _fraction(spec.domain[n][1])]
               for n in ring}
        if family == "covering":
            return {"variables": sorted(ring), "domain": dom,
                    "conditions": {str(n): _poly_key(P(g))
                                   for n, g in (spec.conditions or [])},
                    "obligations": {str(n): [rel, _poly_key(P(g))]
                                    for n, rel, g in _obligations(spec.obligations)}}
        rel, target = None, spec.claim
        if isinstance(spec.claim, tuple):
            rel, target = spec.claim
        if rel is None and cert is not None:
            rel = (cert.payload.get("claim") or {}).get("relation")
        return {"variables": sorted(ring), "domain": dom,
                "region": {str(n): _poly_key(P(g)) for n, g in (spec.region or [])},
                "claim": [rel, None if target is None else _poly_key(P(target))]}
    if family == "synth":
        from . import z3util

        impl, behav, corr = spec.normalized()
        out = {"impl_constraints": _canon_smt2(z3util.smt2(impl)),
               "behavior": _canon_smt2(z3util.smt2(behav)),
               "correctness": _canon_smt2(z3util.smt2(corr)), "objective": None}
        obj = spec.minimize if spec.minimize is not None else spec.maximize
        if obj is not None and cert is not None and cert.kind in ("synth_optimum",):
            value = cert.payload.get("value")
            out["objective"] = ["min" if spec.minimize is not None else "max",
                                _canon_smt2(z3util.smt2(obj == int(value)))
                                if value is not None else None]
        if obj is not None and cert is not None and cert.kind == "synth_proved":
            inner = cert.payload.get("synth") or {}
            if inner.get("kind") == "synth_optimum":
                from .certificate import Certificate

                return _of_spec(spec, family, Certificate.from_dict(inner))
        return out
    if family in ("ratio", "peak", "parametric"):
        params = {str(n): _fraction(v) for n, v in spec.parameters.items()}
        if family == "ratio":
            from .ratio import as_ratio

            ring = tuple(spec.parameters)
            ln, ld = as_ratio(spec.left, ring)
            rn, rd = as_ratio(spec.right, ring)
            return {"parameters": params, "left": [ln.serialize(), ld.serialize()],
                    "right": [rn.serialize(), rd.serialize()], "relation": spec.relation,
                    "region": {str(n): as_ratio(g, ring)[0].serialize()
                               for n, g in (spec.region or [])}}
        if family == "peak":
            return {"parameters": params, "variable": spec.variable,
                    "objective": spec.objective.serialize()}
        from .engines.algebra import _ser

        out = {"parameters": params,
               "objective": {v: _ser(spec, c) for v, c in spec.objective.items()},
               "constraints": [[str(n), {v: _ser(spec, c) for v, c in row.items()},
                                sense, _ser(spec, rhs)]
                               for n, row, sense, rhs in spec.constraints]}
        if _LEGACY.get():
            return out
        return dict(out, **_parametric_scope(spec, cert))
    if family == "resultant":
        from .engines.algebra import _poly

        variables = tuple(spec.variables)
        f, g = (_poly(e, variables) for e in spec.equations)
        return {"variables": list(variables), "eliminated": spec.eliminate,
                "equations": [f.serialize(), g.serialize()]}
    if family == "step":
        from . import boundstep as BS
        from .polynomials import Poly, as_poly, rational_function

        ring = tuple(spec.box)
        one = Poly.const(ring, 1)

        def R(x):
            if isinstance(x, Poly):
                return x, one
            if isinstance(x, (int, Fraction)):
                return Poly.const(ring, x), one
            return BS.normal(rational_function(x, ring))

        return {"parameters": list(ring),
                "box": {n: [str(Fraction(lo)), str(Fraction(hi))]
                        for n, (lo, hi) in spec.box.items()},
                "conditions": {str(n): as_poly(ring, g).serialize()
                               for n, g in (spec.conditions or [])},
                "bound": BS.ser(R(spec.bound)),
                "substitutions": [[str(v), BS.ser(R(u))] for v, u in (spec.substitute or [])],
                "conclude": BS.ser(R(spec.conclude))}
    if family == "sos":
        # 0.34 answered `same: None` for a sum of squares, and three sessions
        # bound their SOS certificates by hand.
        from .polynomials import Poly

        ring = tuple(str(v) for v in spec.variables)
        poly = spec.poly
        if isinstance(poly, (int, Fraction)):
            poly = Poly.const(ring, poly)
        elif not isinstance(poly, Poly):
            poly = Poly.from_z3(poly, ring)
        return {"variables": sorted(ring), "poly": _poly_key(poly)}
    if family == "nonneg":
        import z3  # noqa: F401 -- a z3 term is read through the same parser

        from .polynomials import Poly

        ring = tuple(spec.box or {})

        def P(x):
            if isinstance(x, Poly):
                return x
            if isinstance(x, (int, Fraction)):
                return Poly.const(ring, x)
            return Poly.from_z3(x, ring)

        target = None
        if getattr(spec, "clear_denominators", False) and not isinstance(
                spec.poly, (Poly, int, Fraction)):
            # read as the engine reads it: N, oriented by the certificate's
            # proved sign of D (or + when there is none to read)
            from .polynomials import rational_function

            num, _den = rational_function(spec.poly, ring)
            o = ((cert.payload.get("cleared") or {}).get("orientation", 1)
                 if cert is not None else 1)
            target = num.scaled(o)
        return {"variables": sorted(ring),
                "poly": _poly_key(target if target is not None else P(spec.poly)),
                "box": {n: [_fraction(spec.box[n][0]),
                            None if spec.box[n][1] is None else _fraction(spec.box[n][1])]
                        for n in ring},
                "region": {str(n): _poly_key(P(g)) for n, g in (spec.region or [])}}
    if family == "cover":
        from .cover import edges_of

        problem = (cert.payload.get("problem") if cert is not None else None)
        if name == "HypergraphSpec":
            if problem is None and spec.problem == "matching":
                problem = "packing"
            spec = spec.to_packing() if spec.problem == "matching" else spec.to_cover()
        if cert is not None and cert.kind == "exact_cover":
            pool = list(spec.parts or [])
        else:
            pool = list(spec.candidates or spec.parts or [])
        if spec.cliques:
            pool = [edges_of(c) for c in pool]
        how = "partition" if spec.exact else "cover"
        if problem == "packing":
            how = "packing"        # a packing does not depend on `exact`
        return {"universe": sorted((_elem(u) for u in spec.universe), key=json.dumps),
                "candidates": _family_sorted(pool), "problem": how}
    if family == "cnf":
        return {"clauses": sorted(sorted(c) for c in spec.cnf.clauses)}
    if family == "lp":
        lp = _as_lp(spec)
        A, b, c, names = lp.as_leq_system()
        return {"sense": lp.sense,
                "A": [[str(v) for v in row] for row in A],
                "b": [str(v) for v in b], "c": [str(v) for v in c],
                "names": list(names)}
    if family == "smt":
        import z3

        out = {str(n): _one(f) for n, f in spec.assumptions}
        if spec.goal is not None:
            out["__goal__"] = _one(z3.Not(spec.goal))
            out["__goal__+"] = _one(spec.goal)
        return {"formulas": out}
    return None


def _as_lp(spec):
    name = type(spec).__name__
    if name == "LPSpec":
        return spec
    if name in ("PackingSpec", "HypergraphSpec", "CoverSpec"):
        return spec.to_lp()
    raise TypeError(t("obligation.no_program", got=name))


# --- the comparison ----------------------------------------------------------

def _digest(family, parts) -> str:
    text = json.dumps({"family": family, "parts": parts}, sort_keys=True,
                      ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def fingerprint(obj, family=None) -> str | None:
    """A canonical digest of an obligation: of a certificate (what it is
    about), or of a spec (what it asks; give `family` when the spec type
    alone does not say -- an `LPSpec` is `lp`). Equal fingerprints mean the
    same obligation for the families whose certificate carries all of it;
    None where the certificate keeps only a core (`prove`)."""
    from .certificate import Certificate

    if isinstance(obj, dict):
        obj = Certificate.from_dict(obj)
    if isinstance(obj, Certificate):
        fam = FAMILIES.get(obj.kind)
        if fam not in WHOLE:
            return None
        return _digest(fam, _of_cert(obj))
    fam = family or _family_of_spec(obj)
    if fam not in WHOLE:
        return None
    return _digest(fam, _of_spec(obj, fam))


def fingerprints(cert) -> set:
    """Every digest this certificate's obligation may have been recorded
    under: today's, and -- for the formula families -- the one 0.36 printed
    through z3 (see `_LEGACY`). A construction written by 0.36 recorded the
    latter; it is still read."""
    out = {fingerprint(cert)} - {None}
    tok = _LEGACY.set(True)
    try:
        out |= {fingerprint(cert)} - {None}
    except Exception:  # noqa: BLE001 -- the legacy printer is only a fallback
        pass
    finally:
        _LEGACY.reset(tok)
    return out


def _parametric_scope(spec, cert) -> dict:
    """What a ParametricSpec claims beyond its program, as the engine writes
    it into the certificate: the sense, which witness, the free columns, the
    region and the box it is claimed on, and the target."""
    from . import parametric as PM
    from .polynomials import Poly

    ring = tuple(spec.parameters)

    def P(x):
        if isinstance(x, Poly):
            return x
        if isinstance(x, (int, Fraction)):
            return Poly.const(ring, x)
        return Poly.from_z3(x, ring)

    minimising = getattr(spec, "sense", "max") == "min"
    box = PM._box_of(spec, ring)
    pieces = cert is not None and cert.payload.get("witness") == "pieces"
    claim = getattr(spec, "claim", None)
    return {
        "sense": "min" if minimising else "max",
        "witness": "primal" if getattr(spec, "primal", None) is not None else "dual",
        "free": sorted(str(v) for v in (getattr(spec, "free", None) or [])),
        # a box cut into pieces is certified on the whole box: no region is
        # written, and none is needed for the claim to hold where one was meant
        "region": {} if pieces else {str(n): P(g).serialize()
                                     for n, g in (getattr(spec, "region", None) or [])},
        "box": None if box is None else
        {n: [_fraction(lo), _fraction(hi)] for n, (lo, hi) in box.items()},
        "claim": None if claim is None else
        [">=" if minimising else "<=", P(claim).serialize()]}


def _obligations(obls):
    """`[(name, relation, expr)]` from a CoveringSpec's obligations, given as
    `[(name, expr)]` (read `expr > 0`) or `[(name, relation, expr)]`."""
    out = []
    for o in obls or []:
        if len(o) == 2:
            out.append((str(o[0]), ">", o[1]))
        else:
            out.append((str(o[0]), str(o[1]), o[2]))
    return out


def _family_of_spec(spec):
    return {"IdealSpec": "ideal", "NonnegSpec": "nonneg", "CoverSpec": "cover",
            "AtlasSpec": "atlas", "CoveringSpec": "covering", "RoleSpec": "roles",
            "CNFSpec": "cnf", "LPSpec": "lp", "PackingSpec": "lp", "SOSSpec": "sos",
            "SynthSpec": "synth", "RatioSpec": "ratio", "EliminateSpec": "resultant",
            "PeakSpec": "peak", "StepSpec": "step", "ParametricSpec": "parametric",
            "Spec": "smt"}.get(type(spec).__name__)


def same_obligation(cert, spec) -> dict:
    """`{"same", "family", "differences", "fingerprint"}`: is this
    certificate about the obligation this spec states?

    `same` is None, with the reason in `differences`, for a kind this does
    not cover. `fingerprint` holds both digests where the certificate carries
    the whole obligation."""
    from .certificate import Certificate

    if isinstance(cert, dict):
        cert = Certificate.from_dict(cert)
    fam = FAMILIES.get(cert.kind)
    if fam is None:
        return {"same": None, "family": None, "fingerprint": None,
                "differences": [t("obligation.not_covered", kind=cert.kind)]}
    try:
        mine = _of_cert(cert)
        theirs = _of_spec(spec, fam, cert)
    except Exception as e:  # noqa: BLE001 -- a spec this cannot read is a difference
        return {"same": False, "family": fam, "fingerprint": None,
                "differences": [t("obligation.unreadable", type=type(e).__name__,
                                  why=str(e)[:200])]}
    diffs = (_smt_differences(mine, theirs) if fam == "smt"
             else _differences(fam, mine, theirs))
    out = {"same": not diffs, "family": fam, "differences": diffs,
           "fingerprint": None}
    if fam in WHOLE:
        out["fingerprint"] = {"certificate": _digest(fam, mine),
                              "spec": _digest(fam, theirs)}
    return out


def _differences(fam, mine, theirs) -> list:
    out = []
    for key in mine:
        a, b = mine[key], theirs.get(key)
        if a == b:
            continue
        if key in ("equations", "A", "b", "c", "names") and isinstance(a, list) \
                and isinstance(b, list):
            if len(a) != len(b):
                out.append(t("obligation.count", what=key, cert=len(a), spec=len(b)))
                continue
            idx = [i for i in range(len(a)) if a[i] != b[i]]
            shown = ", ".join(str(i) for i in idx[:6])
            if key == "equations":
                i = idx[0]
                out.append(t("obligation.equation", which=shown,
                             cert=_poly_text(a[i]), spec=_poly_text(b[i])))
            else:
                out.append(t("obligation.rows", what=key, which=shown, n=len(idx)))
            continue
        if key in ("claim", "poly"):
            out.append(t("obligation.claim", cert=_claim_text(a), spec=_claim_text(b)))
            continue
        out.append(t("obligation.part", what=key, cert=_short(a), spec=_short(b)))
    return out


def _smt_differences(mine, theirs) -> list:
    out = []
    spec_f = theirs["formulas"]
    for name, f in mine["formulas"].items():
        if name.startswith("#"):
            continue
        if name == "__goal__":
            if f != spec_f.get("__goal__"):
                out.append(t("obligation.goal"))
            continue
        if name not in spec_f:
            out.append(t("obligation.no_hypothesis", name=name))
        elif spec_f[name] != f:
            out.append(t("obligation.hypothesis", name=name))
    unnamed = [f for n, f in mine["formulas"].items() if n.startswith("#")]
    if unnamed:
        pool = list(spec_f.values())
        missing = [f for f in unnamed if f not in pool]
        if missing:
            out.append(t("obligation.model", n=len(missing)))
    return out


def _short(v) -> str:
    return json.dumps(v, ensure_ascii=False)[:120]
