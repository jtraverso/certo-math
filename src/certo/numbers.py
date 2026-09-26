"""Primality and factorisation, with certificates anyone can check.

A Pratt certificate is the cleanest example of the shape this whole tool is
built around: expensive to find, trivial to verify, and the verification needs
nothing but modular exponentiation.

`n` is prime exactly when there is a witness `a` with

    a^(n-1) = 1  (mod n)                       and
    a^((n-1)/q) != 1  (mod n)   for every prime q dividing n-1

which makes `a` a generator of (Z/n)^*, so that group has n-1 elements, so n
is prime. The catch, and the reason it is a certificate rather than a test, is
that "every prime q dividing n-1" needs those q to be prime too -- so the
certificate is a TREE, recursing down to 2. Checking the whole tree is a
handful of `pow(a, e, n)` calls.

Compare that with `n.is_prime()`: true, fast, and completely unciteable. The
difference matters exactly when a proof depends on it.

Factorisation is the same idea one level simpler: the certificate is the
factors, checking it is one multiplication, and each factor carries its own
primality certificate so "and these are prime" is not left hanging.
"""
from __future__ import annotations

from .i18n import t

SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def _factor(n: int) -> dict:
    """Prime factorisation. Uses FLINT when it is there, trial division else."""
    if n <= 1:
        return {}
    try:
        from flint import fmpz

        out = {}
        for base, exp in fmpz(n).factor():
            out[int(base)] = int(exp)
        return out
    except ImportError:
        pass
    out, m = {}, n
    d = 2
    while d * d <= m:
        while m % d == 0:
            out[d] = out.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


def _witness(n: int, qs):
    """A generator of (Z/n)^*, found by trying small bases first.

    Trying 2, 3, 5, ... rather than random bases keeps the certificate
    REPRODUCIBLE: the same n gives the same witness on every machine, so two
    runs produce the same digest.
    """
    for a in list(SMALL_PRIMES) + list(range(41, 4000, 2)):
        a %= n
        if a < 2:
            continue
        if pow(a, n - 1, n) != 1:
            continue
        if all(pow(a, (n - 1) // q, n) != 1 for q in qs):
            return a
    return None


def pratt(n: int, depth=0, max_depth=64) -> dict:
    """A Pratt certificate for `n`, recursing into the factors of n-1.

    Raises rather than returning something weaker when n is composite: a
    "certificate" that quietly means "probably" is the failure mode this is
    meant to remove.
    """
    n = int(n)
    if n < 2:
        raise ValueError(t("numbers.not_prime", n=n))
    if depth > max_depth:
        raise RuntimeError(t("numbers.too_deep", n=n))
    if n in (2, 3):
        return {"n": n, "base_case": True}

    qs = sorted(_factor(n - 1))
    a = _witness(n, qs)
    if a is None:
        raise ValueError(t("numbers.not_prime", n=n))
    return {
        "n": n,
        "witness": a,
        "factors": [{"q": q, "cert": pratt(q, depth + 1, max_depth)}
                    for q in qs],
    }


def verify_pratt(cert: dict, checks=None) -> list:
    """Check a Pratt tree. Modular exponentiation and nothing else.

    Returns a flat list of (claim, ok, detail), deepest first, so a failure
    points at the node that broke rather than at the root.
    """
    checks = [] if checks is None else checks
    n = int(cert["n"])

    if cert.get("base_case"):
        checks.append((t("verify.pratt.base", n=n), n in (2, 3), ""))
        return checks

    a = int(cert["witness"])
    qs = [int(f["q"]) for f in cert["factors"]]

    # Every child certifies THE FACTOR IT SITS UNDER, and that factor is a
    # prime divisor of n - 1 of the right size. A valid tree for 2, filed
    # under the factor 8, used to make 9 prime: the child verified, and
    # nothing asked which number it was about.
    untied = [str(f["q"]) for f in cert["factors"]
              if int((f.get("cert") or {}).get("n", -1)) != int(f["q"])
              or int(f["q"]) < 2 or (n - 1) % int(f["q"]) != 0]
    checks.append((t("verify.pratt.tied", n=n), n >= 2 and not untied,
                   ", ".join(untied[:4]) or "-"))
    for f in cert["factors"]:
        verify_pratt(f["cert"], checks)

    # The factor list must be the whole of n-1, or the witness proves nothing:
    # missing a prime factor of n-1 would let a composite n slip through.
    m = n - 1
    for q in qs:
        while m % q == 0:
            m //= q
    checks.append((t("verify.pratt.complete", n=n), m == 1,
                   t("verify.pratt.leftover", m=m)))

    checks.append((t("verify.pratt.fermat", n=n), pow(a, n - 1, n) == 1,
                   "a = {}".format(a)))
    bad = [q for q in qs if pow(a, (n - 1) // q, n) == 1]
    checks.append((t("verify.pratt.order", n=n), not bad,
                   t("verify.pratt.collapsed", qs=", ".join(map(str, bad)))
                   if bad else "{} prime factors".format(len(qs))))
    return checks


# ---------------------------------------------------------------------------
# factorisation
# ---------------------------------------------------------------------------


def factorisation(n: int) -> dict:
    """The factors of n, each with its own primality certificate."""
    n = int(n)
    fac = _factor(n)
    return {
        "n": n,
        "factors": [{"p": p, "e": e, "cert": pratt(p)} for p, e in sorted(fac.items())],
    }


def verify_factorisation(cert: dict) -> list:
    """Multiply it back, then check each factor really is prime."""
    n = int(cert["n"])
    product = 1
    for f in cert["factors"]:
        product *= int(f["p"]) ** int(f["e"])
    checks = [(t("verify.factor.product", n=n), product == n,
               " * ".join("{}^{}".format(f["p"], f["e"])
                          for f in cert["factors"]) or "1")]
    # Each prime's certificate is about THAT prime -- the same hole as the
    # Pratt tree one level up: `9 = 9^1` with a certificate that 2 is prime.
    untied = [str(f["p"]) for f in cert["factors"]
              if int((f.get("cert") or {}).get("n", -1)) != int(f["p"])
              or int(f["p"]) < 2 or int(f["e"]) < 1]
    checks.append((t("verify.factor.tied", n=n), not untied,
                   ", ".join(untied[:4]) or "-"))
    for f in cert["factors"]:
        sub = verify_pratt(f["cert"])
        checks.append((t("verify.factor.prime", p=f["p"]),
                       all(c[1] for c in sub),
                       t("verify.factor.steps", n=len(sub))))
    return checks


# ---------------------------------------------------------------------------
# a modular obstruction
# ---------------------------------------------------------------------------


def modular_obstruction(residue_fn, modulus: int, targets) -> dict:
    """No solution mod m, hence none at all. The cheapest refutation there is.

    Exhausting the residues modulo a small m closes a Diophantine question
    that a solver may chew on forever, and the certificate is a table of m
    entries that anyone can recompute. The direction matters and only goes one
    way: no solution mod m proves no solution in Z, while a solution mod m
    proves nothing.
    """
    hit = sorted({residue_fn(x) % modulus for x in range(modulus)})
    want = sorted({t_ % modulus for t_ in targets})
    return {
        "modulus": modulus,
        "reachable": hit,
        "targets": want,
        "disjoint": not (set(hit) & set(want)),
    }
