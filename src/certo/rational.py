"""The fast exact rational, where one is installed.

`gmpy2.mpq` is GMP's rational: the same exact arithmetic as `Fraction`,
about five times faster on the sums of products a simplex pivot is made of
-- measured on 20 000 multiply-adds -- and the exact simplex spent most of
its time in `Fraction`. Used INSIDE the loops that pay for it; what they
return is `Fraction` again, so nothing outside sees a second type.

`CERTO_NO_GMPY=1` keeps `Fraction` everywhere (read at import).
"""
from __future__ import annotations

import os
from fractions import Fraction


def _mpq():
    if os.environ.get("CERTO_NO_GMPY", "").strip() not in ("", "0"):
        return None
    try:
        import gmpy2

        return gmpy2.mpq
    except Exception:  # noqa: BLE001 -- absent or broken: Fraction
        return None


#: The rational type the hot loops compute in.
Q = _mpq() or Fraction


def to_fraction(x) -> Fraction:
    """Back to `Fraction`, exactly."""
    if isinstance(x, Fraction):
        return x
    return Fraction(int(x.numerator), int(x.denominator))


def fast() -> bool:
    return Q is not Fraction
