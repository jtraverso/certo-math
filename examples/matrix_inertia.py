"""The inertia of a symmetric rational matrix, by congruence.

How many eigenvalues of `A + diag(delta)` are positive? Floating point gives a
count that depends on a tolerance near zero; an exact count needs no
tolerance, and a certificate needs no trust:

    S . A . S^T = D        D diagonal
    S . S_inv   = I        S invertible

By Sylvester's law of inertia the signs of D ARE the inertia of A, and a
verifier multiplies twice and reads a diagonal:

    $ certo matrix examples/matrix_inertia.py
    PROVED  [unsat]
      inertia (2, 2, 0) of a 4 by 4 symmetric matrix, by congruence
      certificate: symmetric_inertia (no solver needed)

The matrix below is the adjacency matrix of a path on four vertices, shifted
by a rational diagonal. Its entries are exact -- "1/2" is one half -- and a
float is refused rather than read, because most floats are not the number
they print.

`psd()` asks the yes-or-no question. This matrix is not PSD, so the answer is
REFUTED, and the certificate carries a vector x with x^T A x < 0: the most
direct evidence there is, and it checks on its own.

For a loop over many matrices, `certo.inertia.signature(rows)` returns the
same three numbers, exact and fast, without a certificate.
"""
from certo import MatrixSpec

A = [
    ["1/2", 1, 0, 0],
    [1, "1/2", 1, 0],
    [0, 1, "-1/2", 1],
    [0, 0, 1, "3/2"],
]


def spec():
    return MatrixSpec(matrix=A, question="inertia",
                      title="a path on four vertices, shifted")


def psd():
    return MatrixSpec(matrix=A, question="psd", title="is it PSD?")
