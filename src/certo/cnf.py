"""CNF con variables por nombre, DIMACS, y codificaciones de apoyo.

Las variables se piden por nombre y el objeto lleva la traduccion a enteros
DIMACS. Asi el certificado puede volver a imprimir un modelo legible sin la
sesion de Python que lo produjo.
"""
from __future__ import annotations

from dataclasses import dataclass, field


class CNF:
    def __init__(self, title: str = ""):
        self.title = title
        self._id: dict = {}          # nombre -> entero positivo
        self._name: list = [None]    # entero -> nombre (1-indexado)
        self.clauses: list = []
        self._aux = 0

    # -- variables ---------------------------------------------------------

    def var(self, name) -> int:
        name = str(name)
        v = self._id.get(name)
        if v is None:
            v = len(self._name)
            self._id[name] = v
            self._name.append(name)
        return v

    def aux(self, tag="aux") -> int:
        self._aux += 1
        return self.var("__{}_{}".format(tag, self._aux))

    def name_of(self, v: int) -> str:
        return self._name[abs(v)]

    @property
    def nvars(self) -> int:
        return len(self._name) - 1

    # -- clausulas ---------------------------------------------------------

    def add(self, *lits) -> "CNF":
        """Anade una clausula. Normaliza: quita repetidos, descarta tautologias."""
        flat: list = []
        for x in lits:
            flat.extend(x) if isinstance(x, (list, tuple)) else flat.append(x)
        seen = set()
        cl = []
        for l in flat:
            if l == 0:
                raise ValueError("0 no es un literal valido")
            if -l in seen:
                return self  # tautologia: no aporta nada
            if l not in seen:
                seen.add(l)
                cl.append(int(l))
        self.clauses.append(cl)
        return self

    def add_all(self, clauses) -> "CNF":
        for c in clauses:
            self.add(*c)
        return self

    # -- codificaciones ----------------------------------------------------

    def at_least_one(self, lits) -> "CNF":
        return self.add(*lits)

    def at_most_one(self, lits) -> "CNF":
        """Pairwise. Cuadratica, pero exacta y sin variables auxiliares."""
        lits = list(lits)
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                self.add(-lits[i], -lits[j])
        return self

    def exactly_one(self, lits) -> "CNF":
        lits = list(lits)
        return self.at_least_one(lits).at_most_one(lits)

    def at_most_k(self, lits, k: int) -> "CNF":
        """A lo sumo `k` de `lits`. Contador secuencial: O(n*k) clausulas.

        El encaje pairwise de "a lo sumo k" es C(n, k+1), no cuadratico: con
        35 literales y k=6 son 6.724.520 clausulas, que es donde se descubrio.
        Este es el codificador secuencial de Sinz, con s[i][j] leyendose "de
        los primeros i literales hay al menos j verdaderos".

        Las auxiliares llevan el nombre del contador, no un numero, para que
        una prueba DRAT sobre esta formula se pueda leer.
        """
        lits = list(lits)
        if k < 0:
            raise ValueError("un tope negativo no es una restriccion")
        if k == 0:
            for x in lits:
                self.add(-x)
            return self
        if k >= len(lits):
            return self                     # no restringe nada
        if k == 1:
            return self.at_most_one(lits)

        n = len(lits)
        tag = self._aux
        self._aux += 1
        s = [[self.var("__count{}_{}_{}".format(tag, i, j))
              for j in range(k)] for i in range(n - 1)]

        self.add(-lits[0], s[0][0])
        for j in range(1, k):
            self.add(-s[0][j])
        for i in range(1, n - 1):
            self.add(-lits[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, k):
                self.add(-lits[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-lits[i], -s[i - 1][k - 1])
        self.add(-lits[n - 1], -s[n - 2][k - 1])
        return self

    def implies(self, a, b) -> "CNF":
        return self.add(-a, b)

    def lex_leq(self, xs, ys) -> "CNF":
        """Fuerza (x_1..x_k) <=lex (y_1..y_k). La base para romper simetrias."""
        xs, ys = list(xs), list(ys)
        if len(xs) != len(ys):
            raise ValueError("lex_leq necesita dos vectores de la misma longitud")
        eq = self.aux("lexeq")
        self.add(eq)  # e_0 = verdadero
        for i, (x, y) in enumerate(zip(xs, ys)):
            # e_i -> (x_i <= y_i)
            self.add(-eq, -x, y)
            if i == len(xs) - 1:
                break
            nxt = self.aux("lexeq")
            # nxt <-> eq AND (x_i <-> y_i)
            self.add(-nxt, eq)
            self.add(-nxt, -x, y)
            self.add(-nxt, x, -y)
            self.add(nxt, -eq, x, y)
            self.add(nxt, -eq, -x, -y)
            eq = nxt
        return self

    def break_vertex_symmetry(self, edge_var, n, mode="transpositions") -> "CNF":
        """Rompe simetrias de vertices sobre variables de arista.

        `edge_var(i, j)` devuelve el literal de la arista {i,j}. Con
        transposiciones adyacentes el corte es parcial pero barato: es lo
        estandar cuando el grupo completo es demasiado grande.
        """
        pairs = [(i, j) for j in range(n) for i in range(j)]
        if mode != "transpositions":
            raise ValueError("modo no soportado: " + mode)
        for t in range(n - 1):
            perm = list(range(n))
            perm[t], perm[t + 1] = perm[t + 1], perm[t]
            xs = [edge_var(i, j) for i, j in pairs]
            ys = [edge_var(*sorted((perm[i], perm[j]))) for i, j in pairs]
            self.lex_leq(xs, ys)
        return self

    # -- DIMACS ------------------------------------------------------------

    def to_dimacs(self) -> str:
        out = []
        if self.title:
            out.append("c " + self.title.replace("\n", " "))
        for v in range(1, len(self._name)):
            out.append("c var {} {}".format(v, self._name[v]))
        out.append("p cnf {} {}".format(self.nvars, len(self.clauses)))
        for cl in self.clauses:
            out.append(" ".join(map(str, cl)) + " 0")
        return "\n".join(out) + "\n"

    @classmethod
    def from_dimacs(cls, text: str) -> "CNF":
        """DIMACS as a STREAM of literals, each clause ended by `0`.

        It was read line by line, dropping a line with no literal before its
        `0` -- and that line is the EMPTY CLAUSE, which makes the formula
        unsatisfiable. `p cnf 1 1` / `0` read as no clauses at all, and a
        model of nothing verified as a model of an unsatisfiable formula.
        Two clauses on one line (`1 0 2 0`) became one clause with a literal
        0 in it. Now a `0` closes a clause wherever it is, an empty one
        included, and the header is recorded so a verifier can refuse a file
        that is not what it declares (`declared`, `read`).
        """
        c = cls()
        names: dict = {}
        current: list = []
        read = 0
        c.declared = None
        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            if line.startswith("c var "):
                parts = line.split(None, 3)
                if len(parts) == 4:
                    names[int(parts[2])] = parts[3]
                continue
            if line.startswith("c"):
                if not c.title:
                    c.title = line[1:].strip()
                continue
            if line.startswith("p"):
                head = line.split()
                if len(head) != 4 or head[1] != "cnf":
                    raise ValueError("not a DIMACS CNF header: " + line)
                nv, nc = int(head[2]), int(head[3])
                c.declared = (nv, nc)
                for v in range(1, nv + 1):
                    c.var(names.get(v, "x{}".format(v)))
                continue
            if line.startswith("%"):
                break                      # the SATLIB end marker
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    for l in current:
                        while c.nvars < abs(l):
                            c.var("x{}".format(c.nvars + 1))
                    c.add(*current)        # [] is the empty clause: kept
                    read += 1
                    current = []
                else:
                    current.append(lit)
        if current:
            raise ValueError("the last clause is not ended by 0: "
                             + " ".join(map(str, current)))
        c.read = read
        return c

    def matches_header(self) -> bool:
        """Did the file hold the clauses its `p cnf V C` line declares? A
        tautology the reader drops still counts as read. True when there was
        no header to compare."""
        declared = getattr(self, "declared", None)
        if declared is None:
            return True
        nv, nc = declared
        top = max((abs(l) for cl in self.clauses for l in cl), default=0)
        return getattr(self, "read", len(self.clauses)) == nc and top <= nv

    def decode(self, true_vars) -> dict:
        """{nombre: bool} legible, saltando las auxiliares."""
        t = set(true_vars)
        return {
            self._name[v]: (v in t)
            for v in range(1, len(self._name))
            if not self._name[v].startswith("__")
        }


@dataclass
class CNFSpec:
    """Lo que devuelve spec() para `cases`."""

    cnf: CNF
    title: str = ""
    expect: str = ""  # 'unsat' o 'sat', opcional: solo documenta la intencion
    meta: dict = field(default_factory=dict)
