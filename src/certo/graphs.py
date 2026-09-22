"""Grafos: tipo minimo, graph6, isomorfismo exacto, enumeracion y filtros.

Sin dependencias externas a proposito. Si `geng` (nauty) esta en el PATH se
usa, porque es varios ordenes de magnitud mas rapido; si no, se enumera por
aumento de vertices con forma canonica exacta, que aguanta comodo hasta n=8.
"""
from __future__ import annotations

import itertools
import shutil
import subprocess
import time
from dataclasses import dataclass


def _pair_index(i: int, j: int) -> int:
    """Indice de bit del par no ordenado {i,j}."""
    if i > j:
        i, j = j, i
    return j * (j - 1) // 2 + i


@dataclass(frozen=True)
class Graph:
    n: int
    bits: int  # mascara de bits sobre los pares {i,j}, i<j

    # -- construccion ------------------------------------------------------

    @classmethod
    def from_edges(cls, n: int, edges) -> "Graph":
        b = 0
        for i, j in edges:
            b |= 1 << _pair_index(i, j)
        return cls(n, b)

    def has_edge(self, i: int, j: int) -> bool:
        return i != j and bool(self.bits >> _pair_index(i, j) & 1)

    def edges(self):
        for j in range(self.n):
            for i in range(j):
                if self.bits >> _pair_index(i, j) & 1:
                    yield (i, j)

    def neighbors(self, v: int) -> set:
        return {u for u in range(self.n) if self.has_edge(u, v)}

    def degree(self, v: int) -> int:
        return len(self.neighbors(v))

    @property
    def m(self) -> int:
        return bin(self.bits).count("1")

    def permuted(self, perm) -> "Graph":
        """perm[v] = nueva etiqueta del vertice v."""
        b = 0
        for i, j in self.edges():
            b |= 1 << _pair_index(perm[i], perm[j])
        return Graph(self.n, b)

    # -- graph6 ------------------------------------------------------------

    def to_graph6(self) -> str:
        if self.n > 62:
            raise ValueError("graph6 simple solo hasta n=62")
        out = [chr(self.n + 63)]
        bitstr = []
        for j in range(self.n):
            for i in range(j):
                bitstr.append("1" if self.has_edge(i, j) else "0")
        while len(bitstr) % 6:
            bitstr.append("0")
        for k in range(0, len(bitstr), 6):
            out.append(chr(int("".join(bitstr[k : k + 6]), 2) + 63))
        return "".join(out)

    @classmethod
    def from_graph6(cls, s: str) -> "Graph":
        s = s.strip()
        n = ord(s[0]) - 63
        if n > 62:
            raise ValueError("graph6 simple solo hasta n=62")
        bitstr = "".join(format(ord(c) - 63, "06b") for c in s[1:])
        b, k = 0, 0
        for j in range(n):
            for i in range(j):
                if k < len(bitstr) and bitstr[k] == "1":
                    b |= 1 << _pair_index(i, j)
                k += 1
        return cls(n, b)

    def __str__(self) -> str:
        return "Graph(n={}, m={}, g6={})".format(self.n, self.m, self.to_graph6())


# ---------------------------------------------------------------------------
# isomorfismo: refinamiento 1-WL + forma canonica exacta dentro de las clases
# ---------------------------------------------------------------------------


def wl_colors(g: Graph) -> list:
    """Refinamiento de color 1-WL. Devuelve un color entero por vertice."""
    colors = [g.degree(v) for v in range(g.n)]
    for _ in range(g.n):
        sig = [
            (colors[v], tuple(sorted(colors[u] for u in g.neighbors(v))))
            for v in range(g.n)
        ]
        table = {s: k for k, s in enumerate(sorted(set(sig)))}
        new = [table[s] for s in sig]
        if new == colors:
            break
        colors = new
    return colors


def wl_signature(g: Graph):
    """Invariante barato para agrupar. NO es completo: colisiona a proposito."""
    return (g.n, g.m, tuple(sorted(wl_colors(g))))


def canonical_form(g: Graph) -> tuple:
    """Forma canonica EXACTA.

    Un isomorfismo preserva los colores 1-WL, asi que basta minimizar sobre
    las permutaciones que respetan las clases de color: normalmente son
    poquisimas. En el peor caso (grafos regulares) degenera a n!, tolerable
    para n<=8.
    """
    colors = wl_colors(g)
    classes: dict = {}
    for v in range(g.n):
        classes.setdefault(colors[v], []).append(v)
    ordered = [classes[c] for c in sorted(classes)]

    best = None
    slots, base = [], 0
    for grp in ordered:
        slots.append(list(range(base, base + len(grp))))
        base += len(grp)

    for combo in itertools.product(*[itertools.permutations(s) for s in slots]):
        perm = [0] * g.n
        for grp, targets in zip(ordered, combo):
            for v, t in zip(grp, targets):
                perm[v] = t
        cand = g.permuted(perm).bits
        if best is None or cand < best:
            best = cand
    return (g.n, best)


def is_isomorphic(g: Graph, h: Graph) -> bool:
    if g.n != h.n or g.m != h.m:
        return False
    return canonical_form(g) == canonical_form(h)


# ---------------------------------------------------------------------------
# filtros
# ---------------------------------------------------------------------------


def is_connected(g: Graph) -> bool:
    if g.n == 0:
        return True
    seen, stack = {0}, [0]
    while stack:
        v = stack.pop()
        for u in g.neighbors(v):
            if u not in seen:
                seen.add(u)
                stack.append(u)
    return len(seen) == g.n


def is_chordal(g: Graph) -> bool:
    """Busqueda de cardinalidad maxima + comprobacion del orden de eliminacion."""
    n = g.n
    weight = [0] * n
    numbered = [False] * n
    order = []
    for _ in range(n):
        v = max((x for x in range(n) if not numbered[x]), key=lambda x: weight[x])
        numbered[v] = True
        order.append(v)
        for u in g.neighbors(v):
            if not numbered[u]:
                weight[u] += 1
    order.reverse()  # orden de eliminacion perfecta candidato
    pos = {v: i for i, v in enumerate(order)}
    for v in order:
        later = [u for u in g.neighbors(v) if pos[u] > pos[v]]
        if not later:
            continue
        w = min(later, key=lambda u: pos[u])
        for u in later:
            if u != w and not g.has_edge(w, u):
                return False
    return True


def _has_clique(g: Graph, k: int) -> bool:
    return any(
        all(g.has_edge(a, b) for a, b in itertools.combinations(c, 2))
        for c in itertools.combinations(range(g.n), k)
    )


def is_triangle_free(g: Graph) -> bool:
    return not _has_clique(g, 3)


def is_k4_free(g: Graph) -> bool:
    return not _has_clique(g, 4)


def is_regular(g: Graph) -> bool:
    return len({g.degree(v) for v in range(g.n)}) <= 1


_BASE_FILTERS = {
    "connected": is_connected,
    "chordal": is_chordal,
    "triangle_free": is_triangle_free,
    "k4_free": is_k4_free,
    "regular": is_regular,
    "has_triangle": lambda g: _has_clique(g, 3),
}


class _FilterRegistry:
    """Resuelve nombres simples y parametrizados: 'chordal', 'min_degree=2'."""

    def get(self, spec: str):
        if "=" in spec:
            name, val = spec.split("=", 1)
            try:
                k = int(val)
            except ValueError:
                return None
            if name == "min_degree":
                return lambda g: all(g.degree(v) >= k for v in range(g.n))
            if name == "max_degree":
                return lambda g: all(g.degree(v) <= k for v in range(g.n))
            if name == "edges":
                return lambda g: g.m == k
            return None
        return _BASE_FILTERS.get(spec)

    def names(self):
        return sorted(_BASE_FILTERS) + ["min_degree=K", "max_degree=K", "edges=K"]


FILTERS = _FilterRegistry()


def filter_name(spec) -> str:
    """Stable id for a filter, named or programmable."""
    if isinstance(spec, str):
        return spec
    return "fn:" + getattr(spec, "__name__", "<lambda>")


def compile_filters(specs):
    """Accepts names and CALLABLES.

    A programmable filter cannot be re-checked from a certificate alone -- it
    lives in the spec, not in the catalogue. It is recorded as `fn:<name>` and
    verification says so instead of pretending.
    """
    fns = []
    for s in specs or []:
        if callable(s):
            fns.append((filter_name(s), s))
            continue
        f = FILTERS.get(s)
        if f is None:
            from .i18n import t

            raise ValueError(t("spec.unknown_filter", name=s,
                               available=", ".join(FILTERS.names())))
        fns.append((s, f))
    return fns


# ---------------------------------------------------------------------------
# enumeracion
# ---------------------------------------------------------------------------


def _geng_path():
    return shutil.which("geng")


class WorkBudget(RuntimeError):
    """`geng` was stopped by a bound instead of finishing.

    THE PARTIAL OUTPUT IS DISCARDED, always. A truncated enumeration looks
    exactly like a complete one -- a list of graphs -- and `sweep` would go on
    to report "every graph on n vertices satisfies the predicate" having seen
    a prefix of them. That is not a slow answer, it is a wrong one, and it is
    the single failure this tool exists to prevent. So exceeding a bound is an
    ERROR that propagates, never a shorter list.
    """

    def __init__(self, reason: str, detail: str = ""):
        super().__init__(detail or reason)
        self.reason = reason          # "timeout" | "output"


def _run_geng(args, timeout_s: float, max_bytes: int) -> str:
    """Run `geng`, reading it as it goes and stopping if it exceeds a bound.

    `subprocess.run(capture_output=True)` was what this used to be, and it
    buffers the whole of stdout before anyone can look at it: at n=12 that is
    more than the machine has, so the bound has to be enforced DURING the
    read, not after it.

    One limitation, stated because it is real: the clock is checked once per
    line, so a `geng` that produced nothing at all would not be noticed until
    it did. `geng` emits steadily and the pathological cases here are large
    rather than silent, so the remaining exposure is the final `wait`, which
    is bounded separately.
    """
    proc = subprocess.Popen(args, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    lines, size = [], 0
    deadline = time.monotonic() + timeout_s
    try:
        for line in proc.stdout:
            size += len(line)
            if size > max_bytes:
                raise WorkBudget(
                    "output",
                    "geng produced more than {} MB of graphs before any could "
                    "be used".format(max_bytes // (1024 * 1024)))
            if time.monotonic() > deadline:
                raise WorkBudget(
                    "timeout",
                    "geng ran longer than {}s".format(int(timeout_s)))
            lines.append(line)
        left = max(1.0, deadline - time.monotonic())
        try:
            code = proc.wait(timeout=left)
        except subprocess.TimeoutExpired:
            raise WorkBudget("timeout",
                             "geng ran longer than {}s".format(int(timeout_s)))
        if code != 0:
            err = (proc.stderr.read() or "").strip()
            raise subprocess.CalledProcessError(code, args, stderr=err)
    finally:
        # Kill before close: closing the pipe on a still-running geng leaves
        # it writing into a broken pipe rather than ending it.
        if proc.poll() is None:
            proc.kill()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
        for stream in (proc.stdout, proc.stderr):
            try:
                stream.close()
            except Exception:
                pass
    return "".join(lines)


def enumerate_graphs(n: int, filters=None, use_geng: bool = True,
                     connected_only=False, limits=None):
    """Todos los grafos con n vertices salvo isomorfismo, filtrados.

    Devuelve (lista_filtrada, motor_usado, total_antes_de_filtrar).

    `limits` acota la enumeracion externa. Es opcional y su ausencia NO
    significa "sin cota": se usan los valores por defecto de `Limits`, porque
    el caso que motivo esto es precisamente el de quien no paso nada.
    """
    from .limits import Limits

    lim = limits or Limits()
    fns = compile_filters(filters)
    geng = _geng_path() if use_geng else None

    if geng:
        args = [geng, "-q"]
        if connected_only or any(s == "connected" for s, _ in fns):
            args.append("-c")
        args.append(str(n))
        out = _run_geng(args, lim.enumerate_timeout_s,
                        lim.max_output_mb * 1024 * 1024)
        cands = [Graph.from_graph6(line) for line in out.split() if line]
        engine = "nauty/geng"
    else:
        cands = _augment(n)
        engine = "augmentation (python)"

    keep = [g for g in cands if all(f(g) for _, f in fns)]
    return keep, engine, len(cands)


def _augment(n: int):
    """Genera todos los grafos hasta isomorfismo aumentando un vertice cada vez.

    Correcto y completo: todo grafo con k+1 vertices, al quitarle el ultimo
    vertice, deja un grafo con k vertices que ya esta en el nivel anterior.
    """
    level = [Graph(1, 0)]
    for k in range(1, n):
        seen: dict = {}
        for g in level:
            for r in range(k + 1):
                for s in itertools.combinations(range(k), r):
                    b = g.bits
                    for v in s:
                        b |= 1 << _pair_index(v, k)
                    cand = Graph(k + 1, b)
                    key = canonical_form(cand)
                    if key not in seen:
                        seen[key] = cand
        level = list(seen.values())
    return level
