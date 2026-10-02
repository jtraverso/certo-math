"""Start certo without running the `.pth` hooks of site-packages.

`site` runs every `.pth` file before a line of certo executes, and a line
that begins `import` is code. One such hook, measured on a user's machine,
killed or hung a share of interpreter starts -- empty outputs, hangs past a
deadline -- and `python -S -m certo` ended them. `-S` also drops
site-packages from the path, so on its own it only works where certo happens
to be importable without them.

A launcher written by `certo doctor --launcher DIR` starts Python with `-S`
and puts the site directories back itself, reading each `.pth` for the PATHS
it adds and skipping the lines that run code. It is written on request only,
into a directory the user names, and removing it is deleting one file:
nothing is installed or uninstalled, and the hook -- often there for a
corporate trust store -- keeps working for every other program.
"""
from __future__ import annotations

import os
import sys


def _paths_from_pth(root) -> list:
    import glob

    out = []
    for f in sorted(glob.glob(os.path.join(root, "*.pth"))):
        try:
            text = open(f, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for line in text.splitlines():
            line = line.strip()
            if not line or line.startswith("#") or line.startswith(
                    ("import ", "import\t")):
                continue                      # code, not a path: skipped
            p = line if os.path.isabs(line) else os.path.join(root, line)
            if os.path.isdir(p):
                out.append(os.path.normpath(p))
    return out


def boot(roots) -> int:
    """The launcher's entry: the roots and their `.pth` paths, then certo."""
    for root in roots:
        for p in [root] + _paths_from_pth(root):
            if p not in sys.path:
                sys.path.append(p)
    from .cli import main

    return main(sys.argv[1:])


def launcher_text(roots, python=None, windows=None) -> str:
    """The launcher script: a `.cmd` on Windows, `sh` elsewhere."""
    python = python or sys.executable
    windows = os.name == "nt" if windows is None else windows
    roots = [str(r) for r in roots]
    code = ("import sys; sys.path[:0] = {r!r}; from certo.nosite import boot; "
            "sys.exit(boot({r!r}))").format(r=roots)
    if windows:
        return '@"{}" -S -c "{}" %*\r\n'.format(python, code)
    return '#!/bin/sh\nexec "{}" -S -c "{}" "$@"\n'.format(python, code)


def write_launcher(directory, name="certo-nosite") -> str:
    from pathlib import Path

    from .doctor import _site_roots

    roots = [str(r) for r in _site_roots()
             if r.name.lower() in ("site-packages", "dist-packages")]
    here = str(Path(__file__).resolve().parent.parent)
    if here not in roots:
        roots.insert(0, here)              # certo itself, wherever it lives
    windows = os.name == "nt"
    path = Path(directory) / (name + (".cmd" if windows else ""))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(launcher_text(roots, windows=windows), encoding="utf-8",
                    newline="")
    if not windows:
        path.chmod(0o755)
    return str(path)
