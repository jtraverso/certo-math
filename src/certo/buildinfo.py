"""What THIS certo is: a commit, whether its tree was clean, when it was built.

An installed wheel has no git, and `certo --version` said "not a checkout"
for every one of them: two wheels of one version, one built from a tree with
uncommitted edits, answered the same. The build now writes `_build.json` into
the package (see `setup.py`); a checkout is still read from git, at run time.

    build_info() -> {"source": "build" | "checkout" | "unknown",
                     "commit": full hash or None, "clean": bool or None,
                     "built": "YYYY-MM-DDTHH:MM:SSZ" or None}
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _git(*args):
    try:
        out = subprocess.run(["git", *args], cwd=str(HERE), capture_output=True,
                             text=True, timeout=5)
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout.strip() if out.returncode == 0 else None


def build_info() -> dict:
    shipped = HERE / "_build.json"
    if shipped.is_file():
        try:
            data = json.loads(shipped.read_text(encoding="utf-8"))
            return {"source": "build", "commit": data.get("commit"),
                    "clean": data.get("clean"), "built": data.get("built")}
        except (OSError, ValueError):
            pass
    commit = _git("rev-parse", "HEAD")
    if commit:
        dirty = _git("status", "--porcelain", "--untracked-files=no")
        return {"source": "checkout", "commit": commit,
                "clean": None if dirty is None else dirty == "", "built": None}
    return {"source": "unknown", "commit": None, "clean": None, "built": None}


def describe(info=None) -> str:
    """`32f0068, clean tree, built 2026-11-02` -- the words `--version` uses."""
    from .i18n import t

    info = info or build_info()
    if not info.get("commit"):
        return t("cli.version.no_commit")
    parts = [info["commit"][:7]]
    if info.get("clean") is True:
        parts.append(t("cli.version.clean"))
    elif info.get("clean") is False:
        parts.append(t("cli.version.dirty"))
    if info.get("built"):
        parts.append(t("cli.version.built", date=info["built"][:10]))
    elif info.get("source") == "checkout":
        parts.append(t("cli.version.checkout"))
    return ", ".join(parts)
