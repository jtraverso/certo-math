"""The Lean declaration a binding names, read by Lean itself.

`bind` checked `provides => hypothesis`, and `provides` was a transcription
the user wrote: nothing read the declaration, so a correct identity bound to
the wrong theorem, or to one whose statement had since changed, bound just
the same. Two things are now read from Lean, in ONE elaboration (Mathlib
takes minutes to import):

  * the declaration's ELABORATED TYPE, as Lean prints it, its hash, and the
    axioms it depends on (`sorryAx` among them is a declaration that proves
    nothing);
  * whether that type IS the type of certo's own export of the bound
    certificate: `theorem CertoBindCheck.same : type_of% @D = type_of% @E :=
    rfl`, with `E` the export regenerated now. The kernel accepting it --
    definitional equality, binder names aside -- is the correspondence
    `kernel_checked`. Anything else is `user_asserted`: the transcription is
    the user's, and the recorded hash still catches a statement that moves.

Nothing here is believed by `verify` without Lean: what it records is shown
as recorded, and `verify --elaborate` (or `CERTO_LEAN_ELABORATE=1`) runs the
same elaboration again and refuses a type that changed.
"""
from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

CHECK_NAME = "CertoBindCheck.target"
SAME_NAME = "CertoBindCheck.same"
_BEGIN, _END = "CERTO_TYPE_BEGIN", "CERTO_TYPE_END"


def lean_version(project) -> str | None:
    lake = shutil.which("lake")
    if not lake:
        return None
    try:
        out = subprocess.run([lake, "env", "lean", "--version"], cwd=str(project),
                             capture_output=True, text=True, timeout=120,
                             encoding="utf-8", errors="replace")
        return (out.stdout or "").strip().splitlines()[0] if out.stdout else None
    except (OSError, subprocess.SubprocessError, IndexError):
        return None


def _split_imports(text):
    imports, rest = [], []
    for line in (text or "").splitlines():
        (imports if line.startswith("import ") else rest).append(line)
    return imports, rest


def elaborate(project, declaration, lean_file=None, module=None,
              export_text=None, timeout=1800) -> dict:
    """One Lean run: the declaration's type and axioms, and -- with
    `export_text` -- whether its type is the export's. `{"ran": False,
    "reason"}` when there is no toolchain or project."""
    lake = shutil.which("lake")
    if not lake:
        return {"ran": False, "reason": "no `lake` on PATH"}
    root = Path(project)
    if not ((root / "lakefile.lean").exists() or (root / "lakefile.toml").exists()):
        return {"ran": False, "reason": "no Lean project at {}".format(root)}
    if lean_file:
        body = Path(lean_file).read_text(encoding="utf-8")
    elif module:
        body = "import {}\n".format(module)
    else:
        return {"ran": False, "reason": "name a lean_file or a lean_module"}
    i1, r1 = _split_imports(body)
    i2, r2 = _split_imports(export_text) if export_text else ([], [])
    imports = list(dict.fromkeys(i1 + i2))
    lines = imports + [""] + r1 + [""] + r2 + [
        "",
        '#eval IO.println "{}"'.format(_BEGIN),
        "#check @{}".format(declaration),
        '#eval IO.println "{}"'.format(_END),
        "#print axioms {}".format(declaration),
    ]
    if export_text:
        lines += [
            "theorem {} : (type_of% @{}) = (type_of% @{}) := rfl".format(
                SAME_NAME, declaration, CHECK_NAME),
            "#print axioms {}".format(SAME_NAME),
        ]
    with tempfile.TemporaryDirectory(prefix="certo_bind_") as d:
        f = Path(d) / "CertoBindProbe.lean"
        f.write_text("\n".join(lines) + "\n", encoding="utf-8")
        try:
            out = subprocess.run([lake, "env", "lean", str(f)], cwd=str(root),
                                 capture_output=True, text=True, timeout=timeout,
                                 encoding="utf-8", errors="replace")
        except (OSError, subprocess.SubprocessError) as e:
            return {"ran": False, "reason": "{}: {}".format(type(e).__name__, e)}
    text = (out.stdout or "") + "\n" + (out.stderr or "")
    return parse(text, declaration, bool(export_text))


def parse(text, declaration, with_export) -> dict:
    """What one elaboration said, from its output."""
    out = {"ran": True}
    m = re.search(re.escape(_BEGIN) + r"\s*(.*?)\s*" + re.escape(_END), text, re.S)
    typ = None
    if m:
        block = " ".join(m.group(1).split())
        prefix = declaration + " : "
        # Only a type when Lean printed one: an error between the markers
        # (an unknown constant) is not the declaration's type.
        typ = block[len(prefix):] if block.startswith(prefix) else None
    out["type"] = typ
    out["type_sha256"] = hashlib.sha256(typ.encode()).hexdigest() if typ else None
    ax = re.search(r"'" + re.escape(declaration) + r"' depends on axioms: \[(.*?)\]",
                   text, re.S)
    if ax:
        out["axioms"] = [a.strip() for a in ax.group(1).split(",") if a.strip()]
    elif re.search(r"'" + re.escape(declaration) + r"' does not depend on any axioms",
                   text):
        out["axioms"] = []
    else:
        out["axioms"] = None
    if with_export:
        # Lean ADDS a declaration that failed to elaborate, closed by `sorry`:
        # so "depends on axioms" alone is printed for a type mismatch too.
        # The equality counts only without `sorryAx`.
        same = re.search(r"'" + re.escape(SAME_NAME) +
                         r"' depends on axioms: \[(.*?)\]", text, re.S)
        free = re.search(r"'" + re.escape(SAME_NAME) +
                         r"' does not depend on any axioms", text)
        out["same_type"] = bool(free) or bool(same and "sorryAx" not in same.group(1))
    errors = [l for l in text.splitlines() if ": error:" in l]
    out["errors"] = errors[:8]
    return out


def correspondence(result) -> str:
    """`kernel_checked` only when Lean accepted the type equality with the
    export AND the declaration does not rest on `sorryAx`."""
    if (result.get("ran") and result.get("same_type")
            and result.get("axioms") is not None
            and "sorryAx" not in (result.get("axioms") or [])):
        return "kernel_checked"
    return "user_asserted"


def wanted() -> bool:
    return os.environ.get("CERTO_LEAN_ELABORATE", "").strip() not in ("", "0")
