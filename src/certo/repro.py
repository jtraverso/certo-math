"""Everything a referee needs, in one directory, checkable with nothing else.

The pieces have existed for a while and lived in four commands and a
convention: provenance on each certificate, `status` across a directory,
`verify` per file, the ledger. Somebody assembling a paper appendix had to
know all four and the order to run them in.

This is that, done once, with two rules that make it worth doing at all.

  NOTHING INVALID GOES IN. Every certificate is verified on the way, and one
  that fails is left out and named. A bundle containing a certificate that
  does not check is worse than no bundle: it looks like evidence and is not,
  and the person who finds out is the referee.

  NOTHING UNTIED GOES IN QUIETLY. A certificate names its spec by path and by
  hash. When the file on disk still matches, it is copied in and the bundle is
  self-contained. When it has moved on, the certificate still goes in -- it is
  valid, and its own verification never needed the spec -- but the manifest
  says the source could not be included and why, because a bundle that
  silently shipped a different file would be the worst failure available here.

What comes out is a directory, a MANIFEST.json with a sha256 for every file in
it, and a README that tells a stranger the one command to run.
"""
from __future__ import annotations

import hashlib
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path

from .i18n import t as _t


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bundle(where, out, limits=None, include_ledger=True) -> dict:
    """Verify everything under `where`, and assemble what passes into `out`."""
    from . import __version__
    from .certificate import SCHEMA_VERSION, Certificate
    from .certificate import verify as verify_cert
    src, dest = Path(where), Path(out)
    dest.mkdir(parents=True, exist_ok=True)
    certs_dir = dest / "certificates"
    specs_dir = dest / "specs"
    certs_dir.mkdir(exist_ok=True)

    included, refused, specs, untied = [], [], {}, []
    from . import store

    for entry in _all_certificates(src):
        ref, data = entry
        container, member = store.split_ref(ref)
        # A file keeps its bytes (and its name); a member of an archive is
        # written out as the plain JSON it is.
        path = Path(container) if member is None else Path(member)
        cert = Certificate.from_dict(data)
        rep = verify_cert(cert, limits)
        if not rep.ok:
            # Named, not hidden. The reason somebody built a bundle is to
            # stop having to take things on trust.
            refused.append({"file": path.name, "kind": cert.kind,
                            "why": [n for n, ok, _ in rep.checks if not ok]
                                   or [rep.detail]})
            continue

        target = certs_dir / path.name
        n = 1
        while target.exists():
            target = certs_dir / "{}_{}{}".format(path.stem, n, path.suffix)
            n += 1
        if member is None:
            shutil.copy2(path, target)
        else:
            target = target.with_suffix(".json") if not target.name.endswith(
                ".json") else target
            store.write_certificate(cert, target)
        included.append({"file": "certificates/" + target.name,
                         "kind": cert.kind,
                         "digest": cert.digest(),
                         "solver_free": bool(cert.solver_free),
                         "sha256": _sha256(target)})

        prov = cert.provenance or {}
        spec_path, spec_hash = prov.get("spec_path"), prov.get("spec_sha256")
        if not spec_path:
            continue
        source = Path(spec_path)
        if not source.is_absolute():
            source = (src / source) if (src / source).is_file() else source
        if source.is_file() and (not spec_hash or _sha256(source) == spec_hash):
            specs_dir.mkdir(exist_ok=True)
            spec_target = specs_dir / source.name
            if not spec_target.exists():
                shutil.copy2(source, spec_target)
                specs[source.name] = _sha256(spec_target)
        else:
            untied.append({"file": "certificates/" + target.name,
                           "spec": spec_path,
                           "why": "gone" if not source.is_file() else "changed"})

    if include_ledger:
        for name in ("ledger.jsonl",):
            led = src / name
            if led.is_file():
                shutil.copy2(led, dest / name)

    manifest = {
        "certo_version": __version__,
        "schema": SCHEMA_VERSION,
        "created": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source": str(src),
        "certificates": included,
        "specs": [{"file": "specs/" + k, "sha256": v}
                  for k, v in sorted(specs.items())],
        "refused": refused,
        "specs_not_included": untied,
        "solver_free": sum(1 for c in included if c["solver_free"]),
    }
    (dest / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    manifest["manifest_sha256"] = _sha256(dest / "MANIFEST.json")

    (dest / "README.md").write_text(_readme(manifest), encoding="utf-8")
    return manifest


def _all_certificates(src: Path):
    """Every certificate under `src`, whichever shape it was written in."""
    from .certificate import Certificate

    from . import store

    for ref, _rel, raw in store.walk(src):
        if Path(store.split_ref(ref)[0]).name == "MANIFEST.json":
            continue
        if raw is None:
            continue
        data = Certificate.unwrap(raw) if isinstance(raw, dict) else None
        if isinstance(data, dict) and "kind" in data:
            yield ref, data


def _readme(m: dict) -> str:
    """One command for a stranger, and what the bundle does not claim."""
    kinds = {}
    for c in m["certificates"]:
        kinds[c["kind"]] = kinds.get(c["kind"], 0) + 1
    lines = [
        _t("repro.title"),
        "",
        _t("repro.made", version=m["certo_version"], schema=m["schema"],
           when=m["created"]),
        "",
        _t("repro.contents", n=len(m["certificates"]),
           kinds=", ".join("{} {}".format(v, k)
                           for k, v in sorted(kinds.items())) or "-",
           free=m["solver_free"]),
        "",
        "```bash",
        "pip install certo",
        "for c in certificates/*.json; do certo verify \"$c\"; done",
        "```",
        "",
        _t("repro.free_note", free=m["solver_free"],
           total=len(m["certificates"])),
        "",
    ]
    if m["specs"]:
        lines += [_t("repro.specs", n=len(m["specs"])), ""]
    if m["specs_not_included"]:
        lines += [_t("repro.untied", n=len(m["specs_not_included"])), ""]
        for u in m["specs_not_included"]:
            lines.append("* `{}` -- {} ({})".format(u["file"], u["spec"],
                                                    u["why"]))
        lines.append("")
    if m["refused"]:
        lines += [_t("repro.refused", n=len(m["refused"])), ""]
        for r in m["refused"]:
            lines.append("* {} ({}): {}".format(r["file"], r["kind"],
                                                "; ".join(r["why"][:2])))
        lines.append("")
    lines += [_t("repro.scope"), ""]
    return "\n".join(lines)
