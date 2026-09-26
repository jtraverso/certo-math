"""Auditable log: what was run, what it concluded, and which certificate says so.

Six months later, "we checked that" is worth nothing without the artefact. The
ledger is an append-only JSONL file tying each run to its certificate, the
spec that produced it and the version that ran it -- so a claim in a paper can
be traced back to something re-verifiable.

Two properties it deliberately has:

  * APPEND-ONLY. Entries are never rewritten. A later run that contradicts an
    earlier one is a new line, not an edit; the history is the point.
  * NO COPIES. It stores the certificate's PATH and DIGEST, not the
    certificate. `ledger verify` re-reads and re-verifies each one, so a
    tampered or missing certificate shows up as a failure rather than being
    quietly duplicated into the log.
"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path

DEFAULT_NAME = "ledger.jsonl"


def default_path(workspace=None) -> Path:
    base = Path(workspace) if workspace else Path.cwd()
    return base / DEFAULT_NAME


def append(path, result, cert_path=None, spec_path=None, note="",
           tags=None) -> dict:
    """One line per run. Returns the entry so the caller can show it."""
    cert = result.certificate
    entry = {
        "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "command": result.command,
        "verdict": result.verdict.value,
        "status": result.status.value,
        "conclusive": result.status.conclusive,
        "detail": result.detail,
        "engine": result.engine,
        "elapsed_ms": round(result.elapsed_ms, 1),
        "certificate": None if cert is None else {
            "kind": cert.kind,
            "digest": cert.digest(),
            "solver_free": cert.solver_free,
            "path": str(cert_path) if cert_path else None,
        },
        "spec": str(spec_path) if spec_path else None,
        "spec_sha256": (cert.provenance or {}).get("spec_sha256") if cert else None,
        "certo_version": (cert.provenance or {}).get("certo_version") if cert else None,
        "note": note,
        "tags": list(tags or []),
    }
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, ensure_ascii=False) + "\n")
    return entry


def read(path) -> list:
    p = Path(path)
    if not p.exists():
        return []
    out = []
    for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            out.append({"_corrupt": True, "_line": i, "raw": line[:120]})
    return out


def verify_all(path, limits=None) -> dict:
    """Re-verify every certificate the ledger points at.

    This is the whole point of keeping one: not that a line was written, but
    that what it points at still checks out.
    """
    from .certificate import Certificate
    from .certificate import verify as verify_cert

    rows, counts = [], {"ok": 0, "failed": 0, "missing": 0, "no_cert": 0,
                        "corrupt": 0, "tampered": 0}
    for entry in read(path):
        if entry.get("_corrupt"):
            counts["corrupt"] += 1
            rows.append({"ts": "?", "state": "corrupt",
                         "detail": "unparseable line {}".format(entry["_line"])})
            continue
        # A line can be valid JSON and still be missing fields -- hand-edited,
        # or written by an older version. That must not crash the audit.
        cert_info = entry.get("certificate")
        base = {"ts": entry.get("ts", "?"),
                "command": entry.get("command", "?"),
                "verdict": entry.get("verdict", "?")}
        if not cert_info or not cert_info.get("path"):
            counts["no_cert"] += 1
            rows.append({**base, "state": "no_cert", "detail": ""})
            continue
        from . import store

        p = cert_info["path"]
        if not store.exists(p):
            counts["missing"] += 1
            rows.append({**base, "state": "missing", "detail": str(p)})
            continue
        cert = Certificate.from_dict(store.read_json(p))
        if cert.digest() != cert_info["digest"]:
            # The file at that path is no longer what was logged.
            counts["tampered"] += 1
            rows.append({**base, "state": "changed",
                         "detail": "digest {} != logged {}".format(
                             cert.digest(), cert_info["digest"])})
            continue
        rep = verify_cert(cert, limits)
        counts["ok" if rep.ok else "failed"] += 1
        rows.append({**base, "state": "ok" if rep.ok else "failed",
                     "detail": rep.detail,
                     "warnings": rep.warnings})
    return {"counts": counts, "rows": rows, "total": len(rows)}
