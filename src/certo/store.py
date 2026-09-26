"""Where certificates live on disk: one file, compressed, or many in one archive.

A user ran ~9 000 parametric certificates, 9.4 GB of JSON in one directory,
and listing it took minutes. Measured on eight box certificates of one program
(1.3 MB of JSON): gzip per file is 7.8x smaller in 0.14 s, a zip of them the
same 7.8x in ONE file, and xz 10-13x at fifty times the time. Removing the
program the boxes share bought 1.4x -- it is 12% of a certificate -- and
nothing at all on top of compression, so it is not done.

  * `x.json.gz` is read and written wherever a certificate is: `--cert`,
    `verify`, `atlas`, `status`, `repro`, MCP. The digest is over the content,
    so compressing changes nothing a certificate says.
  * `certo pack DIR -o family.zip` puts a directory's certificates in one zip,
    each member compressed on its own -- so any one of them is read without
    the rest -- with a `manifest.json` naming each member's digest and kind.
    `verify family.zip` checks every member and the manifest; a member is
    named `family.zip#box0412.json` anywhere a path is taken.

Nothing here verifies anything: it moves bytes, and `verify` decides.
"""
from __future__ import annotations

import gzip
import io
import json
import zipfile
from datetime import datetime, timezone
from pathlib import Path

MANIFEST = "manifest.json"


def split_ref(ref):
    """`("archive.zip", "member")` for `archive.zip#member`, else `(ref, None)`."""
    s = str(ref)
    if "#" in s:
        head, member = s.rsplit("#", 1)
        if head.lower().endswith(".zip"):
            return head, member
    return s, None


def read_bytes(ref) -> bytes:
    """The JSON text of a file, a `.gz`, or a zip member, as bytes."""
    path, member = split_ref(ref)
    if member is not None:
        with zipfile.ZipFile(path) as z:
            data = z.read(member)
        return gzip.decompress(data) if member.endswith(".gz") else data
    raw = Path(path).read_bytes()
    if str(path).endswith(".gz") or raw[:2] == b"\x1f\x8b":
        return gzip.decompress(raw)
    return raw


def read_json(ref):
    return json.loads(read_bytes(ref).decode("utf-8"))


def exists(ref) -> bool:
    path, member = split_ref(ref)
    if not Path(path).exists():
        return False
    if member is None:
        return True
    try:
        with zipfile.ZipFile(path) as z:
            return member in z.namelist()
    except (zipfile.BadZipFile, OSError):
        return False


def write_certificate(cert, path) -> None:
    """`path` ending in `.gz` is written gzip-compressed; anything else as the
    indented (or, past a megabyte, compact) JSON `to_json` gives."""
    text = cert.to_json()
    p = Path(path)
    if str(p).endswith(".gz"):
        p.write_bytes(gzip.compress(text.encode("utf-8"), 6))
    else:
        p.write_text(text, encoding="utf-8")


def is_certificate_name(name) -> bool:
    n = str(name).lower()
    return (n.endswith(".json") or n.endswith(".json.gz")) \
        and not n.endswith(MANIFEST)


def walk(root):
    """Every candidate certificate under `root` -- files, `.gz`, and the
    members of any zip -- as `(ref, rel, raw_or_None)`. `raw` is None when the
    bytes are not readable JSON; the caller decides what that means."""
    root = Path(root)
    if root.is_file() or split_ref(root)[1] is not None:
        sources = [root]
    elif root.is_dir():
        sources = sorted(p for p in root.rglob("*")
                         if p.is_file() and (is_certificate_name(p.name)
                                             or p.suffix.lower() == ".zip"))
    else:
        raise FileNotFoundError(str(root))
    for f in sources:
        try:
            rel = str(f.relative_to(root)) if root.is_dir() else f.name
        except ValueError:
            rel = str(f)
        if str(f).lower().endswith(".zip") and split_ref(f)[1] is None:
            try:
                with zipfile.ZipFile(f) as z:
                    names = [n for n in z.namelist() if is_certificate_name(n)]
            except (zipfile.BadZipFile, OSError):
                continue
            for n in names:
                ref = "{}#{}".format(f, n)
                yield ref, "{}#{}".format(rel, n), _try(ref)
            continue
        yield str(f), rel, _try(f)


def _try(ref):
    try:
        return read_json(ref)
    except (ValueError, UnicodeDecodeError, OSError, KeyError,
            zipfile.BadZipFile, EOFError):
        return None


def pack(src, out) -> dict:
    """Every certificate under `src` into the zip `out`, with a manifest.
    Returns what was packed and what was left out, and why."""
    from . import __version__
    from .certificate import SCHEMA_VERSION, Certificate

    src, out = Path(src), Path(out)
    members, skipped = [], []
    seen = set()
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED,
                         compresslevel=6) as z:
        for ref, rel, raw in walk(src):
            if Path(split_ref(ref)[0]).resolve() == out.resolve():
                continue
            data = Certificate.unwrap(raw) if isinstance(raw, dict) else None
            if not isinstance(data, dict) or "kind" not in data:
                skipped.append(rel)
                continue
            cert = Certificate.from_dict(data)
            name = rel.replace("\\", "/").replace("#", "/")
            if name.endswith(".gz"):
                name = name[:-3]
            if name in seen:
                skipped.append(rel)
                continue
            seen.add(name)
            text = cert.to_json().encode("utf-8")
            z.writestr(name, text)
            entry = {"name": name, "digest": cert.digest(), "kind": cert.kind,
                     "schema": cert.schema, "bytes": len(text)}
            box = (cert.payload or {}).get("box")
            if box:
                entry["box"] = box
            members.append(entry)
        manifest = {"certo_version": __version__, "schema": SCHEMA_VERSION,
                    "created": datetime.now(timezone.utc).isoformat(
                        timespec="seconds"),
                    "count": len(members), "members": members}
        z.writestr(MANIFEST, json.dumps(manifest, indent=2, ensure_ascii=False))
    return {"archive": str(out), "count": len(members), "skipped": skipped,
            "bytes": out.stat().st_size,
            "json_bytes": sum(m["bytes"] for m in members)}


def manifest_of(archive):
    try:
        with zipfile.ZipFile(archive) as z:
            return json.loads(z.read(MANIFEST).decode("utf-8"))
    except KeyError:
        return None


def _verify_member(job):
    """One member, verified. Top-level so a process pool can run it."""
    from .certificate import Certificate, verify
    from .limits import Limits

    ref, timeout_ms = job
    try:
        cert = Certificate.from_dict(read_json(ref))
    except Exception as e:  # noqa: BLE001
        return ref, None, False, "{}: {}".format(type(e).__name__, e), ""
    rep = verify(cert, Limits(timeout_ms=timeout_ms))
    return ref, cert.kind, rep.ok, rep.detail, cert.digest()


def verify_archive(archive, jobs=1, timeout_ms=60_000) -> dict:
    """Every member of a packed archive verified, and its manifest checked
    against what the members actually are: the same names, the same digests.
    `jobs > 1` runs members in parallel processes; a pool that breaks -- an
    interpreter dying at start-up is the known way -- finishes serially."""
    archive = str(archive)
    with zipfile.ZipFile(archive) as z:
        names = [n for n in z.namelist() if is_certificate_name(n)]
    refs = ["{}#{}".format(archive, n) for n in names]
    results = {}
    jobs_list = [(r, timeout_ms) for r in refs]
    if jobs > 1 and len(refs) > 1:
        from concurrent.futures import ProcessPoolExecutor
        from concurrent.futures.process import BrokenProcessPool

        try:
            with ProcessPoolExecutor(max_workers=jobs) as pool:
                for res in pool.map(_verify_member, jobs_list, chunksize=4):
                    results[res[0]] = res
        except BrokenProcessPool:
            pass
    for job in jobs_list:
        if job[0] not in results:
            results[job[0]] = _verify_member(job)
    rows = [results[r] for r in refs]
    man = manifest_of(archive)
    declared = {m["name"]: m["digest"] for m in (man or {}).get("members", [])}
    actual = {split_ref(r)[1]: d for r, _k, _ok, _det, d in rows}
    manifest_ok = man is not None and declared == actual
    return {"archive": archive, "count": len(rows),
            "valid": sum(1 for r in rows if r[2]),
            "invalid": [{"member": split_ref(r[0])[1], "kind": r[1],
                         "detail": r[3]} for r in rows if not r[2]],
            "manifest": "missing" if man is None
            else ("ok" if manifest_ok else "differs"),
            "manifest_differs": sorted(set(declared.items()) ^ set(actual.items()))[:5]
            if man is not None and not manifest_ok else []}
