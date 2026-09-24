"""A bug report that decides whose bug it is, and sends nothing.

THE PROBLEM THIS ANSWERS IS NOT "HOW DO I FILE AN ISSUE". It is that almost
every report this project received could not say whose fault the failure was:

    verify(dict) -> AttributeError      filed as the user's adapter; it was certo's
    restricted() dropped every load      found by hand; no solver could have
    a dependency failed to download     the environment, not certo
    a lemma marked PASS                 the user's argument; certo never saw it

So the part worth automating is the TRIAGE, and certo already has everything
it needs to do most of it: `doctor` for the environment, `lint` for the spec,
its own verifier for its own certificates, and -- once the traceback is kept
rather than printed as one line -- where an exception was actually raised.

WHAT IT CONCLUDES, and the evidence each conclusion needs:

  soundness      the certificate VERIFIES and the user says it is false. The
                 worst thing this tool can do, routed to the private channel.
  certo-bug      certo produced a certificate its OWN verifier rejects. That is
                 never the user's fault, and it is the one conclusion reached
                 with certainty.
  certo-bug?     an exception raised inside certo's own code. Probable, not
                 certain -- certo may be reacting badly to a strange spec.
  environment    `doctor` finds something required missing, or the exception
                 is a module that could not be imported.
  spec           the exception was raised in the spec's own code, or `lint`
                 reports an error.
  undetermined   none of the above. Said as such rather than guessed.

NOTHING LEAVES THE MACHINE. The coverage log was designed so that nothing
does without the user seeing it, and specs contain mathematics that may not be
published yet. This writes a folder, prints a link that opens a pre-filled
issue carrying only non-sensitive fields -- version, platform, the triage --
and stops. The person decides what to paste. There is no network code in this
module, and a test checks that there never is.

The user-name part of every home-directory path is rewritten to `<user>`
everywhere except the copy of the spec, which is the user's own file and is
flagged as such.
"""
from __future__ import annotations

import io
import json
import os
import platform
import re
import shutil
import sys
import traceback
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlencode

#: Set while `rerun` is executing a command. A command whose self-check fails
#: INSIDE a report would otherwise write a second report about itself.
_IN_REPORT = False

REPO = "https://github.com/jtraverso/certo-math"
ISSUE_URL = REPO + "/issues/new"
ADVISORY_URL = REPO + "/security/advisories/new"

#: In order: the first that applies is the headline. The others still travel
#: as evidence, because a report can be two things at once.
PRIORITY = ("soundness", "certo-bug", "environment", "certo-bug?", "spec",
            "undetermined", "nothing-found")

_HOME = re.compile(r"([A-Za-z]:[\\/]+Users[\\/]+)[^\\/\s\"']+"
                   r"|(/home/)[^/\s\"']+|(/Users/)[^/\s\"']+")


def redact(text: str) -> str:
    """Replace the user-name part of home-directory paths with `<user>`.

    Generic rather than `str(Path.home())`: on Windows the same home appears
    long (`jtraverso`) and short (`JTRAVE~1`), and a redaction that catches
    one and leaves the other is not a redaction.
    """
    if not text:
        return text

    def sub(m):
        head = m.group(1) or m.group(2) or m.group(3)
        return head + "<user>"
    return _HOME.sub(sub, str(text))


def _certo_root() -> Path:
    return Path(__file__).resolve().parent


def _origin(tb_frames, spec_path) -> str:
    """Who made the call that failed: certo, the spec, or nobody we can name.

    NOT the innermost frame. The first version used it, and it answers the
    wrong question: when certo hands numpy something malformed and numpy
    raises, the innermost frame is numpy's and the bug would be filed as
    "undetermined" -- though it was certo that made the bad call. So library
    frames are skipped and the innermost frame that belongs to certo or to the
    spec decides. If the spec itself calls numpy and numpy raises, the spec's
    frame is the one left, and the spec is what gets named.
    """
    if not tb_frames:
        return "none"
    root = _certo_root()
    spec = Path(spec_path).resolve() if spec_path else None
    for frame in reversed(tb_frames):
        f = Path(frame.filename).resolve()
        if spec is not None and f == spec:
            return "spec"
        try:
            f.relative_to(root)
            return "certo"
        except ValueError:
            continue
    return "other"


def rerun(argv) -> dict:
    """Run a certo command in-process and keep what `main` would throw away.

    `cli.main` turns every exception into one line and exits 3, which is right
    for a person at a terminal and useless for triage: it discards where the
    exception came from. This calls the command's function itself, keeps the
    traceback, and records the Result by wrapping `emit` -- the one seam every
    certifying command goes through, so no command has to know about this.
    """
    from . import cli

    captured = {"result": None}
    real_emit = cli.emit

    def spy(res, args):
        captured["result"] = res
        return real_emit(res, args)

    out, err = io.StringIO(), io.StringIO()
    info = {"argv": list(argv), "exit": None, "exception": None,
            "traceback": "", "origin": "none", "spec": None}
    try:
        args = cli.build_parser().parse_args(list(argv))
    except SystemExit as e:
        info["exit"] = e.code
        info["exception"] = "argument error"
        return info
    info["spec"] = getattr(args, "spec", None)

    global _IN_REPORT
    cli.emit = spy
    _IN_REPORT = True
    try:
        with redirect_stdout(out), redirect_stderr(err):
            info["exit"] = args.func(args)
    except Exception as e:  # noqa: BLE001 -- the whole point is to keep it
        info["exception"] = "{}: {}".format(type(e).__name__, e)
        info["exception_type"] = type(e).__name__
        frames = traceback.extract_tb(e.__traceback__)
        info["traceback"] = "".join(traceback.format_exception(e))
        info["origin"] = _origin(frames, info["spec"])
    finally:
        cli.emit = real_emit
        _IN_REPORT = False
    info["stdout"], info["stderr"] = out.getvalue(), err.getvalue()
    info["result"] = captured["result"]
    return info


def triage(run=None, cert=None, wrong=False, doctor_report=None,
           lint_report=None) -> dict:
    """Every signal, then a headline. Evidence travels with each."""
    signals = []

    res = (run or {}).get("result")
    if res is not None and res.meta.get("self_check") == "FAILED":
        signals.append(("certo-bug",
                        "certo produced a `{}` certificate that its own "
                        "verifier rejects".format(res.certificate.kind)))

    if wrong:
        target = cert if cert is not None else (res.certificate if res else None)
        if target is not None:
            from .certificate import verify
            rep = verify(target)
            if rep.ok:
                signals.append(("soundness",
                                "the `{}` certificate VERIFIES and is reported "
                                "as mathematically false".format(target.kind)))
            else:
                signals.append(("undetermined",
                                "the certificate is reported false, and it "
                                "does not verify either -- so certo already "
                                "refuses it"))

    if run and run.get("exception"):
        kind = run.get("exception_type", "")
        where = run.get("origin")
        if kind in ("ImportError", "ModuleNotFoundError"):
            signals.append(("environment",
                            "a module could not be imported: {}".format(
                                run["exception"])))
        elif where == "certo":
            signals.append(("certo-bug?",
                            "the exception was raised inside certo: {}".format(
                                run["exception"])))
        elif where == "spec":
            signals.append(("spec",
                            "the exception was raised in the spec's own code: "
                            "{}".format(run["exception"])))
        else:
            signals.append(("undetermined",
                            "the exception came from a library certo calls: "
                            "{}".format(run["exception"])))

    if doctor_report is not None and doctor_report.get("missing_required"):
        signals.append(("environment",
                        "`doctor` reports {} required piece(s) missing".format(
                            doctor_report["missing_required"])))
    if doctor_report is not None:
        for row in doctor_report.get("rows", []):
            if row["key"] in ("install", "metadata") and not row["ok"]:
                signals.append(("environment",
                                "`doctor`: {} -- {}".format(row["key"],
                                                            row["detail"])))

    if lint_report is not None and lint_report.get("errors"):
        first = (lint_report.get("findings") or [{}])[0]
        signals.append(("spec", "`lint` reports {} error(s), first: {}".format(
            lint_report["errors"], first.get("message") or first.get("key"))))

    if not signals:
        signals.append(("nothing-found",
                        "the command ran, and nothing certo can check "
                        "disagreed with it. If the RESULT is mathematically "
                        "wrong, run again with --wrong"))

    rank = {c: i for i, c in enumerate(PRIORITY)}
    headline = min(signals, key=lambda s: rank.get(s[0], len(rank)))[0]
    return {"category": headline,
            "evidence": [{"category": c, "detail": redact(d)}
                         for c, d in signals]}


def issue_link(category, command, version) -> str:
    """A pre-filled issue. ONLY non-sensitive fields travel in the URL."""
    if category == "soundness":
        # A certificate that verifies and is false is reported in private.
        return ADVISORY_URL
    fields = {
        "template": "bug.yml",
        "title": "[{}] certo {}".format(category, command or "").strip(),
        "version": version,
        "platform": "{} / Python {}".format(platform.system(),
                                             platform.python_version()),
        "triage": category,
    }
    return ISSUE_URL + "?" + urlencode(fields)


def _coverage_summary() -> dict:
    """Sizes and counts only. The file's own path is left out: it names a user."""
    from . import coverage

    s = coverage.summary()
    return {k: s.get(k) for k in ("lines", "by_command", "by_status",
                                  "first", "last", "full")}


def _stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")


def auto_dir() -> Path:
    """Where an UNASKED report goes: the data directory, never the working one.

    The same rule as the coverage log: certo does not get to leave files where
    the mathematics lives unless it was asked to.
    """
    override = os.environ.get("CERTO_REPORT_DIR")
    if override:
        return Path(override).expanduser()
    from . import coverage
    return coverage.data_dir() / "reports"


def build(argv=None, cert_path=None, wrong=False, with_coverage=False,
          out=None) -> dict:
    """Run, triage, write the folder. Returns what it found and where it put it."""
    from . import __version__, doctor

    run = rerun(argv) if argv else None
    cert = None
    if cert_path:
        from .certificate import Certificate
        cert = Certificate.from_dict(json.loads(
            Path(cert_path).read_text(encoding="utf-8")))

    doc = doctor.report()
    lint_report = None
    spec = (run or {}).get("spec")
    if spec and str(spec).endswith(".py") and Path(spec).exists():
        from . import lint
        try:
            lint_report = lint.lint(spec)
        except Exception:  # noqa: BLE001
            lint_report = None

    tri = triage(run=run, cert=cert, wrong=wrong, doctor_report=doc,
                 lint_report=lint_report)
    command = (argv[0] if argv else "")

    folder = Path(out) if out else Path.cwd() / "certo-report-{}-{}".format(
        _stamp(), tri["category"].rstrip("?"))
    folder.mkdir(parents=True, exist_ok=True)

    manifest = {
        "certo": __version__,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "command": ["certo"] + [redact(a) for a in (argv or [])],
        "triage": tri,
        "exit": (run or {}).get("exit"),
        "created": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "sent": False,
    }

    def write(name, text):
        (folder / name).write_text(text, encoding="utf-8")

    write("triage.json", json.dumps(manifest, indent=2, ensure_ascii=False))
    write("doctor.json", redact(json.dumps(doc, indent=2, ensure_ascii=False)))
    if run is not None:
        write("output.txt", redact("--- stdout ---\n{}\n--- stderr ---\n{}"
                                   .format(run.get("stdout", ""),
                                           run.get("stderr", ""))))
        if run.get("traceback"):
            write("traceback.txt", redact(run["traceback"]))
        res = run.get("result")
        if res is not None and res.certificate is not None:
            write("certificate.json", json.dumps(res.certificate.to_dict(),
                                                 indent=2, ensure_ascii=False))
    if cert is not None:
        write("certificate_given.json", json.dumps(cert.to_dict(), indent=2,
                                                   ensure_ascii=False))
    spec_copied = None
    if spec and Path(spec).exists():
        spec_copied = "spec_" + Path(spec).name
        shutil.copyfile(spec, folder / spec_copied)
    if lint_report is not None:
        write("lint.json", redact(json.dumps(lint_report, indent=2,
                                             ensure_ascii=False)))
    if with_coverage:
        write("coverage.json", json.dumps(_coverage_summary(), indent=2))

    link = issue_link(tri["category"], command, __version__)
    write("report.md", _markdown(manifest, tri, link, spec_copied,
                                 with_coverage, run))
    archive = shutil.make_archive(str(folder), "zip", root_dir=folder)
    return {"folder": str(folder), "archive": archive, "link": link,
            "triage": tri, "spec_included": spec_copied is not None,
            "coverage_included": bool(with_coverage), "sent": False}


def _markdown(manifest, tri, link, spec_copied, with_coverage, run) -> str:
    """In English on purpose: it is written for the public tracker."""
    lines = [
        "# certo bug report",
        "",
        "> **Nothing has been sent.** This folder was written on your machine "
        "and nowhere else.",
    ]
    if spec_copied:
        lines.append("> It includes **your spec** (`{}`), which may be "
                     "mathematics you have not published. Read it before you "
                     "share anything.".format(spec_copied))
    if tri["category"] == "soundness":
        lines.append("> This looks like a **soundness** problem -- a "
                     "certificate that verifies and is false. Please report it "
                     "**privately**: {}".format(ADVISORY_URL))
    lines += [
        "",
        "## Triage: `{}`".format(tri["category"]),
        "",
    ]
    for e in tri["evidence"]:
        lines.append("- **{}** -- {}".format(e["category"], e["detail"]))
    lines += [
        "",
        "## Environment",
        "",
        "- certo `{}`, Python `{}`".format(manifest["certo"],
                                           manifest["python"]),
        "- `{}`".format(redact(manifest["platform"])),
        "- command: `{}`".format(" ".join(manifest["command"])),
        "- exit: `{}`".format(manifest["exit"]),
    ]
    if run and run.get("traceback"):
        lines += ["", "## Traceback", "", "```",
                  redact(run["traceback"]).rstrip(), "```"]
    if with_coverage:
        lines += ["", "## Coverage (sizes and counts only)", "",
                  "Included because you asked. It says which kinds of "
                  "question certo could not settle on this machine, and "
                  "nothing about what they were.", "",
                  "```json", json.dumps(_coverage_summary(), indent=2), "```"]
    lines += ["", "## To file it", "",
              "Open {} and paste this file, attaching anything else from the "
              "folder you are willing to publish.".format(link), ""]
    return "\n".join(lines)


def capture_selfcheck(res, args) -> str:
    """Written automatically when certo's own certificate fails certo's own
    verifier -- the one case where it KNOWS the bug is its own. Local, never
    sent, and a failure here never becomes a second failure."""
    if _IN_REPORT:
        return ""
    try:
        argv = [a for a in sys.argv[1:]] if sys.argv else []
        folder = auto_dir() / "{}-certo-bug".format(_stamp())
        info = build(argv=None, out=folder)
        # The run already happened; record what it produced directly.
        if res is not None and res.certificate is not None:
            (folder / "certificate.json").write_text(
                json.dumps(res.certificate.to_dict(), indent=2,
                           ensure_ascii=False), encoding="utf-8")
        tri = {"category": "certo-bug",
               "evidence": [{"category": "certo-bug",
                             "detail": "certo produced a `{}` certificate its "
                                       "own verifier rejects".format(
                                           res.certificate.kind)}]}
        data = json.loads((folder / "triage.json").read_text(encoding="utf-8"))
        data["triage"] = tri
        data["command"] = ["certo"] + [redact(a) for a in argv]
        (folder / "triage.json").write_text(
            json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
        return info["folder"]
    except Exception:  # noqa: BLE001
        return ""
