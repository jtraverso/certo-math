"""The build writes down WHAT it built: `certo/_build.json`.

A wheel used to answer `certo --version` with "not a checkout" -- the commit
was read from git at run time, and an installed wheel has no git. Two wheels
of the same version, one built from a tree with uncommitted edits, were
indistinguishable. So the build records, once, in the package:

    {"commit": the full hash, "clean": no uncommitted change to a tracked
     file, "built": the UTC date (SOURCE_DATE_EPOCH when set)}

`python -m build` makes the sdist from the checkout and the wheel FROM THE
SDIST, where there is no git: the sdist carries the file, and the wheel keeps
it. Nothing here runs at import time; everything else is in pyproject.toml.
"""
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from setuptools import setup
from setuptools.command.build_py import build_py
from setuptools.command.sdist import sdist

HERE = Path(__file__).resolve().parent
NAME = "_build.json"


def _git(*args):
    try:
        out = subprocess.run(["git", *args], cwd=str(HERE), capture_output=True,
                             text=True, timeout=10)
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout.strip() if out.returncode == 0 else None


def _info():
    """From git when this is a checkout; from the sdist's copy otherwise."""
    commit = _git("rev-parse", "HEAD")
    if commit:
        dirty = _git("status", "--porcelain", "--untracked-files=no")
        epoch = os.environ.get("SOURCE_DATE_EPOCH")
        when = (datetime.fromtimestamp(int(epoch), timezone.utc) if epoch
                else datetime.now(timezone.utc))
        return {"commit": commit, "clean": dirty == "",
                "built": when.strftime("%Y-%m-%dT%H:%M:%SZ")}
    shipped = HERE / "src" / "certo" / NAME
    if shipped.is_file():
        return json.loads(shipped.read_text(encoding="utf-8"))
    return None


def _write(folder):
    info = _info()
    if info is not None:
        Path(folder).mkdir(parents=True, exist_ok=True)
        (Path(folder) / NAME).write_text(json.dumps(info, indent=1) + "\n",
                                         encoding="utf-8")


class BuildPy(build_py):
    def run(self):
        super().run()
        _write(Path(self.build_lib) / "certo")


class Sdist(sdist):
    def make_release_tree(self, base_dir, files):
        super().make_release_tree(base_dir, files)
        _write(Path(base_dir) / "src" / "certo")


setup(cmdclass={"build_py": BuildPy, "sdist": Sdist})
