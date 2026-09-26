"""`python -m certo ...` -- the entry point that needs no launcher.

On Windows `certo.exe` is a small launcher that starts the interpreter as a
CHILD. A caller that times out and kills `certo.exe` leaves that interpreter
running with the pipes open, and waits on them forever; under load the
launcher itself can fail to be found (WinError 2). Both were reported by a
user driving thousands of runs. `python -m certo` starts one process and no
launcher, so a timeout kills the process that holds the pipes. It is the one
to use from `subprocess`.
"""
from .cli import main

raise SystemExit(main())
