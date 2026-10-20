"""Build the isolated Paper II port and run its post-build preflight.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
No publication, Git push, package update, or source repair is performed.
"""
from datetime import datetime, timezone
from pathlib import Path
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / ".lake/palomar-build"
STATE = {}


def state(status, **extra):
    STATE.update(status=status, updated_at=datetime.now(timezone.utc).isoformat(), **extra)
    tmp = LOG / "state.tmp"
    tmp.write_text(json.dumps(STATE, indent=2) + "\n")
    tmp.replace(LOG / "state.json")


def run(command, filename, status):
    with (LOG / filename).open("w", encoding="utf8") as output:
        child = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        state(status, child_pid=child.pid, command=command, log=filename)
        return child.wait()


def main():
    LOG.mkdir(parents=True, exist_ok=True)
    state("STARTING", runner_pid=os.getpid(),
          started_at=datetime.now(timezone.utc).isoformat(),
          revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip())
    code = run(["lake", "build", "Challenge", "Solution"], "build.log", "BUILD_RUNNING")
    if code:
        state("BUILD_FAILED", exit_code=code)
        return code
    code = run([sys.executable, "-I", "tools/check_palomar.py"], "checks.log", "CHECKS_RUNNING")
    state("ALL_CHECKS_PASSED" if code == 0 else "CHECKS_FAILED", exit_code=code)
    return code


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        state("RUNNER_FAILED", error=str(error))
        raise
