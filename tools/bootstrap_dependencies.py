"""Populate independent dependency checkouts at the locked revisions.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
Only Git object storage is reused; project build objects are never copied.
"""
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path("C:/nw/nash-williams-lean/.lake/packages")


def run(args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in lock["packages"]:
        destination = ROOT / ".lake/packages" / package["name"]
        destination.parent.mkdir(parents=True, exist_ok=True)
        assert not destination.exists(), destination
        run(["git", "-c", "core.autocrlf=false", "clone", "--local", "--no-checkout",
             str(SOURCE / package["name"]), str(destination)])
        run(["git", "-C", str(destination), "remote", "set-url", "origin", package["url"]])
        run(["git", "-C", str(destination), "-c", "core.autocrlf=false",
             "checkout", "--detach", package["rev"]])
        actual = subprocess.check_output(["git", "-C", str(destination), "rev-parse", "HEAD"],
                                         text=True).strip()
        assert actual == package["rev"]
    run(["lake", "exe", "cache", "get"])


if __name__ == "__main__":
    main()
