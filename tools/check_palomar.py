"""Verify Paper II's built Palomar interface and source scope.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
This is a local preflight, not a substitute for Palomar's Comparator/NanoDa run.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
REPORT = []


def lean(text):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Check.lean"
        path.write_text(text, encoding="utf8")
        proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                              capture_output=True, text=True, encoding="utf8")
        assert proc.returncode == 0, proc.stdout + proc.stderr
        return proc.stdout + proc.stderr


def strip_comments(text):
    # Nested Lean block comments; retain code and line comments separately.
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    assert depth == 0, "Unclosed block comment"
    return "".join(result)


def static_checks():
    config = json.loads((ROOT / "comparator.json").read_text())
    interface = json.loads((ROOT / "tools/interface_manifest.json").read_text())
    assert config["theorem_names"] == interface["theorems"]
    sources = sorted((ROOT / "PartitionedTriangleAbsorption").rglob("*.lean"))
    sources += [ROOT / name for name in ("PartitionedTriangleAbsorption.lean",
                                        "Challenge.lean", "Solution.lean")]
    for path in sources:
        assert not path.is_symlink(), path
        text = path.read_text(encoding="utf8")
        code = strip_comments(text)
        assert re.match(r"\s*module\b", code), path
        assert len(text.splitlines()) <= (1000 if path.name == "Challenge.lean" else 10000), path
        if path.name != "Challenge.lean":
            assert not re.search(r"\b(sorry|admit|native_decide|axiom)\b", code), path
        else:
            assert len(re.findall(r"\bsorry\b", code)) == 6
            assert re.findall(r"^(?:public )?import (.+)$", code, re.M) == ["Mathlib"]
            assert len(path.read_bytes()) <= 100 * 1024
        assert not re.search(r"^(?:public )?import RequestProject", code, re.M), path
    locked = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in locked["packages"] if p["name"] == "mathlib")
    assert mathlib["rev"] == "c55e6e786f49471c72fbddbec5415808896aec1e"
    assert (ROOT / "lean-toolchain").read_bytes() == (
        ROOT / ".lake/packages/mathlib/lean-toolchain").read_bytes()
    REPORT.append(f"PASS_MODULE_POLICY ({len(sources)} Lean files; no source exceeds the line cap)")
    REPORT.append("PASS_STATEMENT_IMPORTS (Mathlib only)")
    REPORT.append("PASS_NO_PAPER_I_IMPORTS")
    REPORT.append("no sorry/admit/native_decide/custom axiom in the library or Solution")
    return interface


def main():
    interface = static_checks()
    queries = []
    for p in sorted((ROOT / "PartitionedTriangleAbsorption/PaperII").glob("*.lean")):
        if p.stem in ("Core", "Families", "PaperIApplications"):
            queries += re.findall(r"^#print axioms (\S+)", p.read_text(encoding="utf8"), re.M)
    queries = list(dict.fromkeys(queries + interface["theorems"]))
    axout = lean("import Solution\n" + "".join(f"#print axioms {name}\n" for name in queries))
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axout, re.S)
    assert len(found) == len(queries), axout
    assert [name for name, _ in found] == queries, axout
    for name, axioms in found:
        assert {a.strip() for a in axioms.split(",") if a.strip()} <= STANDARD, (name, axioms)
    REPORT.append(f"PASS_STANDARD_AXIOMS ({len(queries)} declarations, including teoremaB_balanced)")
    REPORT.append(axout.strip())

    body = "set_option pp.all true\nset_option pp.universes true\n"
    body += "".join(f"#check @{name}\n" for name in interface["theorems"])
    body += "".join(f"#print {name}\n" for name in interface["definitions"])
    dumps = []
    for module in ("Challenge", "Solution"):
        output = lean(f"import {module}\n" + body)
        output = re.sub(r"/--.*?-/", "", output, flags=re.S)
        dumps.append([line.rstrip() for line in output.splitlines() if line.strip()])
    if dumps[0] != dumps[1]:
        REPORT.extend(difflib.unified_diff(*dumps, fromfile="Challenge", tofile="Solution"))
        raise AssertionError("Compared types or reproduced definitions differ; see report")
    REPORT.append(f"TYPES AND DEFINITIONS IDENTICAL ({len(dumps[0])} lines)")
    REPORT.append("ALL CHECKS PASSED")


if __name__ == "__main__":
    success = False
    try:
        main()
        success = True
    except Exception as error:
        REPORT.extend(["CHECKS FAILED", str(error)])
    report = "\n".join(REPORT) + "\n"
    (ROOT / "tools/check_report.txt").write_text(report, encoding="utf8", newline="\n")
    (ROOT / "tools/check_result.json").write_text(json.dumps(dict(
        status="ALL CHECKS PASSED" if success else "CHECKS FAILED",
        report_sha256=hashlib.sha256(report.encode()).hexdigest(),
        scope="Local preflight; independent Palomar Comparator/NanoDa verification is separate."),
        indent=2) + "\n", encoding="utf8", newline="\n")
    sys.stdout.reconfigure(encoding="utf8")
    print(report)
    raise SystemExit(0 if success else 1)
