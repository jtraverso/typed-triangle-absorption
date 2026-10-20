"""Check the isolated port against its immutable source archive.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
Usage: python -I tools/verify_source_port.py PATH_TO_ORIGINAL_ZIP
"""
from pathlib import Path
import hashlib
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from port_to_module import port
from prepare_palomar import HEADER


def main():
    archive = Path(sys.argv[1])
    manifest = json.loads((ROOT / "tools/source_manifest.json").read_text())
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest["sha256"]
    split = json.loads((ROOT / "tools/split_manifest.json").read_text())
    repairs = json.loads((ROOT / "tools/port_repairs.json").read_text())["repairs"]
    repair_map = {r["path"]: r for r in repairs}
    checked = 0
    with zipfile.ZipFile(archive) as z:
        prefix = archive.stem + "/source/"
        for row in manifest["files"]:
            name = row["path"]
            raw = z.read(prefix + name)
            assert hashlib.sha256(raw).hexdigest() == row["sha256"], name
            if not name.endswith(".lean"):
                continue
            text = raw.decode("utf8")
            if name == split["original_path"]:
                start = text.index("noncomputable def F_BAL040")
                middle = text.index("noncomputable def F_BAL045")
                ending = "end PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam\n"
                finish = text.index(ending)
                for part, body in zip(split["parts"], [text[start:middle], text[middle:finish]]):
                    assert hashlib.sha256(body.encode()).hexdigest() == part["body_sha256"]
                    expected = port(text[:start] + body + ending).encode()
                    assert (ROOT / part["path"]).read_bytes() == expected, part["path"]
                text = HEADER + (
                    "import PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.Bal04Part1\n"
                    "import PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.Bal04Part2\n\n"
                ) + text[finish + len(ending):]
            expected = port(text)
            if name in repair_map:
                repair = repair_map[name]
                assert expected.count(repair["before"]) == 1
                expected = expected.replace(repair["before"], repair["after"])
            assert (ROOT / name).read_bytes() == expected.encode(), name
            checked += 1
    report = dict(status="PASS", original_lean_files_checked=checked,
                  source_archive=manifest["source_archive"], source_sha256=manifest["sha256"],
                  generated_split_modules_checked=2,
                  changes="Mechanical module port, family-boundary split, and the recorded constructor-explicit elaboration repair.")
    (ROOT / "tools/source_port_check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
