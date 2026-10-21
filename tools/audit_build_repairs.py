"""Audit header-only repairs against the initial Palomar build revision.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = "93979dd796e185f13676a9b09593cc09b2b95bbf"
FLOW = "PartitionedTriangleAbsorption/BlowupB/LatinCore/CapacitatedFlowFeasibility.lean"
CHARGE = "PartitionedTriangleAbsorption/BlowupB/PaddedCharge/Universal.lean"
CHARGE_WALK = "PartitionedTriangleAbsorption/BlowupB/Kappa/ChargeWalk.lean"
TRANSPORT = "PartitionedTriangleAbsorption/BlowupB/LatinCore/RootCatalogueTransport.lean"
CHALLENGE = "Challenge.lean"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def canonical(data, path):
    text = data.decode("utf8").replace("\r\n", "\n")
    if path == CHALLENGE:
        for name in ("thirdsT", "TriRegular", "CNExt"):
            text = text.replace(
                f"def {name} {{t : ℕ}} {{V : Type u_1}} [Fintype V] [DecidableEq V] (p : V → Fin t)",
                f"def {name} (p : V → Fin t)")
        text = text.replace("def clsz {t : ℕ} {V : Type u_1} [Fintype V] (p : V → Fin t)",
                            "def clsz (p : V → Fin t)")
    if path == FLOW:
        for module in ("Mathlib.Analysis.Normed.Order.Lattice", "Mathlib.Analysis.RCLike.Basic"):
            text, count = re.subn(r"(?m)^(?:public )?import " + re.escape(module) + r"\n", "", text)
            assert count == 1
    if path in (CHARGE, CHARGE_WALK):
        text = text.replace("-- Resource budget for elaborating the unchanged universal absorber proof.\n", "")
        text = text.replace("set_option maxHeartbeats 1600000\n", "")
    if path == TRANSPORT:
        anchor = "  simp [RootPaths.pathArcs, liftArc, pathArcs, hr, channelVertex]\n"
        assert text.count(anchor) == 1
        text = text.replace(anchor + "  rfl\n", anchor, 1)
    return "\n".join(line for line in text.splitlines() if line.strip()).encode("utf8")


changed = git("diff", "--name-only", BASE, "--", "*.lean").decode().splitlines()
assert set(changed) == {FLOW, CHARGE, CHARGE_WALK, TRANSPORT, CHALLENGE}, changed
rows = []
for path in changed:
    before = git("show", f"{BASE}:{path}")
    after = (ROOT / path).read_bytes()
    assert canonical(before, path) == canonical(after, path), path
    rows.append(dict(file=path, before_sha256=hashlib.sha256(before).hexdigest(),
                     after_sha256=hashlib.sha256(after).hexdigest(),
                     normalized_body_sha256=hashlib.sha256(canonical(after, path)).hexdigest()))
report = dict(status="PASS_STATEMENTS_PRESERVED_AND_AUTHORIZED_TACTIC_CLEANUP", base_revision=BASE,
              current_head=git("rev-parse", "HEAD").decode().strip(),
              checked_utc=datetime.now(timezone.utc).isoformat(), files=rows,
              scope="Exactly five tracked Lean files differ: import placement/public imports, resource headers in two modules, the author-authorized deletion of one redundant trailing rfl in channel_as_walk, and the separately author-authorized alignment of implicit parameter binders in four reproduced Challenge definitions. All definition bodies, mathematical statements and all remaining proof text are unchanged against the initial build revision.")
(ROOT / "tools/build_repair_preservation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf8")
print(json.dumps(report, indent=2))
