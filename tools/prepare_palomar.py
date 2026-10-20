"""Create Paper II's isolated Palomar interface from the unchanged source statements.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from port_to_module import port

HEADER = """/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
"""
BASE = "PartitionedTriangleAbsorption"
ROWS = []
DEFS = []
THMS = []
NS = ""
OUT = [HEADER, """module

public import Mathlib

/-!
# Robust absorption for typed triangles — Paper II

The compared statements are Theorems A, B, C and D, the balanced consequence
of B, and terminal absorption Lemma SC. All definitions below are reproduced
from the frozen proof library with their original names and bodies.

The typical-host property includes positive regular triangle weights, common-
neighbour extension and both global and local integral divisibility. The
four-label theorem is not a theorem for arbitrary divisible hosts. The
semidense theorem uses ordered edit cost. Lemma SC explicitly assumes physical
hinge supply with exponent i - 4 after fixing four roots.

Only Mathlib is imported here. Solution imports the proofs, including the
finite census and conserved-family constructions; none is a hypothesis.
-/

@[expose] public section
"""]


def read(name):
    return (ROOT / BASE / name).read_text(encoding="utf8")


def block(file, name, theorem=False):
    text = read(file)
    found = re.search(r"^(?:(?:noncomputable|private) )?(?:def|abbrev|structure|instance|theorem) "
                      + re.escape(name) + r"\b", text, re.M)
    assert found, (file, name)
    start = found.start()
    if theorem:
        end = text.index(":= by", start)
        code = text[start:end] + ":= by\n  sorry"
    else:
        end = text.find("\n\n", start)
        following = re.search(r"\n(?:(?:noncomputable|private) )?(?:def|abbrev|structure|instance|theorem) ",
                              text[start + 1:])
        if following:
            end = min(end if end >= 0 else len(text), start + 1 + following.start())
        code = text[start:end if end >= 0 else len(text)].rstrip()
    ROWS.append(dict(source=f"{BASE}/{file}", name=NS + "." + name,
                     kind="theorem" if theorem else "definition",
                     source_start_line=text[:start].count("\n") + 1,
                     reproduced_sha256=hashlib.sha256(code.encode()).hexdigest()))
    (THMS if theorem else DEFS).append(NS + "." + name)
    return code


def ns(name, context):
    global NS
    if NS:
        OUT.append("end " + NS)
    NS = name
    OUT.append(f"namespace {name}\n\n{context}")


def add(file, names, theorem=False, prefix=""):
    for name in names.split():
        code = block(file, name, theorem)
        documentation = ""
        if not theorem:
            text = read(file)
            before = text[:text.index(code)].rstrip()
            if before.endswith("-/"):
                pos = before.rfind("/--")
                if pos >= 0 and "-/" not in before[pos:-2]:
                    documentation = before[pos:] + "\n"
            if not documentation:
                descriptions = {
                    "other0": "The opposite label in a two-part partition.",
                    "orderedSideTarget": "The complete bipartite or two-clique adjacency pattern on the chosen side.",
                    "orderedSideCost": "Number of ordered off-diagonal adjacency disagreements with that pattern.",
                    "instDecidableAllowedPair": "Finite decidability of the allowed-pair predicate.",
                }
                documentation = "/-- " + descriptions.get(name, "The source definition of `" + name + "`.") + " -/\n"
        OUT.append(prefix + documentation + code)


def main():
    global NS
    ns(BASE, "open Finset\nvariable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}")
    add("ReturnedBasic.lean", "pairVec degContrib edgeVec degVec typeEdgeVec typeDegVec "
        "IsIntDiv triEdges IsTypedTri IsDecomp HasDecomp IsCopy vertSet IsHinge")
    ns(BASE + ".TypedTransformer", "variable {t : ℕ}")
    add("TypedTransformerLabels.lean", "Link ThreeStepLinks")
    ns("PaddedGeneral", f"open {BASE}.TypedTransformer")
    add("BlowupB/PaddedGeneral/Reduction.lean", "FamilyFacts")
    ns(BASE + ".BlowupB", "open Finset\nvariable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}")
    add("BlowupB/CompleteBlowup.lean", "AllowedPair")
    add("BlowupB/KeevashBridge.lean", "thirdsT TriRegular CNExt KeevashTypedSpec")
    add("BlowupB/Nearly.lean", "instDecidableAllowedPair missSet missDeg")
    add("BlowupB/ReserveWeights.lean", "nPrime")
    add("BlowupB/TypicalReserveMain.lean", "clsz")
    add("BlowupB/TeoremaBBalanced.lean", "BalancedWeights")
    OUT.append("/-- Paper II, Theorem B: nearly complete hosts with positive type weights. -/")
    add("BlowupB/TeoremaB.lean", "teoremaB_of_keevash", theorem=True)
    OUT.append("/-- The balanced consequence of Theorem B; the finite weight condition is retained. -/")
    add("BlowupB/TeoremaBBalanced.lean", "teoremaB_balanced", theorem=True)
    ns("PaddedGeneral.RealInverse", f"open {BASE}.TypedTransformer {BASE}.BlowupB")
    OUT.append("/-- Paper II, Theorem A: three-step links imply the typical-host property. -/")
    add("BlowupB/PaddedGeneral/RealInverse/ThreeStepFamily.lean",
        "keevashTypedSpec_of_threeStepLinks", theorem=True)
    ns(BASE + ".BlowupB.FiniteCensus", f"open {BASE}.TypedTransformer")
    OUT.append("/-- Paper II, computer-assisted Theorem D, without a catalogue-membership premise. -/")
    add("BlowupB/Census/Universal.lean", "keevashTypedSpec_of_admissible", theorem=True)
    ns(BASE + ".TypedApplicationLinks", "")
    add("TypedApplicationLinks.lean", "F0 other0")
    ns(BASE + ".CloneSupply", "open Finset\nvariable {V : Type*} [Fintype V] [DecidableEq V]")
    add("CloneSupply/Basic.lean", "partSet partNbrs partDeg")
    ns(BASE + ".BlowupB.F0Direct", "open Finset CloneSupply TypedApplicationLinks\n"
       "variable {V : Type*} [Fintype V] [DecidableEq V]")
    add("F0OrderedBridge.lean", "orderedSideTarget")
    add("F0OrderedBridge.lean", "orderedSideCost", prefix="open Classical in\n")
    OUT.append("/-- Paper II, Theorem C: mixed triangles in a semidense two-part host. -/")
    add("F0OrderedTheorem.lean", "theorem146_ordered", theorem=True)
    ns(BASE + ".SignedCertificate", "open Finset\n"
       "variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]")
    add("SignedCertificate/Basic.lean", "ind certWeight")
    ns(BASE + ".SignedHinge", "open Finset\nvariable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}")
    add("SignedHinge/Select.lean", "HingeSupply", prefix="open Classical in\n")
    ns(BASE + ".BlowupB.LemmaSC", f"open Finset {BASE} {BASE}.SignedHinge {BASE}.SignedCertificate")
    add("BlowupB/LemmaSC/OnePart.lean", "onePart K3fam")
    OUT.append("variable {V : Type*} [Fintype V] [DecidableEq V]")
    OUT.append("/-- Paper II, Lemma SC: a bounded signed certificate yields a terminal absorber. -/")
    add("BlowupB/LemmaSC/OnePart.lean", "absorber_onePart", theorem=True)
    OUT.append("end " + NS)
    challenge = "\n\n".join(OUT) + "\n"
    assert len(challenge.splitlines()) < 1000 and len(challenge.encode()) < 100 * 1024
    (ROOT / "Challenge.lean").write_text(challenge, encoding="utf8", newline="\n")
    (ROOT / "Solution.lean").write_text(HEADER + """module

public import PartitionedTriangleAbsorption.PaperII.Core
public import PartitionedTriangleAbsorption.PaperII.Families
public import PartitionedTriangleAbsorption.PaperII.PaperIApplications

/-! The six compared declarations are exported with their original names.
All proofs are supplied by the three audited Paper II entry closures. -/
""", encoding="utf8", newline="\n")
    (ROOT / "comparator.json").write_text(json.dumps(dict(
        challenge_module="Challenge", solution_module="Solution", theorem_names=THMS,
        definition_names=[], permitted_axioms=["propext", "Classical.choice", "Quot.sound"],
        enable_nanoda=True), indent=2) + "\n", encoding="utf8")
    (ROOT / "tools/interface_manifest.json").write_text(json.dumps(dict(
        definitions=DEFS, theorems=THMS, reproductions=ROWS,
        note="Challenge definitions are reproduced, not left as unnamed definition holes."),
        indent=2) + "\n", encoding="utf8")
    if "--interface-only" in sys.argv:
        manifest_path = ROOT / "tools/port_manifest.json"
        manifest = json.loads(manifest_path.read_text())
        for name in ("Challenge.lean", "Solution.lean"):
            digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            manifest[name] = dict(before=digest, after=digest)
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps(dict(challenge_lines=len(challenge.splitlines()),
                              compared_theorems=len(THMS), definitions=len(DEFS))))
        return
    # Split one generated certificate module only at a complete-family boundary.
    path = ROOT / BASE / "BlowupB/BalFixer/Fam/Bal04.lean"
    original = path.read_text(encoding="utf8")
    start = original.index("noncomputable def F_BAL040")
    cut = original.index("noncomputable def F_BAL045")
    finish = original.index("end PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam")
    preamble = original[:start]
    ending = "end PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam\n"
    chunks = [original[start:cut], original[cut:finish]]
    parts = []
    for i, body in enumerate(chunks):
        name = f"Bal04Part{i+1}"
        p = path.with_name(name + ".lean")
        p.write_text(preamble + body + ending, encoding="utf8", newline="\n")
        parts.append(dict(path=p.relative_to(ROOT).as_posix(),
                          body_sha256=hashlib.sha256(body.encode()).hexdigest()))
    path.write_text(HEADER +
        "import PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.Bal04Part1\n"
        "import PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.Bal04Part2\n\n"
        + original[finish + len(ending):], encoding="utf8", newline="\n")
    (ROOT / "tools/split_manifest.json").write_text(json.dumps(dict(
        original_path=path.relative_to(ROOT).as_posix(),
        original_sha256=hashlib.sha256(original.encode()).hexdigest(),
        parts=parts, proof_bodies_preserved=True), indent=2) + "\n", encoding="utf8")
    # Mechanical module-system conversion; keep a hash for every source.
    manifest = {}
    for p in sorted(ROOT.rglob("*.lean")):
        raw = p.read_bytes()
        result = port(raw.decode("utf8")).encode()
        p.write_bytes(result)
        manifest[p.relative_to(ROOT).as_posix()] = dict(
            before=hashlib.sha256(raw).hexdigest(), after=hashlib.sha256(result).hexdigest())
    (ROOT / "tools/port_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    # Reuse only the already validated compatibility repair, not compiled project objects.
    rel = "PartitionedTriangleAbsorption/BlowupB/PaddedF12/TorsionFinite.lean"
    p = ROOT / rel
    before = p.read_bytes()
    assert before.count(b"  simpa [cap] using h") == 1
    after = before.replace(b"  simpa [cap] using h", b"  cases a <;> simpa [cap] using h")
    p.write_bytes(after)
    (ROOT / "tools/port_repairs.json").write_text(json.dumps(dict(repairs=[dict(
        path=rel, before_sha256=hashlib.sha256(before).hexdigest(),
        after_sha256=hashlib.sha256(after).hexdigest(),
        before="  simpa [cap] using h", after="  cases a <;> simpa [cap] using h",
        reason="Constructor-explicit elaboration under module visibility; validated in Paper I port aa032bb5dc35280aa1b30f327688c7592a9eb7c0.")]), indent=2) + "\n")
    lake = (ROOT / "lakefile.toml").read_text().replace('name = "nw_aligned"', 'name = "typed_triangle_absorption"')
    lake = lake.replace('version = "0.1.0"', 'version = "1.0.0"\nrequiresModuleSystem = true\ndefaultTargets = ["Challenge", "Solution"]')
    for name in ("PartitionedTriangleAbsorption", "Challenge", "Solution"):
        lake += f'\n[[lean_lib]]\nname = "{name}"\nroots = ["{name}"]\n'
        if name == BASE:
            lake += f'globs = ["{name}", "{name}.+"]\n'
    (ROOT / "lakefile.toml").write_text(lake, encoding="utf8", newline="\n")
    print(json.dumps(dict(challenge_lines=len(challenge.splitlines()),
                          compared_theorems=len(THMS), definitions=len(DEFS),
                          lean_modules=len(manifest))))


if __name__ == "__main__":
    main()
