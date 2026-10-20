/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.CompBal
public import PartitionedTriangleAbsorption.BlowupB.Robust.RMBG2
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.OrdinaryHost

@[expose] public section

/-!
# The Latin core: the open target

`F_latin = {012, 013}` on four classes is the pure Latin core of the 17 conserved BAL families
(after vertex splitting their conserved classes form a block isomorphic to `{abc}` or `{abc, abd}`).
Its integral divisibility is the balance `deg_b = deg_c` at every vertex for the orientation
`0 → 1 → {2,3} → 0`, a ℤ-valued conservation law, so no single-vertex charge token exists.

`LatinTarget` asks for a flexible universal absorber certificate; `keevashTypedSpec_latin_of_target`
turns it into the typed Keevash interface.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral VertexSplit
open PartitionedTriangleAbsorption.BlowupB

/-- The pure Latin core. -/
noncomputable def F_latin : Finset (Multiset (Fin 4)) := {{0, 1, 2}, {0, 1, 3}}

/-- **The open target**: a flexible universal absorber certificate for the Latin core. -/
def LatinTarget : Prop := ∃ L : ℕ, PaddedGeneral.RealInverse.UniversalCertFlexL F_latin L

theorem familyFacts_latin : FamilyFacts F_latin :=
  ⟨by decide +kernel, by unfold Link; decide +kernel, by unfold Link; decide +kernel⟩

/-- The target gives the typed Keevash interface for the Latin core. -/
theorem keevashTypedSpec_latin_of_target (h : LatinTarget) : KeevashTypedSpec F_latin := by
  obtain ⟨L, hL⟩ := h
  exact PaddedGeneral.RealInverse.keevashTypedSpec_of_flexible_absorberL F_latin familyFacts_latin L hL

end PartitionedTriangleAbsorption.BlowupB.LatinCore

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.keevashTypedSpec_latin_of_target
