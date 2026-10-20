/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Assembly
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.VerifiedF12
public import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Assembly

@[expose] public section

/-!
# The covered class of four-class families

`CoveredFamily F` is the decidable predicate "`F` is a relabelling of `F₁`, `F₂`, `F₃` or
`Ftriv`". For every such `F` the padded Keevash statement holds unconditionally.
-/

namespace PaddedTrivial

open PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedApplicationLinks

/-- The covered class: relabellings of the four base families `F₁, F₂, F₃, Ftriv`. -/
def CoveredFamily (F : Finset (Multiset (Fin 4))) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), F = BlowupB.permFam σ F1 ∨ F = BlowupB.permFam σ F2 ∨
    F = BlowupB.permFam σ F3 ∨ F = BlowupB.permFam σ Ftriv

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamily F) := by
  unfold CoveredFamily; infer_instance

/-- **Covered families**: the padded Keevash statement for every family in `CoveredFamily`. -/
theorem keevashPaddedSpec_of_covered (F : Finset (Multiset (Fin 4))) (hF : CoveredFamily F) :
    PaddedInputs.KeevashPaddedSpec F := by
  obtain ⟨σ, rfl | rfl | rfl | rfl⟩ := hF
  · exact BlowupB.keevashPaddedSpec_perm σ PaddedF12.keevashPaddedSpec_F1
  · exact BlowupB.keevashPaddedSpec_perm σ PaddedF12.keevashPaddedSpec_F2
  · exact BlowupB.keevashPaddedSpec_perm σ PaddedF3.keevashPaddedSpec_F3
  · exact keevashPaddedSpec_perm_Ftriv σ

/-- Sanity check: the covered class is nonempty. -/
example : CoveredFamily Ftriv := ⟨1, Or.inr (Or.inr (Or.inr (by
  ext τ; simp [BlowupB.permFam])))⟩

#print axioms keevashPaddedSpec_of_covered

end PaddedTrivial
