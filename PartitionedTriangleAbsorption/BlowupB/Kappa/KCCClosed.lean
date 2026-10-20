/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCC1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCC2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCC3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KMClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KCC1`–`KCC3`: one charged component and an isolated `333`

`CoveredAll₄` adds their relabellings to `CoveredAll₃` (85 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KCC1 : PaddedInputs.KeevashPaddedSpec KCC1 :=
  keevashPaddedSpec_of_certs₈ KCC1 familyFacts_KCC1 universalCert_KCC1 completeInverseCert₈_KCC1

theorem keevashPaddedSpec_KCC2 : PaddedInputs.KeevashPaddedSpec KCC2 :=
  keevashPaddedSpec_of_certs₈ KCC2 familyFacts_KCC2 universalCert_KCC2 completeInverseCert₈_KCC2

theorem keevashPaddedSpec_KCC3 : PaddedInputs.KeevashPaddedSpec KCC3 :=
  keevashPaddedSpec_of_certs₈ KCC3 familyFacts_KCC3 universalCert_KCC3 completeInverseCert₈_KCC3

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₄ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₃ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KCC1 ∨ F = permFam σ PaddedComponents.KCC2 ∨ F = permFam σ PaddedComponents.KCC3

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₄ F) := by
  unfold CoveredAll₄; infer_instance

theorem keevashPaddedSpec_of_coveredAll₄ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₄ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₃ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCC1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCC2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCC3

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 85 of the 765 census classes. -/
theorem targetFour_on_coveredAll₄ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₄ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₄ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KCC1
#print axioms PaddedComponents.keevashPaddedSpec_KCC2
#print axioms PaddedComponents.keevashPaddedSpec_KCC3
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₄
