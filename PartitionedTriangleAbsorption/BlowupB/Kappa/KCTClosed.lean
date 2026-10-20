/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCT1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCT2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCT3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCT4
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCT5
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCT6
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCCClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KCT1`–`KCT6`: a `ℤ/3` component and an isolated `333`

`CoveredAll₅` adds their relabellings to `CoveredAll₄` (91 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KCT1 : PaddedInputs.KeevashPaddedSpec KCT1 :=
  keevashPaddedSpec_of_certs₈ KCT1 familyFacts_KCT1 universalCert_KCT1 completeInverseCert₈_KCT1

theorem keevashPaddedSpec_KCT2 : PaddedInputs.KeevashPaddedSpec KCT2 :=
  keevashPaddedSpec_of_certs₈ KCT2 familyFacts_KCT2 universalCert_KCT2 completeInverseCert₈_KCT2

theorem keevashPaddedSpec_KCT3 : PaddedInputs.KeevashPaddedSpec KCT3 :=
  keevashPaddedSpec_of_certs₈ KCT3 familyFacts_KCT3 universalCert_KCT3 completeInverseCert₈_KCT3

theorem keevashPaddedSpec_KCT4 : PaddedInputs.KeevashPaddedSpec KCT4 :=
  keevashPaddedSpec_of_certs₈ KCT4 familyFacts_KCT4 universalCert_KCT4 completeInverseCert₈_KCT4

theorem keevashPaddedSpec_KCT5 : PaddedInputs.KeevashPaddedSpec KCT5 :=
  keevashPaddedSpec_of_certs₈ KCT5 familyFacts_KCT5 universalCert_KCT5 completeInverseCert₈_KCT5

theorem keevashPaddedSpec_KCT6 : PaddedInputs.KeevashPaddedSpec KCT6 :=
  keevashPaddedSpec_of_certs₈ KCT6 familyFacts_KCT6 universalCert_KCT6 completeInverseCert₈_KCT6

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₅ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₄ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KCT1 ∨ F = permFam σ PaddedComponents.KCT2 ∨ F = permFam σ PaddedComponents.KCT3 ∨ F = permFam σ PaddedComponents.KCT4 ∨ F = permFam σ PaddedComponents.KCT5 ∨ F = permFam σ PaddedComponents.KCT6

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₅ F) := by
  unfold CoveredAll₅; infer_instance

theorem keevashPaddedSpec_of_coveredAll₅ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₅ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₄ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCT1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCT2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCT3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCT4
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCT5
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCT6

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 91 of the 765 census classes. -/
theorem targetFour_on_coveredAll₅ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₅ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₅ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KCT1
#print axioms PaddedComponents.keevashPaddedSpec_KCT2
#print axioms PaddedComponents.keevashPaddedSpec_KCT3
#print axioms PaddedComponents.keevashPaddedSpec_KCT4
#print axioms PaddedComponents.keevashPaddedSpec_KCT5
#print axioms PaddedComponents.keevashPaddedSpec_KCT6
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₅
