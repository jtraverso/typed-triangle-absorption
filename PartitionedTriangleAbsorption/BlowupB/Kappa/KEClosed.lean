/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKE1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKE2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKE3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKE4
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KC3TClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KE1`–`KE4` (all components `Even3`)

`CoveredAll₉` adds their relabellings to `CoveredAll₈` (101 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KE1 : PaddedInputs.KeevashPaddedSpec KE1 :=
  keevashPaddedSpec_of_certs₈ KE1 familyFacts_KE1 universalCert_KE1 completeInverseCert₈_KE1

theorem keevashPaddedSpec_KE2 : PaddedInputs.KeevashPaddedSpec KE2 :=
  keevashPaddedSpec_of_certs₈ KE2 familyFacts_KE2 universalCert_KE2 completeInverseCert₈_KE2

theorem keevashPaddedSpec_KE3 : PaddedInputs.KeevashPaddedSpec KE3 :=
  keevashPaddedSpec_of_certs₈ KE3 familyFacts_KE3 universalCert_KE3 completeInverseCert₈_KE3

theorem keevashPaddedSpec_KE4 : PaddedInputs.KeevashPaddedSpec KE4 :=
  keevashPaddedSpec_of_certs₈ KE4 familyFacts_KE4 universalCert_KE4 completeInverseCert₈_KE4

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₉ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₈ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KE1 ∨ F = permFam σ PaddedComponents.KE2 ∨ F = permFam σ PaddedComponents.KE3 ∨ F = permFam σ PaddedComponents.KE4

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₉ F) := by
  unfold CoveredAll₉; infer_instance

theorem keevashPaddedSpec_of_coveredAll₉ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₉ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₈ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KE1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KE2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KE3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KE4

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 101 of the 765 census classes. -/
theorem targetFour_on_coveredAll₉ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₉ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₉ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KE1
#print axioms PaddedComponents.keevashPaddedSpec_KE2
#print axioms PaddedComponents.keevashPaddedSpec_KE3
#print axioms PaddedComponents.keevashPaddedSpec_KE4
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₉
