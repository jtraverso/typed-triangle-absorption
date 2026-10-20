/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCX1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCX2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCX3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCX4
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCTClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KCX1`–`KCX4`: one charge of unit `4`, `3 ∣ e` as a mod-3 value

`CoveredAll₆` adds their relabellings to `CoveredAll₅` (95 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KCX1 : PaddedInputs.KeevashPaddedSpec KCX1 :=
  keevashPaddedSpec_of_certs₈ KCX1 familyFacts_KCX1 universalCert_KCX1 completeInverseCert₈_KCX1

theorem keevashPaddedSpec_KCX2 : PaddedInputs.KeevashPaddedSpec KCX2 :=
  keevashPaddedSpec_of_certs₈ KCX2 familyFacts_KCX2 universalCert_KCX2 completeInverseCert₈_KCX2

theorem keevashPaddedSpec_KCX3 : PaddedInputs.KeevashPaddedSpec KCX3 :=
  keevashPaddedSpec_of_certs₈ KCX3 familyFacts_KCX3 universalCert_KCX3 completeInverseCert₈_KCX3

theorem keevashPaddedSpec_KCX4 : PaddedInputs.KeevashPaddedSpec KCX4 :=
  keevashPaddedSpec_of_certs₈ KCX4 familyFacts_KCX4 universalCert_KCX4 completeInverseCert₈_KCX4

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₆ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₅ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KCX1 ∨ F = permFam σ PaddedComponents.KCX2 ∨ F = permFam σ PaddedComponents.KCX3 ∨ F = permFam σ PaddedComponents.KCX4

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₆ F) := by
  unfold CoveredAll₆; infer_instance

theorem keevashPaddedSpec_of_coveredAll₆ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₆ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₅ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCX1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCX2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCX3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KCX4

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 95 of the 765 census classes. -/
theorem targetFour_on_coveredAll₆ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₆ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₆ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KCX1
#print axioms PaddedComponents.keevashPaddedSpec_KCX2
#print axioms PaddedComponents.keevashPaddedSpec_KCX3
#print axioms PaddedComponents.keevashPaddedSpec_KCX4
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₆
