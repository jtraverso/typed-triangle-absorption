/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKM1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKM2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKM3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKM4
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKM5
public import PartitionedTriangleAbsorption.BlowupB.Kappa.ChargeClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KM1`–`KM5`: disconnected `ℤ/3`, isolated `333`, no `ThreeStepLinks`

Via `keevashPaddedSpec_of_certs₈` (the original `CompleteInverseCert` is false for families with an
isolated monochromatic class). `CoveredAll₃` adds their relabellings to `CoveredAll₂`
(82 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

/-- **`KeevashPaddedSpec KM1`**, unconditional. -/
theorem keevashPaddedSpec_KM1 : PaddedInputs.KeevashPaddedSpec KM1 :=
  keevashPaddedSpec_of_certs₈ KM1 familyFacts_KM1 universalCert_KM1 completeInverseCert₈_KM1

/-- **`KeevashPaddedSpec KM2`**, unconditional. -/
theorem keevashPaddedSpec_KM2 : PaddedInputs.KeevashPaddedSpec KM2 :=
  keevashPaddedSpec_of_certs₈ KM2 familyFacts_KM2 universalCert_KM2 completeInverseCert₈_KM2

/-- **`KeevashPaddedSpec KM3`**, unconditional. -/
theorem keevashPaddedSpec_KM3 : PaddedInputs.KeevashPaddedSpec KM3 :=
  keevashPaddedSpec_of_certs₈ KM3 familyFacts_KM3 universalCert_KM3 completeInverseCert₈_KM3

/-- **`KeevashPaddedSpec KM4`**, unconditional. -/
theorem keevashPaddedSpec_KM4 : PaddedInputs.KeevashPaddedSpec KM4 :=
  keevashPaddedSpec_of_certs₈ KM4 familyFacts_KM4 universalCert_KM4 completeInverseCert₈_KM4

/-- **`KeevashPaddedSpec KM5`**, unconditional. -/
theorem keevashPaddedSpec_KM5 : PaddedInputs.KeevashPaddedSpec KM5 :=
  keevashPaddedSpec_of_certs₈ KM5 familyFacts_KM5 universalCert_KM5 completeInverseCert₈_KM5

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₃ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₂ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KM1 ∨ F = permFam σ PaddedComponents.KM2 ∨ F = permFam σ PaddedComponents.KM3 ∨ F = permFam σ PaddedComponents.KM4 ∨ F = permFam σ PaddedComponents.KM5

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₃ F) := by
  unfold CoveredAll₃; infer_instance

theorem keevashPaddedSpec_of_coveredAll₃ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₃ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₂ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KM1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KM2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KM3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KM4
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KM5

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 82 of the 765 census classes. -/
theorem targetFour_on_coveredAll₃ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₃ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₃ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KM1
#print axioms PaddedComponents.keevashPaddedSpec_KM2
#print axioms PaddedComponents.keevashPaddedSpec_KM3
#print axioms PaddedComponents.keevashPaddedSpec_KM4
#print axioms PaddedComponents.keevashPaddedSpec_KM5
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₃
