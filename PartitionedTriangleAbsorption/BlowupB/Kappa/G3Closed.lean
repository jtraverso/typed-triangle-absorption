/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ4
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ5
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ6
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ7
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ8
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ9
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ10
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKQ11
public import PartitionedTriangleAbsorption.BlowupB.Kappa.G2Closed

@[expose] public section

/-!
# `KeevashPaddedSpec` for the eleven G3 classes (charged components)

`CoveredAll₁₁` adds their relabellings to `CoveredAll₁₀` (120 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KQ1 : PaddedInputs.KeevashPaddedSpec KQ1 :=
  keevashPaddedSpec_of_certs₈ KQ1 familyFacts_KQ1 universalCert_KQ1 completeInverseCert₈_KQ1

theorem keevashPaddedSpec_KQ2 : PaddedInputs.KeevashPaddedSpec KQ2 :=
  keevashPaddedSpec_of_certs₈ KQ2 familyFacts_KQ2 universalCert_KQ2 completeInverseCert₈_KQ2

theorem keevashPaddedSpec_KQ3 : PaddedInputs.KeevashPaddedSpec KQ3 :=
  keevashPaddedSpec_of_certs₈ KQ3 familyFacts_KQ3 universalCert_KQ3 completeInverseCert₈_KQ3

theorem keevashPaddedSpec_KQ4 : PaddedInputs.KeevashPaddedSpec KQ4 :=
  keevashPaddedSpec_of_certs₈ KQ4 familyFacts_KQ4 universalCert_KQ4 completeInverseCert₈_KQ4

theorem keevashPaddedSpec_KQ5 : PaddedInputs.KeevashPaddedSpec KQ5 :=
  keevashPaddedSpec_of_certs₈ KQ5 familyFacts_KQ5 universalCert_KQ5 completeInverseCert₈_KQ5

theorem keevashPaddedSpec_KQ6 : PaddedInputs.KeevashPaddedSpec KQ6 :=
  keevashPaddedSpec_of_certs₈ KQ6 familyFacts_KQ6 universalCert_KQ6 completeInverseCert₈_KQ6

theorem keevashPaddedSpec_KQ7 : PaddedInputs.KeevashPaddedSpec KQ7 :=
  keevashPaddedSpec_of_certs₈ KQ7 familyFacts_KQ7 universalCert_KQ7 completeInverseCert₈_KQ7

theorem keevashPaddedSpec_KQ8 : PaddedInputs.KeevashPaddedSpec KQ8 :=
  keevashPaddedSpec_of_certs₈ KQ8 familyFacts_KQ8 universalCert_KQ8 completeInverseCert₈_KQ8

theorem keevashPaddedSpec_KQ9 : PaddedInputs.KeevashPaddedSpec KQ9 :=
  keevashPaddedSpec_of_certs₈ KQ9 familyFacts_KQ9 universalCert_KQ9 completeInverseCert₈_KQ9

theorem keevashPaddedSpec_KQ10 : PaddedInputs.KeevashPaddedSpec KQ10 :=
  keevashPaddedSpec_of_certs₈ KQ10 familyFacts_KQ10 universalCert_KQ10 completeInverseCert₈_KQ10

theorem keevashPaddedSpec_KQ11 : PaddedInputs.KeevashPaddedSpec KQ11 :=
  keevashPaddedSpec_of_certs₈ KQ11 familyFacts_KQ11 universalCert_KQ11 completeInverseCert₈_KQ11

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₁₁ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₁₀ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KQ1 ∨ F = permFam σ PaddedComponents.KQ2 ∨ F = permFam σ PaddedComponents.KQ3 ∨ F = permFam σ PaddedComponents.KQ4 ∨ F = permFam σ PaddedComponents.KQ5 ∨ F = permFam σ PaddedComponents.KQ6 ∨ F = permFam σ PaddedComponents.KQ7 ∨ F = permFam σ PaddedComponents.KQ8 ∨ F = permFam σ PaddedComponents.KQ9 ∨ F = permFam σ PaddedComponents.KQ10 ∨ F = permFam σ PaddedComponents.KQ11

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₁₁ F) := by
  unfold CoveredAll₁₁; infer_instance

theorem keevashPaddedSpec_of_coveredAll₁₁ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₁₁ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₁₀ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ4
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ5
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ6
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ7
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ8
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ9
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ10
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KQ11

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 120 of the 765 census classes. -/
theorem targetFour_on_coveredAll₁₁ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₁₁ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₁₁ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KQ1
#print axioms PaddedComponents.keevashPaddedSpec_KQ2
#print axioms PaddedComponents.keevashPaddedSpec_KQ3
#print axioms PaddedComponents.keevashPaddedSpec_KQ4
#print axioms PaddedComponents.keevashPaddedSpec_KQ5
#print axioms PaddedComponents.keevashPaddedSpec_KQ6
#print axioms PaddedComponents.keevashPaddedSpec_KQ7
#print axioms PaddedComponents.keevashPaddedSpec_KQ8
#print axioms PaddedComponents.keevashPaddedSpec_KQ9
#print axioms PaddedComponents.keevashPaddedSpec_KQ10
#print axioms PaddedComponents.keevashPaddedSpec_KQ11
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₁₁
