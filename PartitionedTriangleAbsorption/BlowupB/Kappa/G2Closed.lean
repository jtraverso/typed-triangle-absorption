/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTA1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTB1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTB2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTB3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTH1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTH2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTH3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKTH4
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KEClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for the eight G2 families (torsion in the component, isolated `333`)

`CoveredAll₁₀` adds their relabellings to `CoveredAll₉` (109 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KTA1 : PaddedInputs.KeevashPaddedSpec KTA1 :=
  keevashPaddedSpec_of_certs₈ KTA1 familyFacts_KTA1 universalCert_KTA1 completeInverseCert₈_KTA1

theorem keevashPaddedSpec_KTB1 : PaddedInputs.KeevashPaddedSpec KTB1 :=
  keevashPaddedSpec_of_certs₈ KTB1 familyFacts_KTB1 universalCert_KTB1 completeInverseCert₈_KTB1

theorem keevashPaddedSpec_KTB2 : PaddedInputs.KeevashPaddedSpec KTB2 :=
  keevashPaddedSpec_of_certs₈ KTB2 familyFacts_KTB2 universalCert_KTB2 completeInverseCert₈_KTB2

theorem keevashPaddedSpec_KTB3 : PaddedInputs.KeevashPaddedSpec KTB3 :=
  keevashPaddedSpec_of_certs₈ KTB3 familyFacts_KTB3 universalCert_KTB3 completeInverseCert₈_KTB3

theorem keevashPaddedSpec_KTH1 : PaddedInputs.KeevashPaddedSpec KTH1 :=
  keevashPaddedSpec_of_certs₈ KTH1 familyFacts_KTH1 universalCert_KTH1 completeInverseCert₈_KTH1

theorem keevashPaddedSpec_KTH2 : PaddedInputs.KeevashPaddedSpec KTH2 :=
  keevashPaddedSpec_of_certs₈ KTH2 familyFacts_KTH2 universalCert_KTH2 completeInverseCert₈_KTH2

theorem keevashPaddedSpec_KTH3 : PaddedInputs.KeevashPaddedSpec KTH3 :=
  keevashPaddedSpec_of_certs₈ KTH3 familyFacts_KTH3 universalCert_KTH3 completeInverseCert₈_KTH3

theorem keevashPaddedSpec_KTH4 : PaddedInputs.KeevashPaddedSpec KTH4 :=
  keevashPaddedSpec_of_certs₈ KTH4 familyFacts_KTH4 universalCert_KTH4 completeInverseCert₈_KTH4

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₁₀ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₉ F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedComponents.KTA1 ∨ F = permFam σ PaddedComponents.KTB1 ∨ F = permFam σ PaddedComponents.KTB2 ∨ F = permFam σ PaddedComponents.KTB3 ∨ F = permFam σ PaddedComponents.KTH1 ∨ F = permFam σ PaddedComponents.KTH2 ∨ F = permFam σ PaddedComponents.KTH3 ∨ F = permFam σ PaddedComponents.KTH4

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₁₀ F) := by
  unfold CoveredAll₁₀; infer_instance

theorem keevashPaddedSpec_of_coveredAll₁₀ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₁₀ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₉ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTA1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTB1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTB2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTB3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTH1
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTH2
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTH3
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KTH4

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 109 of the 765 census classes. -/
theorem targetFour_on_coveredAll₁₀ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₁₀ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₁₀ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KTA1
#print axioms PaddedComponents.keevashPaddedSpec_KTB1
#print axioms PaddedComponents.keevashPaddedSpec_KTB2
#print axioms PaddedComponents.keevashPaddedSpec_KTB3
#print axioms PaddedComponents.keevashPaddedSpec_KTH1
#print axioms PaddedComponents.keevashPaddedSpec_KTH2
#print axioms PaddedComponents.keevashPaddedSpec_KTH3
#print axioms PaddedComponents.keevashPaddedSpec_KTH4
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₁₀
