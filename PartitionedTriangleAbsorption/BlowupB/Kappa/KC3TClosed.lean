/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKC3T
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KC2CClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KC3T` (the class "C2")

`CoveredAll₈` adds its relabellings to `CoveredAll₇` (97 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KC3T : PaddedInputs.KeevashPaddedSpec KC3T :=
  keevashPaddedSpec_of_certs₈ KC3T familyFacts_KC3T universalCert_KC3T completeInverseCert₈_KC3T

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₈ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₇ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ PaddedComponents.KC3T

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₈ F) := by
  unfold CoveredAll₈; infer_instance

theorem keevashPaddedSpec_of_coveredAll₈ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₈ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₇ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KC3T

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 97 of the 765 census classes. -/
theorem targetFour_on_coveredAll₈ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₈ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₈ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KC3T
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₈
