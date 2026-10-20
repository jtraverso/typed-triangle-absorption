/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKC2C
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXClosed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KC2C`: two charges of unit `4` and an isolated `333`

`CoveredAll₇` adds its relabellings to `CoveredAll₆` (96 of the 765 census classes).
-/

namespace PaddedComponents

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KC2C : PaddedInputs.KeevashPaddedSpec KC2C :=
  keevashPaddedSpec_of_certs₈ KC2C familyFacts_KC2C universalCert_KC2C completeInverseCert₈_KC2C

end PaddedComponents

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₇ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₆ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ PaddedComponents.KC2C

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₇ F) := by
  unfold CoveredAll₇; infer_instance

theorem keevashPaddedSpec_of_coveredAll₇ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₇ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact keevashPaddedSpec_of_coveredAll₆ F hF
  · exact keevashPaddedSpec_perm σ PaddedComponents.keevashPaddedSpec_KC2C

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 96 of the 765 census classes. -/
theorem targetFour_on_coveredAll₇ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₇ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₇ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedComponents.keevashPaddedSpec_KC2C
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₇
