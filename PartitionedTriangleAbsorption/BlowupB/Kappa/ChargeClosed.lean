/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCa
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKCb
public import PartitionedTriangleAbsorption.BlowupB.CoverageAll

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KCa` and `KCb`: one charge, no torsion, no `ThreeStepLinks`

`KCa = {001,002,011,113}` and `KCb = {001,002,011,022,113}` are subfamilies of `FnoC` with the same
charge `chiNoC`. They are the first families closed that combine a nontrivial charge with the
`KappaLinks` terminal absorbers (`universalCert_of_charge_walk_kappa`, `Kappa/ChargeWalk.lean`).
`CoveredAll₂` adds their relabellings to `CoveredAll` (77 of the 765 census classes).
-/

namespace PaddedCharge

open PartitionedTriangleAbsorption PaddedGeneral

/-- **`KeevashPaddedSpec KCa`**, unconditional. -/
theorem keevashPaddedSpec_KCa : PaddedInputs.KeevashPaddedSpec KCa :=
  keevashPaddedSpec_of_certs KCa familyFacts_KCa universalCert_KCa completeInverseCert_KCa

/-- **`KeevashPaddedSpec KCb`**, unconditional. -/
theorem keevashPaddedSpec_KCb : PaddedInputs.KeevashPaddedSpec KCb :=
  keevashPaddedSpec_of_certs KCb familyFacts_KCb universalCert_KCb completeInverseCert_KCb

end PaddedCharge

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll₂ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll F ∨ ∃ σ : Equiv.Perm (Fin 4),
    F = permFam σ PaddedCharge.KCa ∨ F = permFam σ PaddedCharge.KCb

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll₂ F) := by
  unfold CoveredAll₂; infer_instance

theorem keevashPaddedSpec_of_coveredAll₂ (F : Finset (Multiset (Fin 4))) (hF : CoveredAll₂ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredAll F hF
  · exact keevashPaddedSpec_perm σ PaddedCharge.keevashPaddedSpec_KCa
  · exact keevashPaddedSpec_perm σ PaddedCharge.keevashPaddedSpec_KCb

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 77 of the 765 census classes. -/
theorem targetFour_on_coveredAll₂ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll₂ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll₂ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedCharge.keevashPaddedSpec_KCa
#print axioms PaddedCharge.keevashPaddedSpec_KCb
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll₂
