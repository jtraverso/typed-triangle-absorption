/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKT1
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Closed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KT1 = {000, 001, 002, 011, 113}`, a family WITHOUT `ThreeStepLinks`

* universal certificate: Aristotle's walk refiner (`universal_budget_walk`) with the terminal
  absorbers of `guarded_terminal_absorber_of_mass_kappa` (coloured hub fed by `KappaLinks`);
* lattice: trivial, via the `FiveStepLinks` collapse (`isIntDiv_iff_five`);
* inverse: the `FnA` inverse without its `111` mode.

`CoveredFamilyK₅` adds the relabellings of `KT1` to `CoveredFamily₄`.
-/

namespace PaddedNoCommon

open PartitionedTriangleAbsorption PaddedGeneral

theorem completeInverseCert_KT1 : CompleteInverseCert KT1 :=
  completeInverseCert_of_ternary subset_rfl (fun _ _ => Iff.rfl) ternaryInverse_KT1

/-- **`KeevashPaddedSpec KT1`**, unconditional: the first family without `ThreeStepLinks`. -/
theorem keevashPaddedSpec_KT1 : PaddedInputs.KeevashPaddedSpec KT1 :=
  keevashPaddedSpec_of_certs KT1 familyFacts_KT1 universalCert_KT1 completeInverseCert_KT1

end PaddedNoCommon

namespace PartitionedTriangleAbsorption.BlowupB

open PaddedNoCommon

def CoveredFamilyK₅ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₄ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ KT1

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamilyK₅ F) := by
  unfold CoveredFamilyK₅; infer_instance

theorem keevashPaddedSpec_of_coveredK₅ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamilyK₅ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact keevashPaddedSpec_of_covered₄ F hF
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_KT1

theorem targetFour_on_coveredK₅ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamilyK₅ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredK₅ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedNoCommon.keevashPaddedSpec_KT1
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_of_coveredK₅
