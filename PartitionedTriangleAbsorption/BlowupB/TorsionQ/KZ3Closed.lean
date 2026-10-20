/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.KZ3Inverse
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Closed

@[expose] public section

/-!
# `KeevashPaddedSpec` for `KZ3 = {000,001,002,012,123,133,333}`: `ℤ/3` torsion, no `ThreeStepLinks`

The first family closed with a torsion of order 3, via the generic mod-`q` torsion layer
`TorsionQ.torsion_layerQ`, the `KappaLinks` terminal absorbers and a monochromatic vertex mode.
`CoveredFamilyK₇` adds its relabellings to `CoveredFamilyK₆` (29 of the 765 census classes).
-/

namespace TorsionQ.KZ3

open PartitionedTriangleAbsorption PaddedGeneral PartitionedTriangleAbsorption.TypedTransformer

theorem familyFacts_KZ3 : FamilyFacts KZ3 :=
  ⟨KZ3_card, by unfold Link KZ3; decide, by intro i; fin_cases i <;> (unfold Link KZ3; decide)⟩

theorem universalCert_KZ3 : UniversalCert KZ3 :=
  fun V _ _ p G _ ω hG hs hω hω1 hn => universal_simple_KZ3 p G ω hG hs hω hω1 hn

/-- **`KeevashPaddedSpec KZ3`**, unconditional. -/
theorem keevashPaddedSpec_KZ3 : PaddedInputs.KeevashPaddedSpec KZ3 :=
  keevashPaddedSpec_of_certs KZ3 familyFacts_KZ3 universalCert_KZ3 completeInverseCert_KZ3

end TorsionQ.KZ3

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredFamilyK₇ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamilyK₆ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ TorsionQ.KZ3.KZ3

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamilyK₇ F) := by
  unfold CoveredFamilyK₇; infer_instance

theorem keevashPaddedSpec_of_coveredK₇ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamilyK₇ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl⟩
  · exact keevashPaddedSpec_of_coveredK₆ F hF
  · exact keevashPaddedSpec_perm σ TorsionQ.KZ3.keevashPaddedSpec_KZ3

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 29 of the 765 census classes. -/
theorem targetFour_on_coveredK₇ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamilyK₇ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredK₇ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms TorsionQ.KZ3.keevashPaddedSpec_KZ3
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredK₇
