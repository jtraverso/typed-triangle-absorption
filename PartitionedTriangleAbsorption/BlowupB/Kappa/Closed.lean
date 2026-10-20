/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.ClosedKT1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKT2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKT3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.InverseKT4

@[expose] public section

/-!
# The four connected trivial-lattice `KappaLinks` families without `ThreeStepLinks`

`KT1 = {000,001,002,011,113}`, `KT2 = {000,001,002,011,022,113}`, `KT3 = {000,001,011,112,122,223}`,
`KT4 = {000,001,002,011,022,111,223}`: by the local census these are exactly the census classes
without `ThreeStepLinks` that satisfy `KappaLinks`, have a connected class graph and a trivial lattice
(Python, `kappa_gate.py` / `oddlinks.py`). `CoveredFamilyK₆` adds their relabellings.
-/

namespace PaddedNoCommon

open PartitionedTriangleAbsorption PaddedGeneral

theorem keevashPaddedSpec_KT2 : PaddedInputs.KeevashPaddedSpec KT2 :=
  keevashPaddedSpec_of_certs KT2 familyFacts_KT2 universalCert_KT2
    (completeInverseCert_of_ternary subset_rfl (fun _ _ => Iff.rfl) ternaryInverse_KT2)

theorem keevashPaddedSpec_KT3 : PaddedInputs.KeevashPaddedSpec KT3 :=
  keevashPaddedSpec_of_certs KT3 familyFacts_KT3 universalCert_KT3
    (completeInverseCert_of_ternary subset_rfl (fun _ _ => Iff.rfl) ternaryInverse_KT3)

theorem keevashPaddedSpec_KT4 : PaddedInputs.KeevashPaddedSpec KT4 :=
  keevashPaddedSpec_of_certs KT4 familyFacts_KT4 universalCert_KT4
    (completeInverseCert_of_ternary subset_rfl (fun _ _ => Iff.rfl) ternaryInverse_KT4)

end PaddedNoCommon

namespace PartitionedTriangleAbsorption.BlowupB

open PaddedNoCommon

def CoveredFamilyK₆ (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamilyK₅ F ∨ ∃ σ : Equiv.Perm (Fin 4), F = permFam σ KT2 ∨ F = permFam σ KT3 ∨
    F = permFam σ KT4

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredFamilyK₆ F) := by
  unfold CoveredFamilyK₆; infer_instance

theorem keevashPaddedSpec_of_coveredK₆ (F : Finset (Multiset (Fin 4))) (hF : CoveredFamilyK₆ F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | ⟨σ, rfl | rfl | rfl⟩
  · exact keevashPaddedSpec_of_coveredK₅ F hF
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_KT2
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_KT3
  · exact keevashPaddedSpec_perm σ keevashPaddedSpec_KT4

/-- The proved fragment of `TeoremaBTarget.TargetFour`: 28 of the 765 census classes. -/
theorem targetFour_on_coveredK₆ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamilyK₆ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredK₆ F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PaddedNoCommon.ternaryInverse_KT2
#print axioms PaddedNoCommon.ternaryInverse_KT3
#print axioms PaddedNoCommon.ternaryInverse_KT4
#print axioms PaddedNoCommon.ternaryInverse_KT1
#print axioms PaddedNoCommon.keevashPaddedSpec_KT2
#print axioms PaddedNoCommon.keevashPaddedSpec_KT3
#print axioms PaddedNoCommon.keevashPaddedSpec_KT4
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredK₆
