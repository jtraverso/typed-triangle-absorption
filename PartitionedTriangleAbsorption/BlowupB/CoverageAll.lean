/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoFamilies.Closed
public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.KZ3Closed

@[expose] public section

/-!
# All four-class families proved so far (2026-10-13)

Two independent extension chains of `CoveredFamily₄` (Aristotle's `PaddedNoCommon`):

* Aristotle (task 6d686018): `CoveredFamily₈` = `CoveredFamily₄` + `FnoC` (charge layer, target A)
  + the 45 disconnected `ℤ/3` classes `FB1`–`FB6`, `FM01`–`FM39` (componentwise refiner; for the
  39 with an isolated monochromatic class via `keevashPaddedSpec_of_certs₈`);
* local: `CoveredFamilyK₇` = `CoveredFamily₄` + `KT1`–`KT4` (no `ThreeStepLinks`, `KappaLinks`
  terminal absorbers) + `KZ3` (`ℤ/3`, mod-`q` torsion layer).

`CoveredAll` is their union: 75 of the 765 census classes (Python census; the Lean statement is the
decidable predicate itself).
-/

namespace PartitionedTriangleAbsorption.BlowupB

def CoveredAll (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredFamily₈ F ∨ CoveredFamilyK₇ F

noncomputable instance (F : Finset (Multiset (Fin 4))) : Decidable (CoveredAll F) := by
  unfold CoveredAll; infer_instance

theorem keevashPaddedSpec_of_coveredAll (F : Finset (Multiset (Fin 4))) (hF : CoveredAll F) :
    PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with hF | hF
  · exact keevashPaddedSpec_of_covered₈ F hF
  · exact keevashPaddedSpec_of_coveredK₇ F hF

/-- **The proved fragment of `TeoremaBTarget.TargetFour`.** -/
theorem targetFour_on_coveredAll :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredAll F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_coveredAll F hF

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_coveredAll
