/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Closed
public import PartitionedTriangleAbsorption.BlowupB.TeoremaBGeneralTarget

@[expose] public section

/-!
# Integration of Aristotle project 6ca1e982 (task c42fa9e7, 2026-10-12)

Aristotle proved `KeevashPaddedSpec` for `PaddedTrivial.Ftriv` (all relabellings) and introduced the
decidable class `PaddedTrivial.CoveredFamily` (relabellings of F₁, F₂, F₃, Ftriv). Its family is
literally our F* (`Ftriv_eq_Fstar`); its witness bound `2K + 16` improves our `8K + 40`. Its covered
class is contained in `CoveredFamily₃`, which adds F† and the five Fbit families.

The open targets of the submission (`TeoremaBTarget.TargetFour/TargetFourCerts/TargetAll`) remain
open; `targetFour_on_covered₃` is the proved fragment of `TargetFour`.
-/

namespace PartitionedTriangleAbsorption.BlowupB

theorem Ftriv_eq_Fstar : PaddedTrivial.Ftriv = PaddedFstar.Fstar := rfl

theorem coveredFamily₃_of_aristotle (F : Finset (Multiset (Fin 4)))
    (hF : PaddedTrivial.CoveredFamily F) : CoveredFamily₃ F :=
  Or.inl (Or.inl hF)

/-- The proved fragment of `TeoremaBTarget.TargetFour`. -/
theorem targetFour_on_covered₃ :
    ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → CoveredFamily₃ F →
      PaddedInputs.KeevashPaddedSpec F :=
  fun F _ hF => keevashPaddedSpec_of_covered₃ F hF

/-- Sanity: two of the ten base families are in the covered class (decidably). -/
example : CoveredFamily₃ PaddedFdagger.Fdag := by decide
example : CoveredFamily₃ PaddedFbit.FbitMono := by decide

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.Ftriv_eq_Fstar
#print axioms PartitionedTriangleAbsorption.BlowupB.targetFour_on_covered₃
