/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.TeoremaB748
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Certificates

@[expose] public section

/-! Theorem B on the previously closed families and the seventeen conserved
representatives. The orbit count and exhaustiveness of the finite census are
separate checks; neither is assumed by the decomposition theorem below. -/

namespace PartitionedTriangleAbsorption.BlowupB

def Closed765 (F : Finset (Multiset (Fin 4))) : Prop :=
  Closed748 F ∨ ∃ i : Fin 17, F = (LatinCore.Conserved17.cases i).F

theorem keevashTypedSpec_of_closed765 (F : Finset (Multiset (Fin 4)))
    (hF : PaddedGeneral.FamilyFacts F) (hC : Closed765 F) : KeevashTypedSpec F := by
  rcases hC with h | ⟨i, rfl⟩
  · exact keevashTypedSpec_of_closed748 F hF h
  · exact LatinCore.Conserved17.all_typed_specs i

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashTypedSpec_of_closed765
