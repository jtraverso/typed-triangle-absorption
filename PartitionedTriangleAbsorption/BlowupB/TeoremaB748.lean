/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.ParClosed.All
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.All
public import PartitionedTriangleAbsorption.BlowupB.KeevashPaddedMain

@[expose] public section

/-!
# Theorem B: the 748 closed classes

`Closed748 F`: either `CoveredAll₁₂ F` (the 391 classes with the padded Keevash interface: the 120 of
`CoveredAll₁₁` and the 271 PAR classes), or `F` is one of the 357 closed BAL representatives
(`BalFixer.Fam.balClosed`: 301 without a global charge, 52 with one charge, 4 with torsion).
Every such family has the typed Keevash interface. Up to `S₄` these are 748 of the 765 classes; the
remaining 17 are the conserved (Latin core) BAL classes. The class count is checked in Python
(`census748.py`), not in Lean.
-/

namespace PartitionedTriangleAbsorption.BlowupB

/-- The closed families of Theorem B. -/
def Closed748 (F : Finset (Multiset (Fin 4))) : Prop :=
  CoveredAll₁₂ F ∨ F ∈ BalFixer.Fam.balClosed

/-- **The typed Keevash interface on the closed classes.** -/
theorem keevashTypedSpec_of_closed748 (F : Finset (Multiset (Fin 4)))
    (hF : PaddedGeneral.FamilyFacts F) (hC : Closed748 F) : KeevashTypedSpec F := by
  rcases hC with h | h
  · exact keevashTypedSpec_of_padded hF.card_three (keevashPaddedSpec_of_coveredAll₁₂ F h)
  · exact BalFixer.Fam.keevashTypedSpec_balClosed F h

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashTypedSpec_of_closed748
