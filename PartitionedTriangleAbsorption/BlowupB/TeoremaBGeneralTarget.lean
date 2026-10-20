/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPerm
public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

@[expose] public section

/-! # Theorem B for general families: the exact open targets (definitions only, nothing assumed)

Proved in this package (no sorry, axioms propext / Classical.choice / Quot.sound only):

* `PaddedF12.keevashPaddedSpec_F1/F2`, `PaddedF3.keevashPaddedSpec_F3`;
* `BlowupB.teoremaB_F123_closed`, `BlowupB.teoremaB_perm_F123` (all relabellings of F₁/F₂/F₃);
* `PaddedGeneral.keevashPaddedSpec_of_certs`:
  `FamilyFacts F → UniversalCert F → CompleteInverseCert F → PaddedInputs.KeevashPaddedSpec F`
  for every `F : Finset (Multiset (Fin 4))`;
* `BlowupB.keevashTypedSpec_of_padded`, `BlowupB.teoremaB_balanced` (the consumers).

The propositions below are the OPEN targets. They are definitions, not hypotheses of any theorem.
-/

namespace TeoremaBTarget

open PartitionedTriangleAbsorption PartitionedTriangleAbsorption.BlowupB

/-- Target 1 (main, four classes): the padded Keevash statement for every family on four classes
satisfying the finite facts used by the assembly. -/
def TargetFour : Prop :=
  ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F → PaddedInputs.KeevashPaddedSpec F

/-- Target 1, certificate form: both certificates for every such family. -/
def TargetFourCerts : Prop :=
  ∀ F : Finset (Multiset (Fin 4)), PaddedGeneral.FamilyFacts F →
    PaddedGeneral.UniversalCert F ∧ PaddedGeneral.CompleteInverseCert F

/-- Target 2 (any number of classes): every family of 3-element types in which each class has a
forbidden partner class. -/
def TargetAll : Prop :=
  ∀ (t : ℕ) (F : Finset (Multiset (Fin t))), (∀ τ ∈ F, Multiset.card τ = 3) →
    (∀ i : Fin t, ∃ j, ¬ AllowedPair F i j) → PaddedInputs.KeevashPaddedSpec F

end TeoremaBTarget
