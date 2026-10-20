/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashF12Closed
public import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Assembly

@[expose] public section

/-! # BlowupB.KeevashClosed — the Keevash route closed for F₁, F₂ and F₃

`PaddedF3.keevashPaddedSpec_F3` (the F₃ extension of the PaddedF12 delivery) gives the padded
interface for F₃. Together with `KeevashF12Closed`, all three families of `teoremaB_F123` have
`KeevashTypedSpec`, so Theorem B (ε-balanced, nearly complete, integrally divisible blowups)
holds for F₁, F₂ and F₃ with no remaining hypothesis.
-/

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks

theorem keevashPaddedSpec_F3 : KeevashPaddedSpec F3 := by
  change PaddedInputs.KeevashPaddedSpec F3
  exact PaddedF3.keevashPaddedSpec_F3

theorem keevashTypedSpec_F3 : KeevashTypedSpec F3 :=
  keevashTypedSpec_of_padded (by unfold F3; decide) keevashPaddedSpec_F3

/-- **Theorem B for `F₁`, `F₂`, `F₃`** (ε-balanced, nearly complete), unconditional. -/
theorem teoremaB_F123_closed {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2 ∨ F = F3) :
    ∃ η : ℝ, 0 < η ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, (1 / 4 - η) * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) ∧
          ((univ.filter fun v => p v = i).card : ℝ) ≤ (1 / 4 + η) * Fintype.card V) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset := by
  refine teoremaB_F123 hF ?_
  rcases hF with rfl | rfl | rfl
  · exact keevashTypedSpec_F1
  · exact keevashTypedSpec_F2
  · exact keevashTypedSpec_F3

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_F3
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashTypedSpec_F3
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_F123_closed
