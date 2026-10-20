/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPerm
public import PartitionedTriangleAbsorption.BlowupB.KeevashClosed

@[expose] public section

/-! Application-family specializations of the generic relabelling theorem. -/

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks

/-! ### Corollaries for the relabelled F₁, F₂, F₃ -/

theorem keevashPaddedSpec_F123 {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2 ∨ F = F3) :
    KeevashPaddedSpec F := by
  rcases hF with rfl | rfl | rfl
  · exact keevashPaddedSpec_F1
  · exact keevashPaddedSpec_F2
  · exact keevashPaddedSpec_F3

theorem card_three_F123 {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2 ∨ F = F3) :
    ∀ τ ∈ F, Multiset.card τ = 3 := by
  rcases hF with rfl | rfl | rfl
  · unfold F1; decide
  · unfold F2; decide
  · unfold F3; decide

theorem two_completions_F123 {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2 ∨ F = F3) :
    ∀ a b : Fin 4, AllowedPair F a b →
      (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) ∈ F).card = 2 := by
  rcases hF with rfl | rfl | rfl
  · exact two_completions_F1
  · exact two_completions_F2
  · exact two_completions_F3

/-- **Theorem B for every relabelling of F₁, F₂, F₃** (ε-balanced, nearly complete),
unconditional. -/
theorem teoremaB_perm_F123 (σ : Equiv.Perm (Fin 4)) {F₀ : Finset (Multiset (Fin 4))}
    (hF₀ : F₀ = F1 ∨ F₀ = F2 ∨ F₀ = F3) :
    ∃ η : ℝ, 0 < η ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair (permFam σ F₀) (p u) (p v)) →
        (∀ v, missDeg p (permFam σ F₀) G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, (1 / 4 - η) * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) ∧
          ((univ.filter fun v => p v = i).card : ℝ) ≤ (1 / 4 + η) * Fintype.card V) →
        IsIntDiv p (permFam σ F₀) G.edgeFinset → HasDecomp p (permFam σ F₀) G.edgeFinset := by
  have hK : KeevashTypedSpec (permFam σ F₀) :=
    keevashTypedSpec_of_padded (card_three_perm σ (card_three_F123 hF₀))
      (keevashPaddedSpec_perm σ (keevashPaddedSpec_F123 hF₀))
  have hw : BalancedWeights (permFam σ F₀) (fun _ => 2) := by
    refine balancedWeights_two fun a b hab => ?_
    rw [completions_perm]
    exact two_completions_F123 hF₀ _ _ (allowed_perm σ hab)
  have := teoremaB_balanced hK (fun _ => 2) hw (by norm_num)
  simpa using this


end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_perm_F123
