/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingPivot

@[expose] public section

/-! Integral divergence excludes a vertex with exactly one fractional
incident edge. This is the scalar incidence-row argument, independent of
the eventual choice of a graph representation. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingNoLeaf

open scoped BigOperators

/-- An integral signed sum cannot have exactly one nonintegral summand
whose coefficient is a unit. Applied to an incidence row this rules out
degree one in the fractional-edge graph. -/
theorem integral_of_unique_fractional_candidate {E : Type*} [DecidableEq E]
    (s : Finset E) (a : E → ℤ) (f : E → ℝ) (e : E) (he : e ∈ s)
    (ha : a e = 1 ∨ a e = -1)
    (hother : ∀ j ∈ s.erase e, f j ∈ Set.range (Int.cast : ℤ → ℝ))
    (htotal : (∑ j ∈ s, (a j : ℝ) * f j) ∈ Set.range (Int.cast : ℤ → ℝ)) :
    f e ∈ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  have hchoice : ∀ j : E, ∃ z : ℤ, j ∈ s.erase e → (z : ℝ) = f j := by
    intro j
    by_cases hj : j ∈ s.erase e
    · obtain ⟨z, hz⟩ := hother j hj
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => False.elim (hj h)⟩
  choose z hz using hchoice
  let k : ℤ := ∑ j ∈ s.erase e, a j * z j
  have hk : (k : ℝ) = ∑ j ∈ s.erase e, (a j : ℝ) * f j := by
    dsimp [k]
    simp only [Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hz j hj]
  obtain ⟨b, hb⟩ := htotal
  have hsum := Finset.sum_erase_add s (fun j => (a j : ℝ) * f j) he
  rw [← hk, ← hb] at hsum
  rcases ha with hp | hn
  · refine ⟨b - k, ?_⟩
    simp only [hp, Int.cast_one, one_mul] at hsum
    push_cast
    linarith
  · refine ⟨k - b, ?_⟩
    simp only [hn, Int.cast_neg, Int.cast_one, neg_one_mul] at hsum
    push_cast
    linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingNoLeaf

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingNoLeaf.integral_of_unique_fractional_candidate
