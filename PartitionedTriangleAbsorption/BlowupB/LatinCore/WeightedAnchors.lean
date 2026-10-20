/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Finite greedy placement of weighted anchors. All endpoint weights are
charged on assignment, before any paths are embedded. Candidate sets are
concrete finite sets, not an embedding oracle. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedAnchors

open Finset

variable {J V : Type} [DecidableEq J] [Fintype V] [DecidableEq V] [Nonempty V]

def load (initial : V → ℝ) (weight : J → ℝ) (f : J → V)
    (S : Finset J) (v : V) : ℝ :=
  initial v + ∑ j ∈ S, if f j = v then weight j else 0

theorem load_nonneg (initial : V → ℝ) (weight : J → ℝ) (f : J → V)
    (S : Finset J) (hi : ∀ v, 0 ≤ initial v) (hw : ∀ j, 0 ≤ weight j) (v : V) :
    0 ≤ load initial weight f S v := by
  unfold load
  exact add_nonneg (hi v) (sum_nonneg fun j _ => by split_ifs <;> simp_all)

theorem total (initial : V → ℝ) (weight : J → ℝ) (f : J → V) (S : Finset J) :
    ∑ v, load initial weight f S v = (∑ v, initial v) + ∑ j ∈ S, weight j := by
  simp only [load, sum_add_distrib]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  simp only [sum_ite_eq, sum_ite_eq', mem_univ, ite_true]

/-- Fixed candidate supplies suffice to place every finite list of anchors.
The cap accounts for the final anchor placed at a vertex. -/
theorem exists_placement (S : Finset J) (candidates : J → Finset V)
    (weight : J → ℝ) (initial : V → ℝ) (a T W M : ℝ)
    (hT : 0 < T) (hW : 0 ≤ W)
    (hi : ∀ v, 0 ≤ initial v) (hicap : ∀ v, initial v ≤ T)
    (hw : ∀ j, 0 ≤ weight j) (hwcap : ∀ j, weight j ≤ W)
    (hsupply : ∀ j, a ≤ (candidates j).card)
    (hbudget : M < a * T)
    (hmass : (∑ v, initial v) + ∑ j ∈ S, weight j ≤ M) :
    ∃ f : J → V, (∀ j ∈ S, f j ∈ candidates j) ∧
      (∀ v, load initial weight f S v ≤ T + W) ∧
      (∑ v, load initial weight f S v) ≤ M := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => Classical.arbitrary V, by simp, ?_, ?_⟩
      · intro v
        simp only [load, sum_empty, add_zero]
        linarith [hicap v]
      · simpa only [total, sum_empty, add_zero] using hmass
  | @insert j S hj ih =>
      have hmassS : (∑ v, initial v) + ∑ k ∈ S, weight k ≤ M := by
        rw [sum_insert hj] at hmass
        linarith [hw j]
      obtain ⟨f, hf, hcap, htotal⟩ := ih hmassS
      let Q := load initial weight f S
      have hQ : ∀ v, 0 ≤ Q v := load_nonneg initial weight f S hi hw
      have hlight : ∃ v ∈ candidates j, Q v < T := by
        by_contra h
        have hheavy : ∀ v ∈ candidates j, T ≤ Q v := by
          intro v hv
          exact le_of_not_gt (fun hvT => h ⟨v,hv,hvT⟩)
        have hcount : (candidates j).card * T ≤ M := by
          calc _ = ∑ v ∈ candidates j, T := by simp
            _ ≤ ∑ v ∈ candidates j, Q v := sum_le_sum hheavy
            _ ≤ ∑ v, Q v := sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun v _ _ => hQ v)
            _ ≤ M := htotal
        have hh := mul_le_mul_of_nonneg_right (hsupply j) hT.le
        linarith
      obtain ⟨v, hv, hvT⟩ := hlight
      let f' := Function.update f j v
      have heq : ∀ r, load initial weight f' (insert j S) r =
          Q r + if v = r then weight j else 0 := by
        intro r
        have hsame : (∑ k ∈ S, if f' k = r then weight k else 0) =
            ∑ k ∈ S, if f k = r then weight k else 0 := by
          apply sum_congr rfl
          intro k hk
          have hkj : k ≠ j := by intro h; subst k; exact hj hk
          simp only [f', Function.update_of_ne hkj]
        change initial r + (∑ k ∈ insert j S, if f' k = r then weight k else 0) = _
        rw [sum_insert hj]
        have hfj : f' j = v := by simp [f']
        rw [hfj]
        change initial r + ((if v = r then weight j else 0) +
          ∑ k ∈ S, if f' k = r then weight k else 0) = _
        rw [hsame]
        dsimp [Q, load]
        ring
      refine ⟨f', ?_, ?_, ?_⟩
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · simpa [f'] using hv
        · have hkj : k ≠ j := by intro h; subst k; exact hj hk
          simpa only [f', Function.update_of_ne hkj] using hf k hk
      · intro r
        rw [heq r]
        split_ifs with hvr
        · subst r
          linarith [hwcap j]
        · simpa using hcap r
      · rw [total]
        exact hmass

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedAnchors

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedAnchors.exists_placement
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedAnchors.exists_placement
