/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! The actual first-boundary pivot used in integral flow rounding.
The cycle direction is an explicit input here. Constructing that direction
from a nonintegral graph flow is a separate combinatorial obligation. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingPivot

variable {E W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Move a signed kernel direction until the first coordinate reaches its
box boundary. The entire box and the linear image are preserved. -/
theorem first_boundary (B : (E → ℝ) →ₗ[ℝ] W)
    (f d lower upper : E → ℝ) (s : Finset E) (hs : s.Nonempty)
    (hbox : ∀ e, lower e ≤ f e ∧ f e ≤ upper e)
    (hstrict : ∀ e ∈ s, lower e < f e ∧ f e < upper e)
    (hsign : ∀ e ∈ s, d e = 1 ∨ d e = -1)
    (hzero : ∀ e ∉ s, d e = 0) (hkernel : B d = 0) :
    ∃ t : ℝ, 0 < t ∧
      B (f + t • d) = B f ∧
      (∀ e, lower e ≤ (f + t • d) e ∧ (f + t • d) e ≤ upper e) ∧
      (∀ e ∉ s, (f + t • d) e = f e) ∧
      ∃ e ∈ s, (f + t • d) e = lower e ∨ (f + t • d) e = upper e := by
  classical
  let slack : E → ℝ := fun e => if d e = 1 then upper e - f e else f e - lower e
  let vals := s.image slack
  have hv : vals.Nonempty := hs.image slack
  let t := vals.min' hv
  have htmem : t ∈ vals := Finset.min'_mem vals hv
  obtain ⟨e₀, he₀, heq⟩ := Finset.mem_image.mp htmem
  have htle : ∀ e ∈ s, t ≤ slack e := by
    intro e he
    exact Finset.min'_le vals (slack e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hpos : 0 < t := by
    rw [← heq]
    dsimp [slack]
    split_ifs <;> linarith [hstrict e₀ he₀]
  refine ⟨t, hpos, ?_, ?_, ?_, e₀, he₀, ?_⟩
  · rw [map_add, map_smul, hkernel, smul_zero, add_zero]
  · intro e
    change lower e ≤ f e + t * d e ∧ f e + t * d e ≤ upper e
    by_cases he : e ∈ s
    · have hbound := htle e he
      rcases hsign e he with hp | hn
      · simp only [slack, hp, if_true] at hbound
        rw [hp, mul_one]
        constructor <;> linarith [hbox e]
      · have hn1 : d e ≠ 1 := by rw [hn]; norm_num
        simp only [slack, hn1, if_false] at hbound
        rw [hn, mul_neg_one]
        constructor <;> linarith [hbox e]
    · rw [hzero e he, mul_zero, add_zero]
      exact hbox e
  · intro e he
    change f e + t * d e = f e
    rw [hzero e he, mul_zero, add_zero]
  · change f e₀ + t * d e₀ = lower e₀ ∨ f e₀ + t * d e₀ = upper e₀
    rcases hsign e₀ he₀ with hp | hn
    · right
      simp only [slack, hp, if_true] at heq
      rw [hp, mul_one]
      linarith
    · left
      have hn1 : d e₀ ≠ 1 := by rw [hn]; norm_num
      simp only [slack, hn1, if_false] at heq
      rw [hn, mul_neg_one]
      linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingPivot

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingPivot.first_boundary
