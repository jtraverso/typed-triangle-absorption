/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Scales

@[expose] public section

/-! Restricting to a supplied induced component loses no flexible-scale exponent:
rescale densities by n/n', keeping every absolute degree and supply budget fixed.
This is numerical transport, not a producer of a core absorber. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open PaddedGeneral.RealInverse

theorem core_scales {L : ℕ} {ω δ ρ n n' : ℝ}
    (h : FlexScalesL L ω δ ρ n) (hsmall : n' ≤ n) (hsupply : ω * n ≤ n') :
    FlexScalesL L (ω * n / n') (δ * n / n') (ρ * n / n') n' := by
  have hn : 0 < n := by
    have hne : n ≠ 0 := by intro hz; have := h.ρn; norm_num [hz] at this
    exact lt_of_le_of_ne h.n_nonneg (Ne.symm hne)
  have hn' : 0 < n' := lt_of_lt_of_le (mul_pos h.ω_pos hn) hsupply
  let x := n / n'
  have hx : 1 ≤ x := (le_div_iff₀ hn').mpr (by simpa using hsmall)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have eω : ω * n / n' = ω * x := by dsimp [x]; ring
  have eδ : δ * n / n' = δ * x := by dsimp [x]; ring
  have eρ : ρ * n / n' = ρ * x := by dsimp [x]; ring
  rw [eω, eδ, eρ]
  refine ⟨mul_pos h.ω_pos hx0, ?_, mul_pos h.δ_pos hx0, ?_, ?_, hn'.le, ?_⟩
  · rw [← eω, div_le_one hn']
    exact hsupply
  · have hh := mul_le_mul_of_nonneg_right h.δ_le hx0.le
    nlinarith
  · let P := (ω ^ 2 * δ / 2 ^ L) ^ 2
    have hP : 0 ≤ P := sq_nonneg _
    have hpow : x ≤ x ^ 6 := by
      calc x ≤ x * x ^ 5 := le_mul_of_one_le_right hx0.le (one_le_pow₀ hx)
        _ = x ^ 6 := by ring
    have h1 := mul_le_mul_of_nonneg_right h.ρ_sq hx0.le
    have h2 := mul_le_mul_of_nonneg_left hpow hP
    have heq : ((ω * x) ^ 2 * (δ * x) / 2 ^ L) ^ 2 = P * x ^ 6 := by
      dsimp [P]
      ring
    rw [heq]
    nlinarith
  · have heq : ρ * x * n' = ρ * n := by dsimp [x]; field_simp
    rw [heq]
    exact h.ρn

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17
