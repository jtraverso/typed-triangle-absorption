/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalScalesChiY

@[expose] public section

/-!
# The numerical inputs of the charge layer with charged vertex templates

As `bal_scales_chi`, with `ρT = 2^11 (g + 1) ρ` and
`8 (168 + 168 g) · 1224 ρ n² ≤ Kχ ≤ 8 (168 + 168 g) · 1224 ρ n² + 1` (the active pieces).
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open PaddedGeneral.RealInverse

/-- The extra numerical hypotheses of `component_bal_walk_chi`. -/
structure BalNumericChiYM (ω δ ρ n lam Q θ lamT ρT : ℝ) (N Kχ g C t : ℕ) : Prop where
  lamT_pos : 0 < lamT
  lamT_ω : 1024 * lamT ≤ ω
  ρT_pos : 0 < ρT
  scT : (2 ^ 32 : ℝ) * ρT ≤ lamT ^ 2
  nT : 1 ≤ ρT * n
  d6 : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N) ≤
    6 * lamT * n
  KχB : ((8 * (168 + g * 168) : ℕ) : ℝ) * (1224 * ρ * n ^ 2) ≤ Kχ
  cχ : 9 * (Kχ : ℝ) ≤ 2 ^ 22 * ρT * n ^ 2
  embed : (2 * (97 * (168 + g * 168) : ℕ) + 5 * t : ℝ) + 9 * C + 8 * (δ * n) < ω * n / 2
  deg : max ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N) +
      lamT * n) (δ * n + (30 * C : ℕ)) +
    ((30 * C : ℕ) : ℝ) * ((4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
      44 * (θ + g + g * N) + 44 * (lamT * n)) ≤ 2 * δ * n
  count : 4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + g * N * n + 108 * Kχ +
    (1224 * ρ * n ^ 2 + 11 * N * n + 97 * Kχ) * ((30 * C : ℕ) : ℝ)) ≤ (δ * n) * (ω * n)

set_option maxHeartbeats 8000000 in
/-- **The balanced scales with one global charge and charged vertex templates.** -/
theorem bal_scales_chi_ym (L : ℕ) (ω δ ρ n : ℝ) (hfl : FlexScalesL L ω δ ρ n) (g m C t : ℕ)
    (hL : (2 : ℝ) ^ 40 * ((30 * C + 1) * (g + 1) * (m + 2) * (t + 1)) ≤ 2 ^ L)
    (lam Q Λ0 θ lamT ρT : ℝ) (N Kχ : ℕ)
    (hlamdef : lam = ω ^ 2 * δ / 2 ^ L) (hQdef : Q = 2 ^ 15 * lam * n / ω)
    (hΛdef : Λ0 = 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)))
    (hN1 : 9 * Λ0 ≤ N) (hN2 : (N : ℝ) ≤ 9 * Λ0 + 1) (hθdef : θ = 2 ^ 6 * (g + 1) * N / ω)
    (hlamTdef : lamT = 2 ^ 26 * (g + 1) * δ / 2 ^ L) (hρTdef : ρT = 2 ^ 11 * (g + 1) * ρ)
    (hK1 : ((8 * (168 + g * 168) : ℕ) : ℝ) * (1224 * ρ * n ^ 2) ≤ Kχ)
    (hK2 : (Kχ : ℝ) ≤ ((8 * (168 + g * 168) : ℕ) : ℝ) * (1224 * ρ * n ^ 2) + 1) :
    BalNumericChiYM ω δ ρ n lam Q θ lamT ρT N Kχ g C t := by
  have h := bal_base L ω δ ρ n hfl g lam Q Λ0 θ N hlamdef hQdef hΛdef hN1 hN2 hθdef
  set b := lam * n / ω ^ 2 with hb
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hb0 : 0 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hb1 : 1 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hn := h.n_pos
  have hρ := h.rho_pos
  -- lamT n in units of b
  have hn1 : 1 ≤ n := by nlinarith [h.a12, h.lam_ω, h.ω_le, h.lam_pos]
  have hρn1 : 1 ≤ ρ * n ^ 2 := by
    have := mul_le_mul h.rho_n hn1 zero_le_one (by positivity : (0 : ℝ) ≤ ρ * n)
    nlinarith
  have hlamTn : lamT * n = 2 ^ 26 * (g + 1) * b := by
    have hD : δ * n = 2 ^ L * b := h.D
    have e : lamT * n = 2 ^ 26 * (g + 1) * (δ * n) / 2 ^ L := by rw [hlamTdef]; ring
    rw [e, hD, mul_comm (2 ^ L : ℝ) b, ← mul_assoc, mul_div_assoc, div_self (ne_of_gt h2L),
      mul_one]
  have hlamT0 : 0 < lamT := by rw [hlamTdef]; have := h.δ_pos; positivity
  have hρT0 : 0 < ρT := by rw [hρTdef]; positivity
  -- λ ≤ δ / 2^L
  have hlamL : lam * 2 ^ L ≤ δ := by
    rw [hlamdef]; field_simp
    have : ω ^ 2 ≤ 1 := pow_le_one₀ h.ω_pos.le h.ω_le
    nlinarith [h.δ_pos]
  have hlamTlam : 2 ^ 26 * lam ≤ lamT := by
    rw [hlamTdef, le_div_iff₀ h2L]
    have hδ := h.δ_pos
    nlinarith [mul_nonneg hg0 hδ.le]
  -- the constants against 2^L
  have hP1 : (2 : ℝ) ^ 40 * ((30 * C + 1) * (g + 1)) ≤ 2 ^ L := by
    have h1 : (30 * (C : ℝ) + 1) * (g + 1) ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have hx : (0 : ℝ) ≤ (30 * C + 1) * (g + 1) := by positivity
      have h2 : (1 : ℝ) ≤ (m + 2) * (t + 1) := by nlinarith
      nlinarith
    nlinarith
  have hP3 : (2 : ℝ) ^ 40 * (((g : ℝ) + 1) * (t + 1) + C) ≤ 2 ^ L := by
    have : ((g : ℝ) + 1) * (t + 1) + C ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have e : (30 * (C : ℝ) + 1) * (g + 1) * (m + 2) * (t + 1) =
          ((g + 1) * (t + 1)) * ((30 * C + 1) * (m + 2)) := by ring
      rw [e]
      have h0 : (1 : ℝ) ≤ (g + 1) * (t + 1) := by nlinarith
      have h1 : 2 + (C : ℝ) ≤ (30 * C + 1) * (m + 2) := by nlinarith
      nlinarith
    nlinarith
  have hDb : δ * n = 2 ^ L * b := h.D
  have hW : 2 ^ 63 * (δ * n) ≤ ω * n := h.W
  have hgN : (g : ℝ) * N ≤ g * (2 ^ 21 * b) := mul_le_mul_of_nonneg_left h.Nb hg0
  have hρnb : ρ * n ≤ b := (mul_le_mul_of_nonneg_right h.rho_lam hn.le).trans h.ab
  have hfirst0 : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N) ≤
      2 ^ 28 * (g + 1) * b := by
    have := h.Qb; have := h.ab; have := h.θb
    nlinarith
  have hρn2 : ρ * n ^ 2 ≤ b * (ω * n) := h.rnn
  have hKb : (Kχ : ℝ) ≤ 2 ^ 22 * ((g + 1) * (b * (ω * n))) := by
    have hK2' := hK2
    push_cast at hK2'
    have hX1 : 1 ≤ b * (ω * n) := le_trans hρn1 hρn2
    have hgX : (g + 1) * (ρ * n ^ 2) ≤ (g + 1) * (b * (ω * n)) :=
      mul_le_mul_of_nonneg_left hρn2 (by positivity)
    have hX0' : (0 : ℝ) ≤ (g + 1) * (b * (ω * n)) := by positivity
    nlinarith
  refine ⟨hlamT0, ?_, hρT0, ?_, ?_, ?_, hK1, ?_, ?_, ?_, ?_⟩
  · -- 1024 lamT ≤ ω
    have : 1024 * (lamT * n) ≤ ω * n := by
      rw [hlamTn]
      have : 2 ^ 36 * (g + 1) * b ≤ 2 ^ 63 * (2 ^ L * b) := by
        have hx : (g : ℝ) + 1 ≤ 2 ^ L := by nlinarith
        nlinarith
      rw [← hDb] at this
      linarith
    nlinarith
  · -- 2^32 ρT ≤ lamT²
    rw [hρTdef]
    have h1 : 2 ^ 24 * ρ ≤ lam ^ 2 := h.scale
    have hge : 2 ^ 26 * (g + 1) * lam ≤ lamT := by
      have e1 : lamT * n = 2 ^ 26 * (g + 1) * b := hlamTn
      have e2 : lam * n ≤ b := h.ab
      have : 2 ^ 26 * (g + 1) * lam * n ≤ lamT * n := by
        rw [e1]; have := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 2 ^ 26 * (g + 1))
        nlinarith
      exact le_of_mul_le_mul_right this hn
    have h2 : (2 ^ 26 * (g + 1) * lam) ^ 2 ≤ lamT ^ 2 := by
      have : 0 ≤ 2 ^ 26 * (g + 1) * lam := by have := h.lam_pos; positivity
      nlinarith
    have hg1 : (1 : ℝ) ≤ g + 1 := by linarith
    have hρ0 := h.rho_pos
    have h3 : (g + 1) * (2 ^ 24 * ρ) ≤ (g + 1) ^ 2 * lam ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ g + 1)
      nlinarith [sq_nonneg lam]
    nlinarith
  · rw [hρTdef]; have := h.rho_n; have := h.rho_pos; nlinarith
  · -- d6
    rw [show 6 * lamT * n = 6 * (lamT * n) by ring, hlamTn]
    nlinarith
  · -- cχ
    rw [hρTdef]
    have hK2' := hK2
    push_cast at hK2'
    have hgr : ρ * n ^ 2 ≤ (g + 1) * (ρ * n ^ 2) := by nlinarith
    nlinarith
  · -- embed
    push_cast
    have hcons : 2 * (97 * (168 + (g : ℝ) * 168)) + 5 * t + 9 * C ≤
        2 ^ 15 * (((g : ℝ) + 1) * (t + 1) + C) := by
      nlinarith [mul_nonneg hg0 ht0]
    have hD0 : 0 ≤ δ * n := by rw [hDb]; positivity
    have hDP : 2 ^ L ≤ δ * n := by rw [hDb]; nlinarith
    nlinarith
  · -- deg
    push_cast
    have hfirst : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) +
        (θ + g + g * N) + lamT * n ≤ δ * n := by
      rw [hlamTn, hDb]
      have : (2 ^ 28 + 2 ^ 26) * (g + 1) * b ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b := by
        have hx : 0 ≤ (g + 1) * b := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hP1 hb0]
    have hC30 : 30 * (C : ℝ) ≤ δ * n / 2 := by
      rw [hDb]
      have : 30 * (C : ℝ) * 2 ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b := by
        have hx : 1 ≤ (g + 1) * b := by nlinarith
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hP1 hb0]
    have hmax : max ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) +
        (θ + g + g * N) + lamT * n) (δ * n + 30 * C) ≤ δ * n + 30 * C :=
      max_le (by linarith) le_rfl
    have hload : (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + 44 * (θ + g + g * N) +
        44 * (lamT * n) ≤ 2 ^ 35 * (g + 1) * b := by
      have := h.Qb; have := h.ab; have := h.θb
      rw [hlamTn]
      nlinarith
    have hprod : 30 * (C : ℝ) * ((4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
        44 * (θ + g + g * N) + 44 * (lamT * n)) ≤ δ * n / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hload (by positivity : (0 : ℝ) ≤ 30 * C)
      rw [hDb]
      have h2 : 30 * (C : ℝ) * (2 ^ 35 * (g + 1) * b) ≤
          2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b / 2 := by
        have hx : 0 ≤ (g + 1) * b := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hP1 hb0]
    linarith
  · -- count
    push_cast
    have hWn : 0 ≤ ω * n := le_of_lt (mul_pos h.ω_pos hn)
    set X := b * (ω * n) with hX
    have hX0 : 0 ≤ X := mul_nonneg hb0 hWn
    have h1 : (g : ℝ) * N * n ≤ g * (2 ^ 21 * X) := by
      have := mul_le_mul_of_nonneg_left h.Nn hg0
      rw [hX]; nlinarith
    have h2 : 1224 * ρ * n ^ 2 + 11 * N * n + 97 * Kχ ≤
        1224 * X + 11 * (2 ^ 21 * X) + 97 * (2 ^ 22 * ((g + 1) * X)) := by
      have := h.Nn
      rw [hX]; nlinarith
    have h3 : (1224 * ρ * n ^ 2 + 11 * N * n + 97 * Kχ) * (30 * C) ≤
        (1224 * X + 11 * (2 ^ 21 * X) + 97 * (2 ^ 22 * ((g + 1) * X))) * (30 * C) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hsum : 4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + g * N * n + 108 * Kχ +
        (1224 * ρ * n ^ 2 + 11 * N * n + 97 * Kχ) * (30 * C)) ≤
        2 ^ 38 * ((30 * C + 1) * (g + 1)) * X := by
      have := h.lnn
      nlinarith [mul_nonneg hg0 hX0, mul_nonneg hC0 hX0, mul_nonneg (mul_nonneg hC0 hg0) hX0]
    have hfin : 2 ^ 38 * ((30 * (C : ℝ) + 1) * (g + 1)) * X ≤ (δ * n) * (ω * n) := by
      rw [hDb]
      have : 2 ^ 38 * ((30 * (C : ℝ) + 1) * (g + 1)) * X ≤ 2 ^ L * X :=
        mul_le_mul_of_nonneg_right (by nlinarith) hX0
      rw [hX] at this ⊢
      nlinarith
    linarith

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_scales_chi_ym
