/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalScales

@[expose] public section

/-!
# The numerical inputs of the balanced component certificate with a torsion layer

`bal_base_t`: the base estimates `BalBase` hold with `b' = 64 b` and `P' = 2^L / 64` for every
`N ≤ 576 Λ0 + 1` (the torsion layer multiplies the vertex loads by `q ≤ 12` and adds its tokens).
`tors_scales`: with `lamT = Λ0 / n`, `ρT = 2^11 ρ` and `9 (q Λ0 + 4 q Λ0) ≤ N ≤ 45 q Λ0 + 1`, the
hypotheses of `component_bal_walk_tors` hold when `2^46 (30 C + 1)(g + 1)(m + 2)(t + 1) ≤ 2^L`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open PaddedGeneral.RealInverse

set_option maxHeartbeats 4000000 in
theorem bal_base_t (L : ℕ) (hL6 : 6 ≤ L) (ω δ ρ n : ℝ) (hfl : FlexScalesL L ω δ ρ n) (g : ℕ)
    (lam Q Λ0 θ : ℝ) (N : ℕ)
    (hlamdef : lam = ω ^ 2 * δ / 2 ^ L) (hQdef : Q = 2 ^ 15 * lam * n / ω)
    (hΛdef : Λ0 = 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)))
    (hN1 : 9 * Λ0 ≤ N) (hN2 : (N : ℝ) ≤ 576 * Λ0 + 1) (hθdef : θ = 2 ^ 6 * (g + 1) * N / ω) :
    BalBase ω δ ρ n lam Q Λ0 θ (64 * (lam * n / ω ^ 2)) (2 ^ L / 64) N g := by
  have hΛ0 : 0 ≤ 9 * Λ0 := by
    have := hfl.n_nonneg; have := hfl.ω_pos
    have hlam : 0 ≤ lam := by rw [hlamdef]; have := hfl.δ_pos; positivity
    have hQ : 0 ≤ Q := by rw [hQdef]; positivity
    rw [hΛdef]; positivity
  set N0 : ℕ := ⌈9 * Λ0⌉₊ with hN0
  have h0 := bal_base L ω δ ρ n hfl g lam Q Λ0 (2 ^ 6 * (g + 1) * N0 / ω) N0 hlamdef hQdef hΛdef
    (Nat.le_ceil _) (Nat.ceil_lt_add_one hΛ0).le rfl
  set b : ℝ := lam * n / ω ^ 2 with hb
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hω := h0.ω_pos
  have hn := h0.n_pos
  have hb0 : 0 ≤ b := le_trans (by norm_num) (h0.a12.trans h0.ab)
  have hbω : b * ω ^ 2 = lam * n := by rw [hb]; field_simp
  have hω2 : ω ^ 2 ≤ ω := pow_le_of_le_one hω.le h0.ω_le (by norm_num)
  have hlamn : lam * n ≤ b * ω := by
    rw [← hbω]; exact mul_le_mul_of_nonneg_left hω2 hb0
  have hQbω : Q = 2 ^ 15 * (b * ω) := by
    have := h0.Qω
    have e : Q * ω = 2 ^ 15 * (b * ω) * ω := by rw [this, ← hbω]; ring
    exact mul_right_cancel₀ hω.ne' e
  have h1153 : (1153 : ℝ) ≤ b * ω := by
    have := h0.a12
    linarith
  have hNω : (N : ℝ) ≤ 2 ^ 27 * b * ω := by
    have e : 576 * Λ0 + 1 = 576 * 12288 * (lam * n) + 1152 * Q + 1153 := by rw [hΛdef]; ring
    rw [e, hQbω] at hN2
    linarith
  have hθω : θ * ω = 2 ^ 6 * (g + 1) * N := by rw [hθdef]; field_simp
  have hNpos : (1 : ℝ) ≤ N := by have := h0.Λpos; linarith
  have h2L6 : (2 : ℝ) ^ 6 ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL6
  refine ⟨h0.ω_pos, h0.ω_le, h0.δ_pos, h0.n_pos, h0.lam_pos, h0.lam_ω, h0.rho_pos, h0.rho_lam,
    h0.rho_n, h0.scale, h0.a12, by linarith [h0.ab], ?_, ?_, h0.W, h0.Qpos, h0.Qω,
    by linarith [h0.Qb], by linarith [h0.Λb], h0.Λpos, hNpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [h0.D]; ring
  · -- N ≤ 2^21 (64 b)
    have : b * ω ≤ b := by nlinarith [h0.ω_le]
    linarith
  · rw [hθdef]; positivity
  · -- θ ≤ 2^27 (g + 1) (64 b)
    rw [← mul_le_mul_iff_of_pos_right hω, hθω]
    have h1 : 2 ^ 6 * ((g : ℝ) + 1) * N ≤ 2 ^ 6 * (g + 1) * (2 ^ 27 * b * ω) :=
      mul_le_mul_of_nonneg_left hNω (by positivity)
    linarith
  · -- 2 g N n / θ ≤ ω n / 32
    have e : 2 * (g : ℝ) * N * n / θ = 2 * g * (ω * n) / (2 ^ 6 * (g + 1)) := by
      rw [hθdef]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hWn : (0 : ℝ) ≤ ω * n := by positivity
    linarith [mul_nonneg hg0 hWn]
  · have := h0.lnn; have : (0 : ℝ) ≤ b * (ω * n) := by positivity
    linarith
  · have := h0.rnn; have : (0 : ℝ) ≤ b * (ω * n) := by positivity
    linarith
  · -- N n ≤ 2^21 (64 b) (ω n)
    have := mul_le_mul_of_nonneg_right hNω hn.le
    linarith

/-- The numerical hypotheses of `component_bal_walk_tors`, for `n` vertices and `γ = ω`. -/
structure TorsNumeric (ω δ ρ n lam Q θ lamT ρT : ℝ) (N g m C t q : ℕ) : Prop where
  lam_pos : 0 < lam
  lam_le : lam ≤ 1 / 64
  rho_pos : 0 < ρ
  scale : 2 ^ 24 * ρ ≤ lam ^ 2
  n1 : 1 ≤ ρ * n
  n2 : 256 ≤ lam * n
  δ_pos : 0 < δ
  Q_pos : 0 < Q
  θ_pos : 0 < θ
  lam_ω : 64 * lam ≤ ω
  path : 3 * (4100 * lam * n ^ 2) / Q + 3 +
    2 * (2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 2) < ω * n
  γ1 : ω ≤ 1
  lamT_pos : 0 < lamT
  lamT_ω : 1024 * lamT ≤ ω
  ρT_pos : 0 < ρT
  scT : (2 ^ 32 : ℝ) * ρT ≤ lamT ^ 2
  nT : 1 ≤ ρT * n
  d6 : 2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) ≤ 6 * lamT * n
  cT : (q : ℝ) * (1224 * ρ * n ^ 2) ≤ 2 ^ 22 * ρT * n ^ 2
  NΛ : 9 * (q * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + 4 * q * (lamT * n)) ≤ N
  bud : ((m + 1 : ℕ) : ℝ) + (2 * g * N * n / θ + ((m + 1 : ℕ) : ℝ) * N) +
    ((m + 1 : ℕ) : ℝ) * (((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) +
      lamT * n) + θ + g + 2 * g * N) < ω * n
  embed : (2 * ((168 + 3 * q * 6) + g * (168 + 3 * q * 6) : ℕ) + 5 * t : ℝ) + 9 * C +
    8 * (δ * n) < ω * n / 2
  deg : max (((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + lamT * n) +
      (θ + g + g * N)) (δ * n + (30 * C : ℕ)) +
    ((30 * C : ℕ) : ℝ) * ((q * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
      4 * q * (lamT * n)) + 44 * (θ + g + g * N)) ≤ 2 * δ * n
  count : 4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + 6 * (q * (1224 * ρ * n ^ 2)) + g * N * n +
    (2 * q * (1224 * ρ * n ^ 2) + 11 * N * n) * ((30 * C : ℕ) : ℝ)) ≤ (δ * n) * (ω * n)

set_option maxHeartbeats 8000000 in
/-- **The torsion scales.** -/
theorem tors_scales (L : ℕ) (ω δ ρ n : ℝ) (hfl : FlexScalesL L ω δ ρ n) (g m C t q : ℕ)
    (hq1 : 1 ≤ q) (hq12 : q ≤ 12)
    (hL : (2 : ℝ) ^ 46 * ((30 * C + 1) * (g + 1) * (m + 2) * (t + 1)) ≤ 2 ^ L)
    (lam Q Λ0 θ lamT ρT : ℝ) (N : ℕ)
    (hlamdef : lam = ω ^ 2 * δ / 2 ^ L) (hQdef : Q = 2 ^ 15 * lam * n / ω)
    (hΛdef : Λ0 = 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)))
    (hN1 : 9 * (q * Λ0 + 4 * q * Λ0) ≤ N) (hN2 : (N : ℝ) ≤ 9 * (q * Λ0 + 4 * q * Λ0) + 1)
    (hθdef : θ = 2 ^ 6 * (g + 1) * N / ω) (hlamTdef : lamT = Λ0 / n) (hρTdef : ρT = 2 ^ 11 * ρ) :
    TorsNumeric ω δ ρ n lam Q θ lamT ρT N g m C t q := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqc : (q : ℝ) ≤ 12 := by exact_mod_cast hq12
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hL6 : 6 ≤ L := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ L ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (1 : ℝ) ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have h1 : (1 : ℝ) ≤ (30 * C + 1) * (g + 1) := by nlinarith
      have h2 : (1 : ℝ) ≤ (m + 2) * (t + 1) := by nlinarith
      nlinarith
    linarith
  have hΛ0 : 0 ≤ Λ0 := by
    have := hfl.n_nonneg; have := hfl.ω_pos
    have hlam : 0 ≤ lam := by rw [hlamdef]; have := hfl.δ_pos; positivity
    have hQ : 0 ≤ Q := by rw [hQdef]; positivity
    rw [hΛdef]; positivity
  have hN1' : 9 * Λ0 ≤ N := by nlinarith
  have hN2' : (N : ℝ) ≤ 576 * Λ0 + 1 := by nlinarith
  have h := bal_base_t L hL6 ω δ ρ n hfl g lam Q Λ0 θ N hlamdef hQdef hΛdef hN1' hN2' hθdef
  set b : ℝ := 64 * (lam * n / ω ^ 2) with hb
  set P : ℝ := 2 ^ L / 64 with hP
  have hn := h.n_pos
  have hb1 : 1 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hb0 : 0 ≤ b := by linarith
  have hDb : δ * n = P * b := h.D
  have hPL : (2 : ℝ) ^ 40 * ((30 * C + 1) * (g + 1) * (m + 2) * (t + 1)) ≤ P := by
    rw [hP, le_div_iff₀ (by norm_num)]; linarith
  have hA1 : (1 : ℝ) ≤ (30 * C + 1) * (g + 1) := by nlinarith
  have hA2 : (1 : ℝ) ≤ (m + 2) * (t + 1) := by nlinarith
  have hP1 : (2 : ℝ) ^ 40 * ((30 * C + 1) * (g + 1)) ≤ P := by
    have : (30 * (C : ℝ) + 1) * (g + 1) ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have e : (30 * (C : ℝ) + 1) * (g + 1) * (m + 2) * (t + 1) =
          ((30 * C + 1) * (g + 1)) * ((m + 2) * (t + 1)) := by ring
      rw [e]; nlinarith
    linarith
  have hP2 : (2 : ℝ) ^ 40 * ((g + 1) * (m + 2)) ≤ P := by
    have : ((g : ℝ) + 1) * (m + 2) ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have h0 : (0 : ℝ) ≤ (g + 1) * (m + 2) := by positivity
      have h1 : (1 : ℝ) ≤ (30 * C + 1) * (t + 1) := by nlinarith
      nlinarith
    linarith
  have hP3 : (2 : ℝ) ^ 40 * (((g : ℝ) + 1) * (t + 1) + C) ≤ P := by
    have : ((g : ℝ) + 1) * (t + 1) + C ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have e : (30 * (C : ℝ) + 1) * (g + 1) * (m + 2) * (t + 1) =
          ((g + 1) * (t + 1)) * ((30 * C + 1) * (m + 2)) := by ring
      rw [e]
      have h0 : (1 : ℝ) ≤ (g + 1) * (t + 1) := by nlinarith
      have h1 : 2 + (C : ℝ) ≤ (30 * C + 1) * (m + 2) := by nlinarith
      nlinarith
    linarith
  have hlamTn : lamT * n = Λ0 := by rw [hlamTdef, div_mul_cancel₀ _ hn.ne']
  have hΛb := h.Λb
  have hQb := h.Qb
  have hρnb : ρ * n ≤ b := (mul_le_mul_of_nonneg_right h.rho_lam hn.le).trans h.ab
  have hd0 : 2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) ≤ Λ0 := by
    rw [hΛdef]
    have := mul_le_mul_of_nonneg_right h.rho_lam hn.le
    have := h.a12
    linarith
  have hW : 2 ^ 63 * (δ * n) ≤ ω * n := h.W
  have hgN : (g : ℝ) * N ≤ g * (2 ^ 21 * b) := mul_le_mul_of_nonneg_left h.Nb hg0
  -- the first-order quantity
  have hfirst : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + lamT * n) +
      (θ + g + g * N) ≤ 2 ^ 29 * (g + 1) * b := by
    rw [hlamTn]
    have := h.θb
    linarith [mul_le_mul_of_nonneg_left hb1 hg0, mul_nonneg hg0 hb0]
  refine ⟨h.lam_pos, by linarith [h.lam_ω, h.ω_le], h.rho_pos, h.scale, h.rho_n,
    by linarith [h.a12], h.δ_pos, h.Qpos, h.θpos, h.lam_ω, est_path h, h.ω_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlamTdef]; have := h.Λpos; positivity
  · -- 1024 lamT ≤ ω
    rw [hlamTdef, mul_div_assoc', div_le_iff₀ hn]
    have : 1024 * (2 ^ 17 * b) ≤ ω * n := by
      have h1 : 2 ^ 63 * (P * b) ≤ ω * n := by rw [← hDb]; exact hW
      have h2 : (1 : ℝ) ≤ P := le_trans (by linarith) hP1
      nlinarith
    linarith
  · rw [hρTdef]; have := h.rho_pos; positivity
  · -- 2^32 ρT ≤ lamT²
    rw [hρTdef]
    have hQn : 2 ^ 16 * lam ≤ lamT := by
      rw [hlamTdef, le_div_iff₀ hn, hΛdef]
      have hQω := h.Qω
      have hQ' : 2 ^ 15 * (lam * n) ≤ Q := by
        have := h.ω_le; have := h.Qpos
        nlinarith
      linarith [h.lam_pos]
    have h1 : (2 ^ 16 * lam) ^ 2 ≤ lamT ^ 2 := by
      have : 0 ≤ 2 ^ 16 * lam := by have := h.lam_pos; positivity
      nlinarith
    have := h.scale
    nlinarith
  · rw [hρTdef]; linarith [h.rho_n]
  · -- d6
    rw [show 6 * lamT * n = 6 * (lamT * n) by ring, hlamTn]
    linarith
  · -- cT
    rw [hρTdef]
    have : 0 ≤ ρ * n ^ 2 := by have := h.rho_pos; positivity
    nlinarith
  · -- NΛ
    rw [hlamTn, ← hΛdef]
    exact hN1
  · -- bud
    have hθN := h.θN
    have hNb := h.Nb
    have hm1 : ((m + 1 : ℕ) : ℝ) = m + 1 := by push_cast; ring
    rw [hm1]
    have hsum : (m + 1 : ℝ) + (m + 1) * N + (m + 1) * ((2 * ρ * n + (4 * lam * n +
        2 * (Q + (4096 * lam * n + 1)))) + lamT * n + θ + g + 2 * g * N) ≤
        2 ^ 31 * ((g + 1) * (m + 2)) * b := by
      have hx : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + lamT * n + θ + g +
          2 * g * N ≤ 2 ^ 30 * (g + 1) * b := by linarith [mul_nonneg hg0 hb0]
      have hm2 : (0 : ℝ) ≤ m + 1 := by positivity
      have := mul_le_mul_of_nonneg_left hx hm2
      nlinarith [mul_nonneg hm0 hb0, mul_nonneg hg0 hb0, mul_nonneg (mul_nonneg hm0 hg0) hb0]
    have hfin : 2 ^ 31 * (((g : ℝ) + 1) * (m + 2)) * b < ω * n / 2 := by
      have h1 : 2 ^ 63 * (P * b) ≤ ω * n := by rw [← hDb]; exact hW
      have h2 : 2 ^ 40 * (((g : ℝ) + 1) * (m + 2)) * b ≤ P * b :=
        mul_le_mul_of_nonneg_right hP2 hb0
      have hpos : 0 < ((g : ℝ) + 1) * (m + 2) * b := by positivity
      linarith
    have hωn : 0 < ω * n := mul_pos h.ω_pos hn
    linarith
  · -- embed
    push_cast
    have hcons : 2 * ((168 + 3 * (q : ℝ) * 6) + g * (168 + 3 * q * 6)) + 5 * t + 9 * C ≤
        2 ^ 10 * (((g : ℝ) + 1) * (t + 1) + C) := by
      linarith [mul_nonneg hg0 ht0, mul_le_mul_of_nonneg_left hqc hg0]
    have hD0 : 0 ≤ δ * n := by rw [hDb]; positivity
    have hDP : 2 ^ 40 * (((g : ℝ) + 1) * (t + 1) + C) ≤ δ * n := by
      rw [hDb]; linarith [mul_le_mul_of_nonneg_left hb1 (le_trans (by positivity) hP3)]
    nlinarith
  · -- deg
    push_cast
    have hfd : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + lamT * n) +
        (θ + g + g * N) ≤ δ * n := by
      rw [hDb]
      have : 2 ^ 29 * ((g : ℝ) + 1) * b ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b := by
        have hx : 0 ≤ (g + 1) * b := by positivity
        nlinarith
      linarith [mul_le_mul_of_nonneg_right hP1 hb0]
    have hC30 : 30 * (C : ℝ) ≤ δ * n / 2 := by
      rw [hDb]
      have : 30 * (C : ℝ) * 2 ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b := by
        have hx : 1 ≤ (g + 1) * b := by nlinarith
        nlinarith
      linarith [mul_le_mul_of_nonneg_right hP1 hb0]
    have hmax : max ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + lamT * n) +
        (θ + g + g * N)) (δ * n + 30 * C) ≤ δ * n + 30 * C :=
      max_le (by linarith) le_rfl
    have hload : (q * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + 4 * q * (lamT * n)) +
        44 * (θ + g + g * N) ≤ 2 ^ 35 * (g + 1) * b := by
      rw [hlamTn, ← hΛdef]
      have := h.θb
      have : (q : ℝ) * Λ0 ≤ 12 * (2 ^ 17 * b) := by nlinarith
      linarith [mul_le_mul_of_nonneg_left hb1 hg0, mul_nonneg hg0 hb0]
    have hprod : 30 * (C : ℝ) * ((q * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
        4 * q * (lamT * n)) + 44 * (θ + g + g * N)) ≤ δ * n / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hload (by positivity : (0 : ℝ) ≤ 30 * C)
      rw [hDb]
      have h2 : 30 * (C : ℝ) * (2 ^ 35 * (g + 1) * b) ≤
          2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b / 2 := by
        have hx : 0 ≤ (g + 1) * b := by positivity
        nlinarith
      linarith [mul_le_mul_of_nonneg_right hP1 hb0]
    linarith
  · -- count
    push_cast
    have hWn : 0 ≤ ω * n := le_of_lt (mul_pos h.ω_pos hn)
    set X := b * (ω * n) with hX
    have hX0 : 0 ≤ X := mul_nonneg hb0 hWn
    have hr := h.rnn
    have hl := h.lnn
    have h1 : (g : ℝ) * N * n ≤ g * (2 ^ 21 * X) := by
      have := mul_le_mul_of_nonneg_left h.Nn hg0
      rw [hX]; linarith
    have hq1224 : (q : ℝ) * (1224 * ρ * n ^ 2) ≤ 12 * (1224 * X) := by
      have : 0 ≤ ρ * n ^ 2 := by have := h.rho_pos; positivity
      nlinarith
    have h2 : 2 * q * (1224 * ρ * n ^ 2) + 11 * N * n ≤ 24 * (1224 * X) + 11 * (2 ^ 21 * X) := by
      have := h.Nn
      rw [hX]; linarith
    have h3 : (2 * q * (1224 * ρ * n ^ 2) + 11 * N * n) * (30 * C) ≤
        (24 * (1224 * X) + 11 * (2 ^ 21 * X)) * (30 * C) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hsum : 4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + 6 * (q * (1224 * ρ * n ^ 2)) + g * N * n +
        (2 * q * (1224 * ρ * n ^ 2) + 11 * N * n) * (30 * C)) ≤
        2 ^ 35 * ((30 * C + 1) * (g + 1)) * X := by
      linarith [mul_nonneg hg0 hX0, mul_nonneg hC0 hX0, mul_nonneg (mul_nonneg hC0 hg0) hX0]
    have hfin : 2 ^ 35 * ((30 * (C : ℝ) + 1) * (g + 1)) * X ≤ (δ * n) * (ω * n) := by
      rw [hDb]
      have : 2 ^ 35 * ((30 * (C : ℝ) + 1) * (g + 1)) * X ≤ P * X :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
      rw [hX] at this ⊢
      linarith
    linarith

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_base_t
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.tors_scales
