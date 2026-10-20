/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalComponent
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.FlexL

@[expose] public section

/-!
# The numerical inputs of the balanced component certificate

From the flexible scales at `2^L` (`FlexScalesL L ω δ ρ n`, reserve scale `(ω²δ/2^L)²`) and
`2^40 (30 C + 1)(g + 1)(m + 2)(t + 1) ≤ 2^L`, the choices
`λ = ω²δ/2^L`, `Q = 2^15 λ n / ω`, `Λ0 = 4096 λ n + 2 (Q + 4096 λ n + 1)`, `9 Λ0 ≤ N ≤ 9 Λ0 + 1`,
`θ = 2^6 (g + 1) N / ω` satisfy every numerical hypothesis of `component_bal_walk` (with `γ = ω`).

Everything is measured in `b = λ n / ω²`: `δ n = 2^L b`, `ω n ≥ 2^63 δ n`, `b ≥ 2^12`
(`BalBase`); each hypothesis is then a short estimate.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open PaddedGeneral.RealInverse

/-- The base estimates, in units of `b = λ n / ω²`. -/
structure BalBase (ω δ ρ n lam Q Λ0 θ b P : ℝ) (N : ℕ) (g : ℝ) : Prop where
  ω_pos : 0 < ω
  ω_le : ω ≤ 1
  δ_pos : 0 < δ
  n_pos : 0 < n
  lam_pos : 0 < lam
  lam_ω : 64 * lam ≤ ω
  rho_pos : 0 < ρ
  rho_lam : ρ ≤ lam
  rho_n : 1 ≤ ρ * n
  scale : 2 ^ 24 * ρ ≤ lam ^ 2
  a12 : 2 ^ 12 ≤ lam * n
  ab : lam * n ≤ b
  P1 : 1 ≤ P
  D : δ * n = P * b
  W : 2 ^ 63 * (δ * n) ≤ ω * n
  Qpos : 0 < Q
  Qω : Q * ω = 2 ^ 15 * (lam * n)
  Qb : Q ≤ 2 ^ 15 * b
  Λb : Λ0 ≤ 2 ^ 17 * b
  Λpos : 2 ≤ Λ0
  N1 : (1 : ℝ) ≤ N
  Nb : (N : ℝ) ≤ 2 ^ 21 * b
  θpos : 0 < θ
  θb : θ ≤ 2 ^ 27 * (g + 1) * b
  θN : 2 * g * N * n / θ ≤ ω * n / 32
  lnn : lam * n ^ 2 ≤ b * (ω * n)
  rnn : ρ * n ^ 2 ≤ b * (ω * n)
  Nn : (N : ℝ) * n ≤ 2 ^ 21 * b * (ω * n)

set_option maxHeartbeats 4000000 in
theorem bal_base (L : ℕ) (ω δ ρ n : ℝ) (hfl : FlexScalesL L ω δ ρ n) (g : ℕ)
    (lam Q Λ0 θ : ℝ) (N : ℕ)
    (hlamdef : lam = ω ^ 2 * δ / 2 ^ L) (hQdef : Q = 2 ^ 15 * lam * n / ω)
    (hΛdef : Λ0 = 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)))
    (hN1 : 9 * Λ0 ≤ N) (hN2 : (N : ℝ) ≤ 9 * Λ0 + 1) (hθdef : θ = 2 ^ 6 * (g + 1) * N / ω) :
    BalBase ω δ ρ n lam Q Λ0 θ (lam * n / ω ^ 2) (2 ^ L) N g := by
  obtain ⟨hω, hω1, hδ, hδω, hρsq, hn0, hρn⟩ := hfl
  rw [← hlamdef] at hρsq
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have h2L1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  have hω2pos : 0 < ω ^ 2 := by positivity
  have hω2 : ω ^ 2 ≤ 1 := pow_le_one₀ hω.le hω1
  have hδ1 : δ ≤ 1 / 2 ^ 63 := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlam2L : lam * 2 ^ L = ω ^ 2 * δ := by rw [hlamdef]; field_simp
  have hlamδ : lam ≤ δ := by
    have h1 : ω ^ 2 * δ ≤ δ := by nlinarith
    have h2 : lam * 1 ≤ lam * 2 ^ L := mul_le_mul_of_nonneg_left h2L1 hlam.le
    linarith
  have hlamω : 64 * lam ≤ ω := by
    have : 64 * δ ≤ ω := by nlinarith
    linarith
  have hlam1 : lam ≤ 1 := by linarith
  have hρ : 0 < ρ := by
    by_contra h; push Not at h
    have : ρ * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hn0
    linarith
  have hn : 0 < n := by
    by_contra h; push Not at h
    have : ρ * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le h
    linarith
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith
  have hρlam : ρ ≤ lam := by nlinarith
  have hlamn2 : 2 ^ 24 ≤ lam ^ 2 * n := by
    have : 2 ^ 24 * ρ * n ≤ lam ^ 2 * n := mul_le_mul_of_nonneg_right hρsq hn.le
    nlinarith
  have hn1 : 1 ≤ n := by
    have : lam ^ 2 * n ≤ n := by nlinarith
    linarith
  have ha : 2 ^ 12 ≤ lam * n := by
    have hsq : (2 ^ 12 : ℝ) ^ 2 ≤ (lam * n) ^ 2 := by
      have : (lam * n) ^ 2 = lam ^ 2 * n * n := by ring
      rw [this]; nlinarith
    have hpos : 0 ≤ lam * n := by positivity
    nlinarith
  set b : ℝ := lam * n / ω ^ 2 with hbdef
  have hb_eq : b * ω ^ 2 = lam * n := by rw [hbdef]; field_simp
  have hab : lam * n ≤ b := by
    rw [hbdef, le_div_iff₀ hω2pos]
    have := mul_le_mul_of_nonneg_left hω2 (by positivity : (0 : ℝ) ≤ lam * n)
    linarith
  have hD : δ * n = 2 ^ L * b := by
    have h1 : 2 ^ L * b * ω ^ 2 = δ * n * ω ^ 2 := by
      calc 2 ^ L * b * ω ^ 2 = 2 ^ L * (b * ω ^ 2) := by ring
        _ = 2 ^ L * (lam * n) := by rw [hb_eq]
        _ = lam * 2 ^ L * n := by ring
        _ = ω ^ 2 * δ * n := by rw [hlam2L]
        _ = δ * n * ω ^ 2 := by ring
    exact (mul_right_cancel₀ hω2pos.ne' h1).symm
  have hW : 2 ^ 63 * (δ * n) ≤ ω * n := by nlinarith
  have hω2ω : ω ^ 2 ≤ ω := pow_le_of_le_one hω.le hω1 (by norm_num)
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hbω : lam * n / ω ≤ b := by
    rw [hbdef, div_le_div_iff₀ hω hω2pos]
    have := mul_le_mul_of_nonneg_left hω2ω (by positivity : (0 : ℝ) ≤ lam * n)
    linarith
  have hinvω : 1 / ω ≤ b / 2 ^ 12 := by
    rw [div_le_div_iff₀ hω (by norm_num), one_mul]
    have h1 : b * ω ^ 2 ≤ b * ω := mul_le_mul_of_nonneg_left hω2ω hb0
    linarith
  have hQ : 0 < Q := by rw [hQdef]; positivity
  have hQω : Q * ω = 2 ^ 15 * (lam * n) := by rw [hQdef]; field_simp
  have hQb : Q ≤ 2 ^ 15 * b := by
    have e : Q = 2 ^ 15 * (lam * n / ω) := by rw [hQdef]; ring
    rw [e]; nlinarith
  have hQωb : Q / ω ≤ 2 ^ 15 * b := by
    have e : Q / ω = 2 ^ 15 * b := by rw [hQdef, hbdef]; field_simp
    rw [e]
  have hΛ2 : 2 ≤ Λ0 := by rw [hΛdef]; nlinarith
  have hΛb : Λ0 ≤ 2 ^ 17 * b := by rw [hΛdef]; nlinarith
  have hΛωb : Λ0 / ω ≤ 2 ^ 17 * b := by
    have e : Λ0 / ω = 12288 * (lam * n / ω) + 2 * (Q / ω) + 2 * (1 / ω) := by
      rw [hΛdef]; field_simp; ring
    rw [e]
    nlinarith
  have hN0 : (1 : ℝ) ≤ N := by linarith
  have hNωb : (N : ℝ) / ω ≤ 2 ^ 21 * b := by
    have e1 : (N : ℝ) / ω ≤ (9 * Λ0 + 1) / ω := div_le_div_of_nonneg_right hN2 hω.le
    have e2 : (9 * Λ0 + 1) / ω = 9 * (Λ0 / ω) + 1 / ω := by field_simp
    nlinarith
  have hNb : (N : ℝ) ≤ 2 ^ 21 * b := by
    have e : (N : ℝ) = (N : ℝ) / ω * ω := by field_simp
    have h0 : (0 : ℝ) ≤ (N : ℝ) / ω := by positivity
    have : (N : ℝ) / ω * ω ≤ (N : ℝ) / ω := by nlinarith
    linarith
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hθb : θ ≤ 2 ^ 27 * (g + 1) * b := by
    have e : θ = 2 ^ 6 * (g + 1) * ((N : ℝ) / ω) := by rw [hθdef]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hNωb (by positivity : (0 : ℝ) ≤ 2 ^ 6 * (g + 1))
    nlinarith
  have hθN : 2 * g * N * n / θ ≤ ω * n / 32 := by
    have e : 2 * (g : ℝ) * N * n / θ = 2 * g * (ω * n) / (2 ^ 6 * (g + 1)) := by
      rw [hθdef]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hWn : (0 : ℝ) ≤ ω * n := by positivity
    nlinarith [mul_nonneg hg0 hWn]
  have hlnn : lam * n ^ 2 ≤ b * (ω * n) := by
    have e : lam * n ^ 2 = b * ω ^ 2 * n := by rw [hb_eq]; ring
    rw [e]
    have hb0 : 0 ≤ b := by positivity
    have : ω ^ 2 ≤ ω := by nlinarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ b * n)
    nlinarith
  have hrnn : ρ * n ^ 2 ≤ b * (ω * n) := by
    have : ρ * n ^ 2 ≤ lam * n ^ 2 := mul_le_mul_of_nonneg_right hρlam (sq_nonneg n)
    linarith
  have hNn : (N : ℝ) * n ≤ 2 ^ 21 * b * (ω * n) := by
    have e : (N : ℝ) * n = (N : ℝ) / ω * (ω * n) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hNωb (by positivity)
  exact ⟨hω, hω1, hδ, hn, hlam, hlamω, hρ, hρlam, hρn, hρsq, ha, hab, h2L1, hD, hW, hQ, hQω, hQb,
    hΛb, hΛ2, hN0, hNb, hθ, hθb, hθN, hlnn, hrnn, hNn⟩

/-- The numerical hypotheses of `component_bal_walk`, for `n` vertices and `γ = ω`. -/
structure BalNumeric (ω δ ρ n lam Q θ : ℝ) (N g m C t : ℕ) : Prop where
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
  bud : ((m + 1 : ℕ) : ℝ) + (2 * g * N * n / θ + ((m + 1 : ℕ) : ℝ) * N) +
    ((m + 1 : ℕ) : ℝ) * ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + θ + g +
      2 * g * N) < ω * n
  embed : (2 * (168 + g * 168 : ℕ) + 5 * t : ℝ) + 9 * C + 8 * (δ * n) < ω * n / 2
  deg : max ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N))
      (δ * n + (30 * C : ℕ)) +
    ((30 * C : ℕ) : ℝ) * ((4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
      44 * (θ + g + g * N)) ≤ 2 * δ * n
  count : 4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + g * N * n +
    (1224 * ρ * n ^ 2 + 11 * N * n) * ((30 * C : ℕ) : ℝ)) ≤ (δ * n) * (ω * n)

section Estimates

variable {ω δ ρ n lam Q Λ0 θ b P : ℝ} {N : ℕ} {g : ℝ}

theorem est_path (h : BalBase ω δ ρ n lam Q Λ0 θ b P N g) :
    3 * (4100 * lam * n ^ 2) / Q + 3 +
      2 * (2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 2) < ω * n := by
  have e : 3 * (4100 * lam * n ^ 2) / Q = 12300 / 32768 * (ω * n) := by
    rw [div_eq_iff h.Qpos.ne']
    have h1 : 3 * (4100 * lam * n ^ 2) = 12300 / 32768 * n * (2 ^ 15 * (lam * n)) := by ring
    rw [h1, ← h.Qω]; ring
  rw [e]
  have hWpos : 0 < ω * n := mul_pos h.ω_pos h.n_pos
  have hb0 : 0 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hρnb : ρ * n ≤ b := (mul_le_mul_of_nonneg_right h.rho_lam h.n_pos.le).trans h.ab
  have hsmall : 3 + 2 * (2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 2) ≤
      2 ^ 19 * b := by
    have := h.Qb; have := h.ab; have := h.a12; nlinarith
  have hWb : 2 ^ 63 * b ≤ ω * n := by
    have := h.W; rw [h.D] at this
    have : 2 ^ 63 * b ≤ 2 ^ 63 * (P * b) := by nlinarith [h.P1]
    linarith
  nlinarith

theorem est_bud (h : BalBase ω δ ρ n lam Q Λ0 θ b P N g) (hg0 : 0 ≤ g) (m : ℕ)
    (hP : 2 ^ 40 * ((g + 1) * (m + 2)) ≤ P) :
    ((m + 1 : ℕ) : ℝ) + (2 * g * N * n / θ + ((m + 1 : ℕ) : ℝ) * N) +
      ((m + 1 : ℕ) : ℝ) * ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + θ + g +
        2 * g * N) < ω * n := by
  push_cast
  have hb0 : 0 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hb1 : 1 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hρnb : ρ * n ≤ b := (mul_le_mul_of_nonneg_right h.rho_lam h.n_pos.le).trans h.ab
  have hgN : g * N ≤ g * (2 ^ 21 * b) := mul_le_mul_of_nonneg_left h.Nb hg0
  have hin : 1 + (N : ℝ) + ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + θ + g +
      2 * g * N) ≤ 2 ^ 30 * (g + 1) * b := by
    have := h.Qb; have := h.ab; have := h.θb; have := h.Nb
    nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hrest : ((m : ℝ) + 1) + ((m : ℝ) + 1) * N + ((m : ℝ) + 1) *
      ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + θ + g + 2 * g * N) ≤
      ((m : ℝ) + 1) * (2 ^ 30 * (g + 1) * b) := by
    have := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)
    nlinarith
  have hWb : 2 ^ 63 * (P * b) ≤ ω * n := by have := h.W; rw [h.D] at this; exact this
  have hbig : ((m : ℝ) + 1) * (2 ^ 30 * (g + 1) * b) ≤ ω * n / 2 := by
    have h1 : ((m : ℝ) + 1) * (2 ^ 30 * (g + 1) * b) ≤ 2 ^ 30 * ((g + 1) * (m + 2)) * b := by
      have hx : (0 : ℝ) ≤ (g + 1) * b := by positivity
      nlinarith
    have h2 : 2 ^ 30 * ((g + 1) * (m + 2)) * b ≤ P * b / 2 ^ 10 := by
      rw [le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_right hP hb0
      nlinarith
    have h3 : P * b / 2 ^ 10 ≤ ω * n / 2 := by
      have hPb : 0 ≤ P * b := by nlinarith [h.P1]
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith
    linarith
  have := h.θN
  have hWpos : 0 < ω * n := mul_pos h.ω_pos h.n_pos
  linarith

theorem est_embed (h : BalBase ω δ ρ n lam Q Λ0 θ b P N g) (C t : ℕ) (g' : ℕ)
    (hP : 2 ^ 40 * (((g' : ℝ) + 1) * (t + 1) + C) ≤ P) :
    (2 * (168 + g' * 168 : ℕ) + 5 * t : ℝ) + 9 * C + 8 * (δ * n) < ω * n / 2 := by
  push_cast
  have hb1 : 1 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hg0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hDP : P ≤ δ * n := by rw [h.D]; nlinarith [h.P1]
  have hW := h.W
  have hcons : 2 * (168 + (g' : ℝ) * 168) + 5 * t + 9 * C ≤ 2 ^ 10 * (((g' : ℝ) + 1) * (t + 1) + C) := by
    nlinarith [mul_nonneg hg0 ht0]
  have hD0 : 0 ≤ δ * n := by rw [h.D]; nlinarith [h.P1]
  nlinarith

theorem est_deg (h : BalBase ω δ ρ n lam Q Λ0 θ b P N g) (hg0 : 0 ≤ g) (C : ℕ)
    (hP : 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) ≤ P) :
    max ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N))
        (δ * n + (30 * C : ℕ)) +
      ((30 * C : ℕ) : ℝ) * ((4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
        44 * (θ + g + g * N)) ≤ 2 * δ * n := by
  push_cast
  have hb0 : 0 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hb1 : 1 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hρnb : ρ * n ≤ b := (mul_le_mul_of_nonneg_right h.rho_lam h.n_pos.le).trans h.ab
  have hgN : g * N ≤ g * (2 ^ 21 * b) := mul_le_mul_of_nonneg_left h.Nb hg0
  have hfirst0 : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N) ≤
      2 ^ 28 * (g + 1) * b := by
    have := h.Qb; have := h.ab; have := h.θb
    nlinarith
  have hPb : 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b ≤ P * b := mul_le_mul_of_nonneg_right hP hb0
  have hfirst : (2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) + (θ + g + g * N) ≤
      δ * n := by
    rw [h.D]
    have : 2 ^ 28 * (g + 1) * b ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b := by
      have hx : 0 ≤ (g + 1) * b := by positivity
      nlinarith
    linarith
  have hC30 : 30 * (C : ℝ) ≤ δ * n / 2 := by
    rw [h.D]
    have : 30 * (C : ℝ) * 2 ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b := by
      have hx : 1 ≤ (g + 1) * b := by nlinarith
      nlinarith
    linarith
  have hmax : max ((2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1)))) +
      (θ + g + g * N)) (δ * n + 30 * C) ≤ δ * n + 30 * C := max_le (by linarith) le_rfl
  have hload : (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + 44 * (θ + g + g * N) ≤
      2 ^ 34 * (g + 1) * b := by
    have := h.Qb; have := h.ab; have := h.θb
    nlinarith
  have hprod : 30 * (C : ℝ) * ((4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) +
      44 * (θ + g + g * N)) ≤ δ * n / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hload (by positivity : (0 : ℝ) ≤ 30 * C)
    rw [h.D]
    have h2 : 30 * (C : ℝ) * (2 ^ 34 * (g + 1) * b) ≤ 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) * b / 2 := by
      have hx : 0 ≤ (g + 1) * b := by positivity
      nlinarith
    linarith
  linarith

theorem est_count (h : BalBase ω δ ρ n lam Q Λ0 θ b P N g) (hg0 : 0 ≤ g) (C : ℕ)
    (hP : 2 ^ 40 * ((30 * (C : ℝ) + 1) * (g + 1)) ≤ P) :
    4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + g * N * n +
      (1224 * ρ * n ^ 2 + 11 * N * n) * ((30 * C : ℕ) : ℝ)) ≤ (δ * n) * (ω * n) := by
  push_cast
  have hb0 : 0 ≤ b := le_trans (by norm_num) (h.a12.trans h.ab)
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hWn : 0 ≤ ω * n := le_of_lt (mul_pos h.ω_pos h.n_pos)
  set X := b * (ω * n) with hX
  have hX0 : 0 ≤ X := mul_nonneg hb0 hWn
  have h1 : (g : ℝ) * N * n ≤ g * (2 ^ 21 * X) := by
    have := mul_le_mul_of_nonneg_left h.Nn hg0
    rw [hX]; nlinarith
  have h2 : 1224 * ρ * n ^ 2 + 11 * N * n ≤ 1224 * X + 11 * (2 ^ 21 * X) := by
    have := h.rnn; have := h.Nn
    rw [hX]; nlinarith
  have h3 : (1224 * ρ * n ^ 2 + 11 * N * n) * (30 * C) ≤
      (1224 * X + 11 * (2 ^ 21 * X)) * (30 * C) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have hsum : 4 * (2 * ρ * n ^ 2 + 16 * lam * n ^ 2 + g * N * n +
      (1224 * ρ * n ^ 2 + 11 * N * n) * (30 * C)) ≤ 2 ^ 32 * ((30 * C + 1) * (g + 1)) * X := by
    have := h.rnn; have := h.lnn
    nlinarith [mul_nonneg hg0 hX0, mul_nonneg hC0 hX0, mul_nonneg (mul_nonneg hC0 hg0) hX0]
  have hfin : 2 ^ 32 * ((30 * (C : ℝ) + 1) * (g + 1)) * X ≤ (δ * n) * (ω * n) := by
    rw [h.D]
    have : 2 ^ 32 * ((30 * (C : ℝ) + 1) * (g + 1)) * X ≤ P * X :=
      mul_le_mul_of_nonneg_right (by nlinarith) hX0
    rw [hX] at this ⊢
    nlinarith
  linarith

end Estimates

/-- **The balanced scales.** -/
theorem bal_scales (L : ℕ) (ω δ ρ n : ℝ) (hfl : FlexScalesL L ω δ ρ n) (g m C t : ℕ)
    (hL : (2 : ℝ) ^ 40 * ((30 * C + 1) * (g + 1) * (m + 2) * (t + 1)) ≤ 2 ^ L)
    (lam Q Λ0 θ : ℝ) (N : ℕ)
    (hlamdef : lam = ω ^ 2 * δ / 2 ^ L) (hQdef : Q = 2 ^ 15 * lam * n / ω)
    (hΛdef : Λ0 = 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)))
    (hN1 : 9 * Λ0 ≤ N) (hN2 : (N : ℝ) ≤ 9 * Λ0 + 1) (hθdef : θ = 2 ^ 6 * (g + 1) * N / ω) :
    BalNumeric ω δ ρ n lam Q θ N g m C t := by
  have hB := bal_base L ω δ ρ n hfl g lam Q Λ0 θ N hlamdef hQdef hΛdef hN1 hN2 hθdef
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ (30 * C + 1) * (g + 1) := by positivity
  have hP1 : (2 : ℝ) ^ 40 * ((30 * C + 1) * (g + 1)) ≤ 2 ^ L := by
    have : ((30 * (C : ℝ) + 1) * (g + 1)) ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have h1 : (30 * (C : ℝ) + 1) * (g + 1) ≤ (30 * C + 1) * (g + 1) * (m + 2) := by nlinarith
      have h2 : (0 : ℝ) ≤ (30 * C + 1) * (g + 1) * (m + 2) := by positivity
      nlinarith
    nlinarith
  have hP2 : (2 : ℝ) ^ 40 * ((g + 1) * (m + 2)) ≤ 2 ^ L := by
    have : ((g : ℝ) + 1) * (m + 2) ≤ (30 * C + 1) * (g + 1) * (m + 2) * (t + 1) := by
      have h0 : (0 : ℝ) ≤ (g + 1) * (m + 2) := by positivity
      have h1 : (1 : ℝ) ≤ (30 * C + 1) * (t + 1) := by nlinarith
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
  refine ⟨hB.lam_pos, by linarith [hB.lam_ω, hB.ω_le], hB.rho_pos, hB.scale, hB.rho_n,
    by linarith [hB.a12], hB.δ_pos, hB.Qpos, hB.θpos, hB.lam_ω, est_path hB,
    est_bud hB hg0 m hP2, est_embed hB C t g hP3, est_deg hB hg0 C hP1, est_count hB hg0 C hP1⟩

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_scales
