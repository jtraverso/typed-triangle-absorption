/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Numerical closure for the endpoint-precharged weighted embedding.
These bounds do not assert an embedding; its actual mass, endpoint and
individual-weight hypotheses must still be supplied by the construction. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEmbeddingBudget

def factor (C K : ℕ) : ℕ := 4096 * (C + 1) * (K + 1)

theorem factor_bounds (C K : ℕ) :
    2514 ≤ (factor C K : ℝ) ∧
    392 * (K : ℝ) * C + 384 ≤ factor C K ∧
    1257 + 14 * (C : ℝ) ≤ factor C K ∧
    49 * (C : ℝ) + 16 ≤ factor C K := by
  unfold factor
  push_cast
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hCK := mul_nonneg hC hK
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exclusion (q t n ω mass d W : ℝ) (hq : 1 ≤ q)
    (ht : 0 < t) (ht1 : t ≤ 1) (hn : 0 < n) (hsize : 1 ≤ t ^ 2 * n)
    (hmass : mass ≤ q * t ^ 2 * n ^ 2) (hd : d ≤ 2 * t ^ 2 * n)
    (hW : W ≤ q * t * n) (hsmall : 32 * q * t ≤ ω) :
    4 * mass / (q * t * n) + 4 + 2 * (d + q * t * n + 2 * W) < ω * n := by
  have hq0 : 0 < q := by linarith
  have hden : 0 < q * t * n := by positivity
  have hdiv : 4 * mass / (q * t * n) ≤ 4 * t * n := by
    apply (div_le_iff₀ hden).mpr
    calc 4 * mass ≤ 4 * (q * t ^ 2 * n ^ 2) := by linarith
      _ = 4 * t * n * (q * t * n) := by ring
  have hsq : t ^ 2 * n ≤ t * n := by
    have ht2 : t ^ 2 ≤ t := by nlinarith
    exact mul_le_mul_of_nonneg_right ht2 hn.le
  have htn : 1 ≤ t * n := hsize.trans hsq
  have hqtn : t * n ≤ q * t * n := by nlinarith
  have hωn := mul_le_mul_of_nonneg_right hsmall hn.le
  nlinarith

theorem scale (q t lam ω : ℝ) (hq : 0 ≤ q) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hscale : 4096 * t ≤ lam) (hsmall : q * lam ≤ ω ^ 3) :
    32 * q * t ≤ ω := by
  have hh := mul_le_mul_of_nonneg_left hscale hq
  have hω2 : ω * ω ≤ ω := mul_le_of_le_one_right hω hω1
  have hω3 : ω ^ 3 ≤ ω := by
    calc ω ^ 3 = ω * (ω * ω) := by ring
      _ ≤ ω * ω := mul_le_mul_of_nonneg_left hω2 hω
      _ ≤ ω := hω2
  nlinarith

theorem pinned_load (q t n load : ℝ) (hq : 2514 ≤ q)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hn : 0 ≤ n)
    (hload : load ≤ 2514 * t ^ 2 * n) : load ≤ q * t * n := by
  have hsq : t ^ 2 ≤ t := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq hn
  have hq' := mul_le_mul_of_nonneg_right hq (mul_nonneg ht hn)
  nlinarith

theorem load_target (q t n lam ω load : ℝ) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hlam : 0 ≤ lam) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hscale : 4096 * t ≤ lam) (hload : load ≤ 3 * q * t * n) :
    load ≤ 4 * q * lam * n / ω := by
  have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hq hn)
  have hnonneg : 0 ≤ q * lam * n := by positivity
  have hb : load ≤ 4 * q * lam * n := by nlinarith
  exact hb.trans ((le_div_iff₀ hω).mpr
    (mul_le_of_le_one_right (by positivity) hω1))

theorem count_target (q rho lam n ω count : ℝ) (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hcount : count ≤ q * rho * n ^ 2) :
    count ≤ 4 * q * lam * n ^ 2 / ω := by
  have hsq : lam ^ 2 ≤ lam := by nlinarith
  have hrho : rho ≤ 4 * lam := by norm_num at hscale; nlinarith
  have hh := mul_le_mul_of_nonneg_right hrho (mul_nonneg hq (sq_nonneg n))
  have hb : count ≤ 4 * q * lam * n ^ 2 := by nlinarith
  exact hb.trans ((le_div_iff₀ hω).mpr
    (mul_le_of_le_one_right (by positivity) hω1))

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEmbeddingBudget
