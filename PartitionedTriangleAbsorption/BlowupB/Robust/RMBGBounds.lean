/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Robustly matchable bipartite graphs: the real estimates

* `choose_mul_ratio_pow_le`: `C(n,k) (k/n)^k ≤ k^k/k! ≤ e^k ≤ 3^k`;
* `term1_le`, `term3_le`: the two union-bound terms are at most `(1/100)^a` once `d ≥ 7`;
* `geom_sum_le_two_mul`: `∑_{a<K} r^(a+1) ≤ 2 r` for `0 ≤ r ≤ 1/2`;
* `ratio_pow_le`: `32 (19/20)^200 ≤ 1/2`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Robust

theorem choose_mul_ratio_pow_le (n k : ℕ) (hn : 0 < n) :
    (n.choose k : ℝ) * ((k : ℝ) / n) ^ k ≤ 3 ^ k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
  have h2 : (n : ℝ) ^ k / k.factorial * ((k : ℝ) / n) ^ k = (k : ℝ) ^ k / k.factorial := by
    rw [div_pow]; field_simp
  have h3 : (k : ℝ) ^ k / k.factorial ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
  have h4 : Real.exp k = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
  have h5 : Real.exp 1 ^ k ≤ 3 ^ k := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  calc (n.choose k : ℝ) * ((k : ℝ) / n) ^ k ≤ (n : ℝ) ^ k / k.factorial * ((k : ℝ) / n) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (k : ℝ) ^ k / k.factorial := h2
    _ ≤ Real.exp k := h3
    _ = Real.exp 1 ^ k := h4
    _ ≤ 3 ^ k := h5

/-- The binomial bound with a larger ratio `q ≤ k'/n` replaced by `(k'/n)`, `k' = 2k`. -/
theorem choose_mul_pow_le_six (n k : ℕ) (hn : 0 < n) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ 2 * (k : ℝ) / n) : (n.choose k : ℝ) * q ^ k ≤ 6 ^ k := by
  have h := choose_mul_ratio_pow_le n k hn
  have hpow : q ^ k ≤ (2 * (k : ℝ) / n) ^ k := pow_le_pow_left₀ hq0 hq k
  have hsplit : (2 * (k : ℝ) / n) ^ k = 2 ^ k * ((k : ℝ) / n) ^ k := by
    rw [← mul_pow]; congr 1; ring
  calc (n.choose k : ℝ) * q ^ k ≤ (n.choose k : ℝ) * (2 * (k : ℝ) / n) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 2 ^ k * ((n.choose k : ℝ) * ((k : ℝ) / n) ^ k) := by rw [hsplit]; ring
    _ ≤ 2 ^ k * 3 ^ k := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 6 ^ k := by rw [← mul_pow]; norm_num

/-- A generic three-factor term `C(n,a) C(N,b) q^(a d)` with `C(N,b) q^b ≤ 3^b`. -/
theorem term_le (n N a b d : ℕ) (hn : 0 < n) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 10)
    (hqa : q ≤ 2 * (a : ℝ) / n) (hb : (N.choose b : ℝ) * q ^ b ≤ 3 ^ b)
    (hba : b ≤ 2 * a) (hexp : a + b + 4 * a ≤ a * d) :
    (n.choose a : ℝ) * (N.choose b : ℝ) * q ^ (a * d) ≤ (1 / 100) ^ a := by
  set e := a * d - a - b with he
  have hsplit : a * d = a + b + e := by omega
  have he4 : 4 * a ≤ e := by omega
  have hA := choose_mul_pow_le_six n a hn q hq0 hqa
  have hqe : q ^ e ≤ (1 / 10 : ℝ) ^ (4 * a) :=
    (pow_le_pow_left₀ hq0 hq1 e).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) he4)
  have h3b : (3 : ℝ) ^ b ≤ 9 ^ a := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]; exact pow_le_pow_right₀ (by norm_num) hba
  calc (n.choose a : ℝ) * (N.choose b : ℝ) * q ^ (a * d)
      = ((n.choose a : ℝ) * q ^ a) * ((N.choose b : ℝ) * q ^ b) * q ^ e := by
        rw [hsplit, pow_add, pow_add]; ring
    _ ≤ 6 ^ a * 9 ^ a * (1 / 10 : ℝ) ^ (4 * a) := by
        apply mul_le_mul _ hqe (by positivity) (by positivity)
        exact mul_le_mul hA (hb.trans h3b) (by positivity) (by positivity)
    _ = (54 / 10000 : ℝ) ^ a := by rw [pow_mul, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (1 / 100) ^ a := pow_le_pow_left₀ (by norm_num) (by norm_num) a

/-- Term of the first bad family: `C(n,a) C(n,2a-1) ((2a-1)/n)^(a d) ≤ (1/100)^a`. -/
theorem term1_le (m a d : ℕ) (ha : 1 ≤ a) (ha10 : 10 * a ≤ m) (hd : 7 ≤ d) :
    ((m + m).choose a : ℝ) * ((m + m).choose (2 * a - 1) : ℝ) *
      (((2 * a - 1 : ℕ) : ℝ) / (m + m : ℕ)) ^ (a * d) ≤ (1 / 100) ^ a := by
  have hn : 0 < m + m := by omega
  have hnR : (0 : ℝ) < ((m + m : ℕ) : ℝ) := by exact_mod_cast hn
  have hcast : ((2 * a - 1 : ℕ) : ℝ) ≤ 2 * a := by
    have : 2 * a - 1 ≤ 2 * a := Nat.sub_le _ _
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ ((2 * a - 1 : ℕ) : ℝ) / (m + m : ℕ) := by positivity
  have hqa : ((2 * a - 1 : ℕ) : ℝ) / (m + m : ℕ) ≤ 2 * (a : ℝ) / (m + m : ℕ) :=
    div_le_div_of_nonneg_right hcast hnR.le
  have hq1 : ((2 * a - 1 : ℕ) : ℝ) / (m + m : ℕ) ≤ 1 / 10 := by
    rw [div_le_iff₀ hnR]
    have : (10 : ℝ) * (2 * a) ≤ ((m + m : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 10 * (2 * a) ≤ m + m)
    linarith
  refine term_le (m + m) (m + m) a (2 * a - 1) d hn _ hq0 hq1 hqa ?_ (by omega) ?_
  · exact choose_mul_ratio_pow_le (m + m) (2 * a - 1) hn
  · have : a * 7 ≤ a * d := Nat.mul_le_mul_left a hd
    omega

/-- Term of the third bad family: `C(n,c) C(m,c-1) ((2c-2)/n)^(c d) ≤ (1/100)^c`. -/
theorem term3_le (m c d : ℕ) (hc : 1 ≤ c) (hc10 : 10 * c ≤ m) (hd : 7 ≤ d) :
    ((m + m).choose c : ℝ) * (m.choose (c - 1) : ℝ) *
      (((2 * (c - 1) : ℕ) : ℝ) / (m + m : ℕ)) ^ (c * d) ≤ (1 / 100) ^ c := by
  have hn : 0 < m + m := by omega
  have hm : 0 < m := by omega
  have hnR : (0 : ℝ) < ((m + m : ℕ) : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hqeq : ((2 * (c - 1) : ℕ) : ℝ) / (m + m : ℕ) = ((c - 1 : ℕ) : ℝ) / m := by
    push_cast; field_simp; ring
  have hcast : ((2 * (c - 1) : ℕ) : ℝ) ≤ 2 * c := by
    have : 2 * (c - 1) ≤ 2 * c := by omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ ((2 * (c - 1) : ℕ) : ℝ) / (m + m : ℕ) := by positivity
  have hqa : ((2 * (c - 1) : ℕ) : ℝ) / (m + m : ℕ) ≤ 2 * (c : ℝ) / (m + m : ℕ) :=
    div_le_div_of_nonneg_right hcast hnR.le
  have hq1 : ((2 * (c - 1) : ℕ) : ℝ) / (m + m : ℕ) ≤ 1 / 10 := by
    rw [div_le_iff₀ hnR]
    have : (10 : ℝ) * (2 * c) ≤ ((m + m : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 10 * (2 * c) ≤ m + m)
    linarith
  refine term_le (m + m) m c (c - 1) d hn _ hq0 hq1 hqa ?_ (by omega) ?_
  · rw [hqeq]; exact choose_mul_ratio_pow_le m (c - 1) hm
  · have : c * 7 ≤ c * d := Nat.mul_le_mul_left c hd
    omega

/-- `∑_{a<K} r^(a+1) ≤ 2 r` for `0 ≤ r ≤ 1/2`. -/
theorem geom_sum_le_two_mul (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (K : ℕ) :
    ∑ a ∈ Finset.range K, r ^ (a + 1) ≤ 2 * r := by
  have key : ∀ K : ℕ, ∑ a ∈ Finset.range K, r ^ (a + 1) + 2 * r ^ (K + 1) ≤ 2 * r := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have h : 2 * r ^ (K + 1 + 1) ≤ r ^ (K + 1) := by
        rw [pow_succ]
        have : 0 ≤ r ^ (K + 1) := by positivity
        nlinarith
      linarith
  have hpos : 0 ≤ 2 * r ^ (K + 1) := by positivity
  linarith [key K]

theorem ratio_pow_le : (32 : ℝ) * (19 / 20) ^ 200 ≤ 1 / 2 := by norm_num

end PartitionedTriangleAbsorption.BlowupB.Robust

#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.term1_le
#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.term3_le
