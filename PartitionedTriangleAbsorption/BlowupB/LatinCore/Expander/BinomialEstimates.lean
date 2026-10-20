/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Binomial estimates for the permutation-expander union bound

Elementary real estimates used by `PermutationExpander.lean`:

* `choose_le_three_mul_div_pow` : `C(n,r) ≤ (3n/r)^r` for `r ≥ 1`;
* `choose_pow_le` : `C(n,r)^k ≤ (3kn/s)^s` whenever `r k ≤ s`, `1 ≤ s ≤ n`, `1 ≤ k`;
* `choose_mul_pow_le` : `C(m,s) n^s ≤ C(n,s) m^s` for `m ≤ n`;
* `union_term_le` : the per-size union-bound term for four permutations and expansion
  threshold `1/20` is at most `2^{-s}`.

No probabilistic library is used; everything is a finite real inequality.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander

/-- `C(n,r) ≤ (3n/r)^r` for `r ≥ 1` (from `r^r/r! ≤ e^r ≤ 3^r`). -/
theorem choose_le_three_mul_div_pow (n r : ℕ) (hr : 1 ≤ r) :
    (n.choose r : ℝ) ≤ (3 * n / r) ^ r := by
  have h1 := Nat.choose_le_pow_div (α := ℝ) r n
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0:ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have h2 := Real.pow_div_factorial_le_exp (r : ℝ) hrpos.le r
  have h3 : Real.exp (r : ℝ) ≤ 3 ^ r := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) r
  have h4 : (r : ℝ) ^ r ≤ 3 ^ r * r.factorial := by
    rw [div_le_iff₀ hf] at h2; nlinarith
  calc (n.choose r : ℝ) ≤ n ^ r / r.factorial := h1
    _ ≤ (3 * n / r) ^ r := by
      rw [div_pow, mul_pow, div_le_div_iff₀ hf (by positivity)]
      have : (0:ℝ) ≤ n ^ r := by positivity
      nlinarith

/-- Monotonicity step: `((3n/r)^r)^k ≤ (3kn/s)^s` when `r k ≤ s ≤ n`. -/
theorem three_div_pow_mono (n r s k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (hrs : r * k ≤ s)
    (hsn : s ≤ n) : ((3 * n / r : ℝ) ^ r) ^ k ≤ (3 * k * n / s) ^ s := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hspos : (0 : ℝ) < s := by
    exact_mod_cast (le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hrs)
  have hrs' : (r:ℝ) * k ≤ s := by exact_mod_cast hrs
  have hsn' : (s:ℝ) ≤ n := by exact_mod_cast hsn
  set t : ℝ := s / k with ht
  have htr : (r:ℝ) ≤ t := by rw [ht, le_div_iff₀ hkpos]; exact hrs'
  have htpos : 0 < t := by positivity
  have htn : t ≤ n := by
    rw [ht, div_le_iff₀ hkpos]; nlinarith
  have hbase : (3 * k * n / s : ℝ) = 3 * n / t := by
    rw [ht]; field_simp
  rw [hbase, ← pow_mul]
  obtain ⟨m, hm⟩ : ∃ m, s = r * k + m := ⟨s - r * k, by omega⟩
  have key1 : (t / r) ^ (r * k) ≤ Real.exp (m : ℝ) := by
    have : t / r ≤ Real.exp ((t - r) / r) := by
      have := Real.add_one_le_exp ((t - r) / r)
      have e : (t - r) / r + 1 = t / r := by field_simp; ring
      linarith
    calc (t / r) ^ (r * k) ≤ Real.exp ((t - r) / r) ^ (r * k) :=
          pow_le_pow_left₀ (by positivity) this _
      _ = Real.exp (m : ℝ) := by
          rw [← Real.exp_nat_mul]; congr 1
          have hm' : (s:ℝ) = r * k + m := by exact_mod_cast hm
          rw [ht]; push_cast; field_simp; linarith
  have key2 : Real.exp (m : ℝ) ≤ (3 * n / t) ^ m := by
    rw [← Real.exp_one_pow]
    apply pow_le_pow_left₀ (Real.exp_pos 1).le
    have : (3:ℝ) ≤ 3 * n / t := by rw [le_div_iff₀ htpos]; linarith
    linarith [Real.exp_one_lt_d9]
  have split : (3 * n / r : ℝ) ^ (r * k) = (3 * n / t) ^ (r * k) * (t / r) ^ (r * k) := by
    rw [← mul_pow]; congr 1; field_simp
  rw [split, hm, pow_add]
  gcongr
  exact key1.trans key2

/-- `C(n,r)^k ≤ (3kn/s)^s` whenever `r k ≤ s`, `1 ≤ s ≤ n`, `1 ≤ k` (including `r = 0`). -/
theorem choose_pow_le (n r s k : ℕ) (hk : 1 ≤ k) (hrs : r * k ≤ s) (hs : 1 ≤ s)
    (hsn : s ≤ n) : (n.choose r : ℝ) ^ k ≤ (3 * k * n / s) ^ s := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_pow]
    apply one_le_pow₀
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs
    rw [le_div_iff₀ hspos]
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    have : (s:ℝ) ≤ n := by exact_mod_cast hsn
    nlinarith
  · calc (n.choose r : ℝ) ^ k ≤ ((3 * n / r : ℝ) ^ r) ^ k :=
          pow_le_pow_left₀ (by positivity) (choose_le_three_mul_div_pow n r hr) k
      _ ≤ _ := three_div_pow_mono n r s k hr hk hrs hsn

/-- `C(m,s) n^s ≤ C(n,s) m^s` for `m ≤ n`, i.e. `C(m,s)/C(n,s) ≤ (m/n)^s`. -/
theorem choose_mul_pow_le (m n : ℕ) (hmn : m ≤ n) :
    ∀ s : ℕ, m.choose s * n ^ s ≤ n.choose s * m ^ s
  | 0 => by simp
  | s + 1 => by
    have ih := choose_mul_pow_le m n hmn s
    have hm := Nat.choose_succ_right_eq m s
    have hn := Nat.choose_succ_right_eq n s
    have key : (m - s) * n ≤ m * (n - s) := by
      rcases le_total s m with h | h
      · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hmn
        simp only [Nat.add_sub_cancel_left]
        rw [show s + a + b - s = a + b by omega]; nlinarith
      · simp [Nat.sub_eq_zero_of_le h]
    have hpos : 0 < s + 1 := Nat.succ_pos s
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc m.choose (s+1) * n ^ (s+1) * (s+1) = (m.choose s * n ^ s) * ((m - s) * n) := by
          rw [show m.choose (s+1) * n ^ (s+1) * (s+1)
              = (m.choose (s+1) * (s+1)) * n ^ s * n by ring, hm]; ring
      _ ≤ (n.choose s * m ^ s) * (m * (n - s)) := Nat.mul_le_mul ih key
      _ = n.choose (s+1) * m ^ (s+1) * (s+1) := by
          rw [show n.choose (s+1) * m ^ (s+1) * (s+1)
              = (n.choose (s+1) * (s+1)) * m ^ s * m by ring, hn]; ring

/-- **The union-bound term.** For `1 ≤ s`, `2s ≤ n` and `20 r ≤ s`,
`C(n,s) · (C(n,r) C(s+r,s) / C(n,s))^4 ≤ 2^{-s}`. -/
theorem union_term_le (n s r : ℕ) (hs : 1 ≤ s) (hsn : 2 * s ≤ n) (hrs : r * 20 ≤ s) :
    (n.choose s : ℝ) * (((n.choose r : ℝ) * ((s + r).choose s : ℝ)) / n.choose s) ^ 4
      ≤ (1 / 2) ^ s := by
  have hsn' : s ≤ n := by omega
  have hsrn : s + r ≤ n := by omega
  have hCpos : (0:ℝ) < (n.choose s : ℝ) := by exact_mod_cast Nat.choose_pos hsn'
  have hBA : ((s + r).choose s : ℝ) ≤ (n.choose r : ℝ) := by
    rw [Nat.choose_symm_add]; exact_mod_cast Nat.choose_le_choose r hsrn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0:ℝ) < s := by exact_mod_cast hs
  have hBn : ((s + r).choose s : ℝ) / (n.choose s : ℝ) ≤ (((s + r : ℕ) : ℝ) / n) ^ s := by
    have h := choose_mul_pow_le (s + r) n hsrn s
    have h' : ((s + r).choose s : ℝ) * (n:ℝ) ^ s ≤ (n.choose s : ℝ) * ((s + r : ℕ) : ℝ) ^ s := by
      exact_mod_cast h
    rw [div_pow, div_le_div_iff₀ hCpos (by positivity)]; linarith
  generalize hA : (n.choose r : ℝ) = A at *
  generalize hB : ((s + r).choose s : ℝ) = B at *
  generalize hCn : (n.choose s : ℝ) = Cn at *
  generalize hx : (((s + r : ℕ) : ℝ) / n) = x at *
  have hA0 : 0 ≤ A := by rw [← hA]; positivity
  have hB0 : 0 ≤ B := by rw [← hB]; positivity
  have hx0 : 0 ≤ x := by rw [← hx]; positivity
  have hqle : A * B / Cn ≤ A * x ^ s := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hBn hA0
  have hterm : Cn * (A * B / Cn) ^ 4 ≤ A ^ 5 * (x ^ s) ^ 3 := by
    have e : Cn * (A * B / Cn) ^ 4 = (A * B) * (A * B / Cn) ^ 3 := by
      field_simp
    rw [e]
    calc A * B * (A * B / Cn) ^ 3 ≤ (A * A) * (A * x ^ s) ^ 3 := by
          gcongr
      _ = A ^ 5 * (x ^ s) ^ 3 := by ring
  have hA20 : A ^ 20 ≤ (60 * n / s) ^ s := by
    have := choose_pow_le n r s 20 (by norm_num) hrs hs hsn'
    rw [← hA]; convert this using 2; norm_num
  set α : ℝ := (s : ℝ) / n with hα
  have hαpos : 0 < α := by positivity
  have hαle : α ≤ 1 / 2 := by
    rw [hα, div_le_iff₀ hnpos]; have : (2 * s : ℝ) ≤ n := by exact_mod_cast hsn
    linarith
  have hx20 : x ^ 20 ≤ 3 * α ^ 20 := by
    have hxle : x ≤ (21 / 20) * α := by
      rw [← hx, hα]; push_cast
      have : (r:ℝ) * 20 ≤ s := by exact_mod_cast hrs
      rw [div_le_iff₀ hnpos]; field_simp; linarith
    calc x ^ 20 ≤ ((21/20) * α) ^ 20 := pow_le_pow_left₀ hx0 hxle 20
      _ = (21/20)^20 * α ^ 20 := by ring
      _ ≤ 3 * α ^ 20 := by gcongr; norm_num
  have h60 : (60 * n / s : ℝ) = 60 / α := by rw [hα]; field_simp
  have hmain : (Cn * (A * B / Cn) ^ 4) ^ 20 ≤ (((1:ℝ) / 2) ^ s) ^ 20 := by
    have h1 : (Cn * (A * B / Cn) ^ 4) ^ 20 ≤ (A ^ 5 * (x ^ s) ^ 3) ^ 20 :=
      pow_le_pow_left₀ (by rw [← hCn]; positivity) hterm 20
    have h2 : (A ^ 5 * (x ^ s) ^ 3) ^ 20 = ((A ^ 20) ^ 5) * ((x ^ 20) ^ 3) ^ s := by ring
    have h3 : ((A ^ 20) ^ 5) * ((x ^ 20) ^ 3) ^ s
        ≤ (((60 / α) ^ s) ^ 5) * ((3 * α ^ 20) ^ 3) ^ s := by
      rw [← h60]; gcongr
    have h4 : (((60 / α) ^ s) ^ 5) * ((3 * α ^ 20) ^ 3) ^ s = (60 ^ 5 * 27 * α ^ 55) ^ s := by
      rw [← pow_mul, show s * 5 = 5 * s by ring, pow_mul, ← mul_pow]
      congr 1; field_simp; ring
    have h5 : (60 ^ 5 * 27 * α ^ 55 : ℝ) ≤ ((1:ℝ)/2) ^ 20 := by
      have : α ^ 55 ≤ (1/2 : ℝ) ^ 55 := pow_le_pow_left₀ hαpos.le hαle 55
      nlinarith
    calc (Cn * (A * B / Cn) ^ 4) ^ 20 ≤ (60 ^ 5 * 27 * α ^ 55) ^ s := by linarith
      _ ≤ (((1:ℝ)/2) ^ 20) ^ s := pow_le_pow_left₀ (by positivity) h5 s
      _ = (((1:ℝ) / 2) ^ s) ^ 20 := by rw [← pow_mul, ← pow_mul, mul_comm]
  exact (pow_le_pow_iff_left₀ (by rw [← hCn]; positivity) (by positivity) (by norm_num)).mp hmain

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander
