/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.Counting

@[expose] public section

/-!
# Latin profile normalization (§5)

For a balanced `L ⊆ Qc n` we construct a triangle chain

  `Y = ∑ z_ab · tri(a, b, a+b) + ∑ wB_(e,a) · mB(e,a) + ∑ wC_(e,a) · mC(e,a)`

whose vertex out-profile is exactly the out-degree profile of `L` in all three classes:

* `z_ab = [(b - a) mod n < d_A(a)] ∈ {0,1}` fixes the `A`-profile exactly (Latin rows);
* the defects of the `B`- and `C`-profiles are zero-sum and bounded by `n`; integer flows on the
  fixed expander (`integer_flow`) carry them, and each edge flow is split among the `n` Latin
  triangles through its tail (`split`), giving coefficients `|w| ≤ 21`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Positivization Cycles

variable {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart)

/-- The triangle chain with Latin coefficients `z` and move coefficients `wB`, `wC`. -/
def triChain (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) : Vc n × Vc n → ℤ :=
  ∑ p : Fin n × Fin n, z p.1 p.2 • tri p.1 p.2 (p.1 + p.2) +
    ∑ q : G.edgeSet × Fin n, wB q.1 q.2 • mB G o q.1 q.2 +
    ∑ q : G.edgeSet × Fin n, wC q.1 q.2 • mC G o q.1 q.2

omit [NeZero n] in
theorem outF_tri (a b c : Fin n) (w : Vc n) :
    outF (tri a b c) w = (if vA a = w then 1 else 0) + (if vB b = w then 1 else 0) +
      (if vC c = w then 1 else 0) := by
  simp only [tri, outF_add, outF_ind]

theorem outF_mB (e : G.edgeSet) (a : Fin n) (w : Vc n) :
    outF (mB G o e a) w = (if vB (o e).snd = w then 1 else 0) -
      (if vB (o e).fst = w then 1 else 0) := by
  simp only [mB, outF_add, outF_sub, outF_ind]
  ring

theorem outF_mC (e : G.edgeSet) (a : Fin n) (w : Vc n) :
    outF (mC G o e a) w = (if vC (o e).snd = w then 1 else 0) -
      (if vC (o e).fst = w then 1 else 0) := by
  simp only [mC, outF_add, outF_sub, outF_ind]
  ring

theorem outF_triChain (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) (w : Vc n) :
    outF (triChain G o z wB wC) w =
      ∑ p : Fin n × Fin n, z p.1 p.2 * outF (tri p.1 p.2 (p.1 + p.2)) w +
      ∑ q : G.edgeSet × Fin n, wB q.1 q.2 * outF (mB G o q.1 q.2) w +
      ∑ q : G.edgeSet × Fin n, wC q.1 q.2 * outF (mC G o q.1 q.2) w := by
  simp only [triChain, outF_add, outF_sum]

theorem triChain_outF_A (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) (x : Fin n) :
    outF (triChain G o z wB wC) (vA x) = ∑ b, z x b := by
  rw [outF_triChain]
  simp only [outF_tri, outF_mB, outF_mC, vA_inj, vB_ne_vA, vC_ne_vA, if_false, add_zero,
    sub_self, mul_zero, Finset.sum_const_zero]
  rw [Fintype.sum_prod_type]
  simp

theorem incZ_eq (x : Fin n) (e : G.edgeSet) :
    incZ G o x e = (if vB (o e).snd = vB x then 1 else 0) - (if vB (o e).fst = vB x then 1 else 0) := by
  simp [incZ, vB_inj, eq_comm]

theorem incZ_eq' (x : Fin n) (e : G.edgeSet) :
    incZ G o x e = (if vC (o e).snd = vC x then 1 else 0) - (if vC (o e).fst = vC x then 1 else 0) := by
  simp [incZ, vC_inj, eq_comm]

theorem triChain_outF_B (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) (x : Fin n) :
    outF (triChain G o z wB wC) (vB x) =
      ∑ a, z a x + ∑ e, incZ G o x e * ∑ a, wB e a := by
  rw [outF_triChain]
  have h1 : ∑ p : Fin n × Fin n, z p.1 p.2 * outF (tri p.1 p.2 (p.1 + p.2)) (vB x) =
      ∑ a, z a x := by
    simp only [outF_tri, vA_ne_vB, vB_inj, vC_ne_vB, if_false, zero_add, add_zero]
    rw [Fintype.sum_prod_type]
    simp
  have h2 : ∑ q : G.edgeSet × Fin n, wB q.1 q.2 * outF (mB G o q.1 q.2) (vB x) =
      ∑ e, incZ G o x e * ∑ a, wB e a := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [outF_mB, incZ_eq]; ring
  have h3 : ∑ q : G.edgeSet × Fin n, wC q.1 q.2 * outF (mC G o q.1 q.2) (vB x) = 0 := by
    simp [outF_mC, vC_ne_vB]
  rw [h1, h2, h3, add_zero]

theorem triChain_outF_C (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) (x : Fin n) :
    outF (triChain G o z wB wC) (vC x) =
      ∑ a, z a (x - a) + ∑ e, incZ G o x e * ∑ a, wC e a := by
  rw [outF_triChain]
  have h1 : ∑ p : Fin n × Fin n, z p.1 p.2 * outF (tri p.1 p.2 (p.1 + p.2)) (vC x) =
      ∑ a, z a (x - a) := by
    simp only [outF_tri, vA_ne_vC, vB_ne_vC, vC_inj, if_false, zero_add]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single (x - a)]
    · simp
    · intro b _ hb
      rw [if_neg]
      · ring
      · intro h; apply hb; rw [← h]; abel
    · simp
  have h2 : ∑ q : G.edgeSet × Fin n, wB q.1 q.2 * outF (mB G o q.1 q.2) (vC x) = 0 := by
    simp [outF_mB, vB_ne_vC]
  have h3 : ∑ q : G.edgeSet × Fin n, wC q.1 q.2 * outF (mC G o q.1 q.2) (vC x) =
      ∑ e, incZ G o x e * ∑ a, wC e a := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [outF_mC, incZ_eq']; ring
  rw [h1, h2, h3, add_zero]

/-! ### The Latin rows -/

/-- Latin row coefficients: `z_ab = [(b - a) mod n < d]`. -/
def zRow (d : Fin n → ℕ) (a b : Fin n) : ℤ := if (b - a).val < d a then 1 else 0

theorem sum_zRow (d : Fin n → ℕ) (hd : ∀ a, d a ≤ n) (a : Fin n) :
    ∑ b, zRow d a b = d a := by
  unfold zRow
  rw [Finset.sum_boole]
  have : (univ.filter (fun b : Fin n => (b - a).val < d a)).card =
      (univ.filter (fun c : Fin n => c.val < d a)).card := by
    apply Finset.card_bij (fun b _ => b - a)
    · intro b hb; simpa using hb
    · intro b _ b' _ h; exact sub_left_injective h
    · intro c hc
      refine ⟨c + a, ?_, by abel⟩
      simpa using hc
  rw [this, card_fin_val_lt n (d a) (hd a)]

theorem zRow_nonneg (d : Fin n → ℕ) (a b : Fin n) : 0 ≤ zRow d a b := by
  unfold zRow; split_ifs <;> norm_num

theorem zRow_le_one (d : Fin n → ℕ) (a b : Fin n) : zRow d a b ≤ 1 := by
  unfold zRow; split_ifs <;> norm_num

theorem sum_col_zRow_le (d : Fin n → ℕ) (b : Fin n) : ∑ a, zRow d a b ≤ n := by
  calc ∑ a, zRow d a b ≤ ∑ _a : Fin n, (1 : ℤ) := Finset.sum_le_sum fun a _ => zRow_le_one d a b
    _ = n := by simp

theorem sum_col_zRow_nonneg (d : Fin n → ℕ) (b : Fin n) : 0 ≤ ∑ a, zRow d a b :=
  Finset.sum_nonneg fun a _ => zRow_nonneg d a b

theorem sum_diag_zRow (d : Fin n → ℕ) (hd : ∀ a, d a ≤ n) :
    ∑ c, ∑ a, zRow d a (c - a) = ∑ a, (d a : ℤ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← sum_zRow d hd a]
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun c => rfl)

/-! ### Profile normalization -/

variable (ho : ∀ e, (o e).edge = e.val)

include ho in
/-- **Profile normalization (§5).** For every balanced `L ⊆ Qc n` there is a triangle chain with
Latin coefficients in `{0,1}` and move coefficients `|w| ≤ 21` whose out-profile equals the
out-degree profile of `L` at every vertex. -/
theorem profile_normalization (hexp : ExpandingFlowInverse.Expands G (1 / 20))
    (L : Finset (Vc n × Vc n)) (hLQ : L ⊆ Qc n) (hbal : Balanced L) :
    ∃ (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ),
      (∀ a b, |z a b| ≤ 1) ∧ (∀ e a, |wB e a| ≤ 21) ∧ (∀ e a, |wC e a| ≤ 21) ∧
      ∀ w, outF (triChain G o z wB wC) w = outDeg L w := by
  classical
  let dA : Fin n → ℕ := fun x => outDeg L (vA x)
  have hdA : ∀ a, dA a ≤ n := fun a => outDeg_le_n L hLQ _
  let z := zRow dA
  obtain ⟨htB, htC⟩ := class_totals L hLQ hbal
  -- the `B` defect
  let gB : Fin n → ℤ := fun x => (outDeg L (vB x) : ℤ) - ∑ a, z a x
  have hgB : ∑ x, gB x = 0 := by
    simp only [gB, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp only [z, sum_zRow dA hdA]
    have h : ((∑ x, outDeg L (vB x) : ℕ) : ℤ) = ((∑ x, dA x : ℕ) : ℤ) := by rw [htB]
    push_cast at h; linarith
  have hgBb : ∀ x, |(gB x : ℝ)| ≤ n := by
    intro x
    have h1 := outDeg_le_n L hLQ (vB x)
    have h2 := sum_col_zRow_le dA x
    have h3 := sum_col_zRow_nonneg dA x
    have : |gB x| ≤ n := by
      rw [abs_le]; simp only [gB, z]; constructor <;> push_cast <;> omega
    exact_mod_cast this
  -- the `C` defect
  let gC : Fin n → ℤ := fun x => (outDeg L (vC x) : ℤ) - ∑ a, z a (x - a)
  have hgC : ∑ x, gC x = 0 := by
    simp only [gC, Finset.sum_sub_distrib]
    simp only [z, sum_diag_zRow dA hdA]
    have h : ((∑ x, outDeg L (vC x) : ℕ) : ℤ) = ((∑ x, dA x : ℕ) : ℤ) := by rw [htC]
    push_cast at h; linarith
  have hgCb : ∀ x, |(gC x : ℝ)| ≤ n := by
    intro x
    have h1 := outDeg_le_n L hLQ (vC x)
    have h2 : ∑ a, z a (x - a) ≤ n := by
      calc ∑ a, z a (x - a) ≤ ∑ _a : Fin n, (1 : ℤ) :=
            Finset.sum_le_sum fun a _ => zRow_le_one dA a _
        _ = n := by simp
    have h3 : 0 ≤ ∑ a, z a (x - a) := Finset.sum_nonneg fun a _ => zRow_nonneg dA a _
    have : |gC x| ≤ n := by
      rw [abs_le]; simp only [gC]; constructor <;> omega
    exact_mod_cast this
  -- integer flows
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨FB, hFB, hFBb⟩ := integer_flow G o ho (1 / 20) (by norm_num) hexp gB hgB n hn0 hgBb
  obtain ⟨FC, hFC, hFCb⟩ := integer_flow G o ho (1 / 20) (by norm_num) hexp gC hgC n hn0 hgCb
  have hbound : ∀ F : G.edgeSet → ℤ, (∀ e, |(F e : ℝ)| < n / (1 / 20) + 1) →
      ∀ e, |F e| ≤ 20 * n := by
    intro F hF e
    have h := hF e
    have h' : |(F e : ℝ)| < 20 * n + 1 := by
      have : (n : ℝ) / (1 / 20) = 20 * n := by ring
      linarith
    have h'' : |F e| < 20 * n + 1 := by exact_mod_cast h'
    omega
  refine ⟨z, fun e a => split n (FB e) a, fun e a => split n (FC e) a, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [abs_le]
    exact ⟨by linarith [zRow_nonneg dA a b], zRow_le_one dA a b⟩
  · intro e a
    have := abs_split_le n (FB e) 20 (by exact_mod_cast hbound FB hFBb e) a
    push_cast at this; linarith
  · intro e a
    have := abs_split_le n (FC e) 20 (by exact_mod_cast hbound FC hFCb e) a
    push_cast at this; linarith
  · intro w
    obtain ⟨i, x⟩ := w
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      revert i; decide
    rcases hi with rfl | rfl | rfl
    · change outF _ (vA x) = _
      rw [triChain_outF_A]
      exact_mod_cast sum_zRow dA hdA x
    · change outF _ (vB x) = _
      rw [triChain_outF_B]
      simp only [sum_split]
      rw [hFB x]
      simp only [gB, vB]
      ring
    · change outF _ (vC x) = _
      rw [triChain_outF_C]
      simp only [sum_split]
      rw [hFC x]
      simp only [gC, vC]
      ring

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
