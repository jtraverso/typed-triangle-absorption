/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.Profile

@[expose] public section

/-!
# The integer face filling of every balanced demand (§6)

The fixed face family `faceFun G o : FIdx G → (Vc n × Vc n → ℤ)` consists of the Latin triangles,
the `B`- and `C`-moves and the rectangles of the three blocks.  For **every** balanced
`L ⊆ Qc n` (`core_filling`) there are integer coefficients `a` with

* `∑_φ a_φ · faceFun φ (α) = χ_L(α)` for every arc `α`, and
* `∑_φ |a_φ| · |faceFun φ (α)| ≤ Tc` for every arc `α`,

where `Tc = 3 + 2 · 21 · 32 + 1078401 · 256` is an absolute constant.  The residual of the
profile-normalizing triangle chain has zero margins in every block; each block is filled by the
bounded integer rectangular inverse `RealTensorFilling.bounded_integer_preimage` on the fixed
expander.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Matrix Positivization Cycles OrientedCycleVector

variable {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart)

/-- Face indices: Latin triangles, `B`-moves, `C`-moves, rectangles. -/
abbrev FIdx := (Fin n × Fin n) ⊕ ((G.edgeSet × Fin n) ⊕ ((G.edgeSet × Fin n) ⊕
  (ZMod 3 × G.edgeSet × G.edgeSet)))

/-- The arc function of each face. -/
def faceFun : FIdx G → Vc n × Vc n → ℤ
  | Sum.inl p => tri p.1 p.2 (p.1 + p.2)
  | Sum.inr (Sum.inl q) => mB G o q.1 q.2
  | Sum.inr (Sum.inr (Sum.inl q)) => mC G o q.1 q.2
  | Sum.inr (Sum.inr (Sum.inr r)) => rect G o r.1 r.2.1 r.2.2

/-- The fixed faces (positivization format). -/
def dFace (φ : FIdx G) : Face (Vc n) := faceOf (faceFun G o φ)

theorem faceFun_unit (φ : FIdx G) : IsUnitF (faceFun G o φ) := by
  rcases φ with p | q | q | r
  · exact tri_unit _ _ _
  · exact mB_unit G o _ _
  · exact mC_unit G o _ _
  · exact rect_unit G o _ _ _

theorem faceFun_circ (φ : FIdx G) : IsCircF (faceFun G o φ) := by
  rcases φ with p | q | q | r
  · exact tri_circ _ _ _
  · exact mB_circ G o _ _
  · exact mC_circ G o _ _
  · exact rect_circ G o _ _ _

theorem dFace_val (φ : FIdx G) (α : Vc n × Vc n) : (dFace G o φ).val α = faceFun G o φ α :=
  faceOf_val _ (faceFun_unit G o φ) α

theorem dFace_isCirc (φ : FIdx G) : (dFace G o φ).IsCirc :=
  faceOf_isCirc _ (faceFun_unit G o φ) (faceFun_circ G o φ)

theorem mem_Qc_rect (i : ZMod 3) (x y : Fin n) : (((i, x), (i + 1, y)) : Vc n × Vc n) ∈ Qc n := by
  rw [mem_Qc]

/-- The support of every face lies in `Qc n` and has at most four arcs. -/
theorem faceFun_supp (φ : FIdx G) :
    ∃ S : Finset (Vc n × Vc n), S ⊆ Qc n ∧ S.card ≤ 4 ∧ ∀ α, faceFun G o φ α ≠ 0 → α ∈ S := by
  rcases φ with p | q | q | r
  · refine ⟨_, ?_, (card_le_three _ _ _).trans (by norm_num), tri_supp p.1 p.2 (p.1 + p.2)⟩
    intro α hα
    simp only [mem_insert, mem_singleton] at hα
    rcases hα with rfl | rfl | rfl
    · exact mem_Qc_A_B _ _
    · exact mem_Qc_B_C _ _
    · exact mem_Qc_C_A _ _
  · refine ⟨_, ?_, card_le_four _ _ _ _, mB_supp G o q.1 q.2⟩
    intro α hα
    simp only [mem_insert, mem_singleton] at hα
    rcases hα with rfl | rfl | rfl | rfl
    · exact mem_Qc_A_B _ _
    · exact mem_Qc_B_C _ _
    · exact mem_Qc_A_B _ _
    · exact mem_Qc_B_C _ _
  · refine ⟨_, ?_, card_le_four _ _ _ _, mC_supp G o q.1 q.2⟩
    intro α hα
    simp only [mem_insert, mem_singleton] at hα
    rcases hα with rfl | rfl | rfl | rfl
    · exact mem_Qc_B_C _ _
    · exact mem_Qc_C_A _ _
    · exact mem_Qc_B_C _ _
    · exact mem_Qc_C_A _ _
  · refine ⟨_, ?_, card_le_four _ _ _ _, rect_supp G o r.1 r.2.1 r.2.2⟩
    intro α hα
    simp only [mem_insert, mem_singleton] at hα
    rcases hα with rfl | rfl | rfl | rfl <;> exact mem_Qc_rect _ _ _

theorem faceFun_mem_Qc (φ : FIdx G) (α : Vc n × Vc n) (h : faceFun G o φ α ≠ 0) : α ∈ Qc n := by
  obtain ⟨S, hS, -, hα⟩ := faceFun_supp G o φ
  exact hS (hα α h)

theorem dFace_supp_subset (φ : FIdx G) : (dFace G o φ).supp ⊆ Qc n :=
  faceOf_supp_subset _ _ (faceFun_mem_Qc G o φ)

theorem dFace_card (φ : FIdx G) : (dFace G o φ).supp.card ≤ 4 := by
  obtain ⟨S, -, hS4, hα⟩ := faceFun_supp G o φ
  exact (card_le_card (faceOf_supp_subset _ S hα)).trans hS4

theorem incZ_snd (e : G.edgeSet) : incZ G o (o e).snd e = 1 := by
  have := dart_fst_ne_snd (o e)
  simp [incZ, Ne.symm this]

theorem dFace_nonempty (φ : FIdx G) : (dFace G o φ).supp.Nonempty := by
  rcases φ with p | q | q | r
  · refine faceOf_supp_nonempty _ (vA p.1, vB p.2) ?_
    simp [faceFun, tri_apply, vA_ne_vB, vA_ne_vC, vB_ne_vC, vB_ne_vA, vC_ne_vA, vC_ne_vB]
  · refine faceOf_supp_nonempty _ (vA q.2, vB (o q.1).snd) ?_
    have hfs := dart_fst_ne_snd (o q.1)
    simp [faceFun, mB_apply, vA_ne_vB, vB_ne_vA, vB_ne_vC, vB_inj, Ne.symm hfs]
  · refine faceOf_supp_nonempty _ (vB ((o q.1).fst - q.2), vC (o q.1).snd) ?_
    have hfs := dart_fst_ne_snd (o q.1)
    simp [faceFun, mC_apply, vB_ne_vC, vC_ne_vA, vC_ne_vB, vC_inj, Ne.symm hfs]
  · refine faceOf_supp_nonempty _ ((r.1, (o r.2.1).snd), (r.1 + 1, (o r.2.2).snd)) ?_
    simp [faceFun, rect, incZ_snd]

/-! ### Residual of the triangle chain -/

section Residual

variable (L : Finset (Vc n × Vc n))

theorem triChain_eq_sum (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) :
    triChain G o z wB wC = ∑ p : Fin n × Fin n, z p.1 p.2 • faceFun G o (Sum.inl p) +
      ∑ q : G.edgeSet × Fin n, wB q.1 q.2 • faceFun G o (Sum.inr (Sum.inl q)) +
      ∑ q : G.edgeSet × Fin n, wC q.1 q.2 • faceFun G o (Sum.inr (Sum.inr (Sum.inl q))) := rfl

theorem triChain_circ (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ) :
    IsCircF (triChain G o z wB wC) := by
  intro w
  rw [triChain_eq_sum]
  simp only [inF_add, outF_add, inF_sum, outF_sum, faceFun_circ G o _ w]

theorem triChain_supp (z : Fin n → Fin n → ℤ) (wB wC : G.edgeSet → Fin n → ℤ)
    (α : Vc n × Vc n) (hα : α ∉ Qc n) : triChain G o z wB wC α = 0 := by
  have h0 : ∀ φ, faceFun G o φ α = 0 := fun φ => by
    by_contra h; exact hα (faceFun_mem_Qc G o φ α h)
  rw [triChain_eq_sum]
  simp [Finset.sum_apply, h0]

/-- Row sums of a block of an arc function supported in `Qc n`. -/
theorem block_row (X : Vc n × Vc n → ℤ) (hX : ∀ α, α ∉ Qc n → X α = 0) (i : ZMod 3)
    (x : Fin n) : ∑ y, X ((i, x), (i + 1, y)) = outF X (i, x) := by
  unfold outF
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (i + 1)]
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro y _
    apply hX
    rw [mem_Qc]; exact hj
  · simp

/-- Column sums of a block of an arc function supported in `Qc n`. -/
theorem block_col (X : Vc n × Vc n → ℤ) (hX : ∀ α, α ∉ Qc n → X α = 0) (i : ZMod 3)
    (y : Fin n) : ∑ x, X ((i, x), (i + 1, y)) = inF X (i + 1, y) := by
  unfold inF
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro x _
    apply hX
    rw [mem_Qc]
    intro h; exact hj (add_right_cancel h).symm
  · simp

/-- Integer entries of the two-sided incidence product. -/
theorem incidence_entry (c : Matrix G.edgeSet G.edgeSet ℤ) (X : Matrix (Fin n) (Fin n) ℤ)
    (h : incidence G o * c.map (Int.castRingHom ℝ) * (incidence G o).transpose =
      X.map (Int.castRingHom ℝ)) (x y : Fin n) :
    ∑ e, ∑ e', c e e' * (incZ G o x e * incZ G o y e') = X x y := by
  have h1 := congrFun (congrFun h x) y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, incidence_eq_incZ,
    Int.coe_castRingHom] at h1
  have h2 : ((∑ e, ∑ e', c e e' * (incZ G o x e * incZ G o y e') : ℤ) : ℝ) = (X x y : ℝ) := by
    rw [← h1]
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e' _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  exact_mod_cast h2

end Residual

/-! ### The filling -/

/-- The per-arc load bound of the integer face filling. -/
def Tc : ℕ := 3 + 2 * 21 * 32 + 1078401 * 256

variable (ho : ∀ e, (o e).edge = e.val)

include ho in
/-- Number of faces through an arc (measured by `∑ |value|`). -/
theorem faceFun_count (hdeg : ∀ v, G.degree v ≤ 8) (α : Vc n × Vc n) :
    ∑ φ, |faceFun G o φ α| ≤ 3 + 32 + 32 + 256 := by
  simp only [Fintype.sum_sum_type, faceFun]
  have h1 := tri_count α
  have h2 := mB_count G o ho 8 hdeg α
  have h3 := mC_count G o ho 8 hdeg α
  have h4 := rect_count G o ho 8 hdeg α
  push_cast at h2 h3 h4
  linarith

include ho in
/-- **Integer face filling of every balanced demand with bounded per-arc load (§6).** -/
theorem core_filling (hdeg : ∀ v, G.degree v ≤ 8) (hexp : ExpandingFlowInverse.Expands G (1 / 20))
    (hconn : G.Connected) (L : Finset (Vc n × Vc n)) (hLQ : L ⊆ Qc n) (hbal : Balanced L) :
    ∃ a : FIdx G → ℤ, (∀ α, ∑ φ, a φ * faceFun G o φ α = if α ∈ L then 1 else 0) ∧
      ∀ α, ∑ φ, |a φ| * |faceFun G o φ α| ≤ Tc := by
  classical
  obtain ⟨z, wB, wC, hz, hwB, hwC, hout⟩ := profile_normalization G o ho hexp L hLQ hbal
  set Y := triChain G o z wB wC with hYdef
  let X : Vc n × Vc n → ℤ := chiF L - Y
  have hXsupp : ∀ α, α ∉ Qc n → X α = 0 := by
    intro α hα
    have h1 : α ∉ L := fun h => hα (hLQ h)
    simp [X, chiF, h1, Y, triChain_supp G o z wB wC α hα]
  have hXout : ∀ w, outF X w = 0 := by
    intro w; simp only [X, outF_sub, outF_chiF, hout, sub_self]
  have hXin : ∀ w, inF X w = 0 := by
    intro w
    simp only [X, inF_sub]
    rw [chiF_circ L hbal w, triChain_circ G o z wB wC w, outF_chiF]
    exact sub_eq_zero.mpr (hout w).symm
  -- bound on the triangle chain
  have hYb : ∀ α, |Y α| ≤ 1347 := by
    intro α
    rw [hYdef, triChain]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |∑ p : Fin n × Fin n, z p.1 p.2 * tri p.1 p.2 (p.1 + p.2) α| ≤ 3 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (Finset.sum_le_sum fun p _ => ?_) (tri_count α)
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hz _ _)
    have h2 : |∑ q : G.edgeSet × Fin n, wB q.1 q.2 * mB G o q.1 q.2 α| ≤ 21 * 32 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ q : G.edgeSet × Fin n, 21 * |mB G o q.1 q.2 α| :=
            Finset.sum_le_sum fun q _ => by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hwB _ _) (abs_nonneg _)
        _ = 21 * ∑ q : G.edgeSet × Fin n, |mB G o q.1 q.2 α| := by rw [Finset.mul_sum]
        _ ≤ 21 * 32 := by
            have := mB_count G o ho 8 hdeg α
            push_cast at this; linarith
    have h3 : |∑ q : G.edgeSet × Fin n, wC q.1 q.2 * mC G o q.1 q.2 α| ≤ 21 * 32 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ q : G.edgeSet × Fin n, 21 * |mC G o q.1 q.2 α| :=
            Finset.sum_le_sum fun q _ => by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hwC _ _) (abs_nonneg _)
        _ = 21 * ∑ q : G.edgeSet × Fin n, |mC G o q.1 q.2 α| := by rw [Finset.mul_sum]
        _ ≤ 21 * 32 := by
            have := mC_count G o ho 8 hdeg α
            push_cast at this; linarith
    calc _ ≤ |∑ p : Fin n × Fin n, z p.1 p.2 * tri p.1 p.2 (p.1 + p.2) α +
          ∑ q : G.edgeSet × Fin n, wB q.1 q.2 * mB G o q.1 q.2 α| +
          |∑ q : G.edgeSet × Fin n, wC q.1 q.2 * mC G o q.1 q.2 α| := abs_add_le _ _
      _ ≤ |∑ p : Fin n × Fin n, z p.1 p.2 * tri p.1 p.2 (p.1 + p.2) α| +
          |∑ q : G.edgeSet × Fin n, wB q.1 q.2 * mB G o q.1 q.2 α| +
          |∑ q : G.edgeSet × Fin n, wC q.1 q.2 * mC G o q.1 q.2 α| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 1347 := by linarith
  have hXb : ∀ α, |X α| ≤ 1348 := by
    intro α
    have h1 : |chiF L α| ≤ 1 := by unfold chiF; split_ifs <;> simp
    calc |X α| = |chiF L α - Y α| := rfl
      _ ≤ |chiF L α| + |Y α| := abs_sub _ _
      _ ≤ 1348 := by linarith [hYb α]
  -- the blocks
  let Xb : ZMod 3 → Matrix (Fin n) (Fin n) ℤ := fun i x y => X ((i, x), (i + 1, y))
  have hrow : ∀ i x, ∑ y, Xb i x y = 0 := fun i x => by
    simp only [Xb]; rw [block_row X hXsupp i x, hXout]
  have hcol : ∀ i y, ∑ x, Xb i x y = 0 := fun i y => by
    simp only [Xb]; rw [block_col X hXsupp i y, hXin]
  have hrect : ∀ i : ZMod 3, ∃ c : Matrix G.edgeSet G.edgeSet ℤ,
      incidence G o * c.map (Int.castRingHom ℝ) * (incidence G o).transpose =
        (Xb i).map (Int.castRingHom ℝ) ∧ ∀ e e', |c e e'| ≤ 1078401 := by
    intro i
    obtain ⟨c, hc, hcb⟩ := RealTensorFilling.bounded_integer_preimage G G o o ho ho hconn hconn
      (1 / 20) (1 / 20) (by norm_num) (by norm_num) hexp hexp (Xb i) (hcol i) (hrow i) 1348
      (by norm_num) (fun x y => by exact_mod_cast hXb _)
    refine ⟨c, hc, fun e e' => ?_⟩
    have h1 := hcb e e'
    have h2 : |(c e e' : ℝ)| < 1078402 := by norm_num at h1 ⊢; linarith
    have h3 : |c e e'| < 1078402 := by exact_mod_cast h2
    omega
  choose c hc hcb using hrect
  -- the rectangle chain reproduces the residual
  have hR : ∀ α, ∑ r : ZMod 3 × G.edgeSet × G.edgeSet,
      c r.1 r.2.1 r.2.2 * rect G o r.1 r.2.1 r.2.2 α = X α := by
    rintro ⟨⟨j, x⟩, ⟨k, y⟩⟩
    by_cases hk : k = j + 1
    · subst hk
      rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
      · rw [Fintype.sum_prod_type]
        have := incidence_entry G o (c j) (Xb j) (hc j) x y
        simp only [rect, and_self, if_true]
        rw [this]
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro r _
        simp [rect, Ne.symm hi]
      · simp
    · rw [hXsupp _ (by rw [mem_Qc]; exact hk)]
      apply Finset.sum_eq_zero
      intro r _
      simp only [rect]
      rw [if_neg, mul_zero]
      rintro ⟨rfl, h⟩; exact hk h
  -- the coefficients
  let a : FIdx G → ℤ := Sum.elim (fun p => z p.1 p.2) (Sum.elim (fun q => wB q.1 q.2)
    (Sum.elim (fun q => wC q.1 q.2) (fun r => c r.1 r.2.1 r.2.2)))
  refine ⟨a, fun α => ?_, fun α => ?_⟩
  · simp only [Fintype.sum_sum_type, a, Sum.elim_inl, Sum.elim_inr, faceFun]
    rw [hR α]
    have hY : Y α = ∑ p : Fin n × Fin n, z p.1 p.2 * tri p.1 p.2 (p.1 + p.2) α +
        ∑ q : G.edgeSet × Fin n, wB q.1 q.2 * mB G o q.1 q.2 α +
        ∑ q : G.edgeSet × Fin n, wC q.1 q.2 * mC G o q.1 q.2 α := by
      rw [hYdef, triChain]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hX : X α = chiF L α - Y α := rfl
    have hchi : chiF L α = if α ∈ L then 1 else 0 := rfl
    rw [hX, hY, ← hchi]
    ring
  · simp only [Fintype.sum_sum_type, a, Sum.elim_inl, Sum.elim_inr, faceFun]
    have h1 : ∑ p : Fin n × Fin n, |z p.1 p.2| * |tri p.1 p.2 (p.1 + p.2) α| ≤ 3 :=
      le_trans (Finset.sum_le_sum fun p _ => mul_le_of_le_one_left (abs_nonneg _) (hz _ _))
        (tri_count α)
    have h2 : ∑ q : G.edgeSet × Fin n, |wB q.1 q.2| * |mB G o q.1 q.2 α| ≤ 21 * 32 := by
      calc _ ≤ ∑ q : G.edgeSet × Fin n, 21 * |mB G o q.1 q.2 α| :=
            Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hwB _ _) (abs_nonneg _)
        _ = 21 * ∑ q : G.edgeSet × Fin n, |mB G o q.1 q.2 α| := by rw [Finset.mul_sum]
        _ ≤ 21 * 32 := by
            have := mB_count G o ho 8 hdeg α
            push_cast at this; linarith
    have h3 : ∑ q : G.edgeSet × Fin n, |wC q.1 q.2| * |mC G o q.1 q.2 α| ≤ 21 * 32 := by
      calc _ ≤ ∑ q : G.edgeSet × Fin n, 21 * |mC G o q.1 q.2 α| :=
            Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hwC _ _) (abs_nonneg _)
        _ = 21 * ∑ q : G.edgeSet × Fin n, |mC G o q.1 q.2 α| := by rw [Finset.mul_sum]
        _ ≤ 21 * 32 := by
            have := mC_count G o ho 8 hdeg α
            push_cast at this; linarith
    have h4 : ∑ r : ZMod 3 × G.edgeSet × G.edgeSet,
        |c r.1 r.2.1 r.2.2| * |rect G o r.1 r.2.1 r.2.2 α| ≤ 1078401 * 256 := by
      calc _ ≤ ∑ r : ZMod 3 × G.edgeSet × G.edgeSet, 1078401 * |rect G o r.1 r.2.1 r.2.2 α| :=
            Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcb _ _ _) (abs_nonneg _)
        _ = 1078401 * ∑ r : ZMod 3 × G.edgeSet × G.edgeSet, |rect G o r.1 r.2.1 r.2.2 α| := by
            rw [Finset.mul_sum]
        _ ≤ 1078401 * 256 := by
            have := rect_count G o ho 8 hdeg α
            push_cast at this; linarith
    unfold Tc
    push_cast
    linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
