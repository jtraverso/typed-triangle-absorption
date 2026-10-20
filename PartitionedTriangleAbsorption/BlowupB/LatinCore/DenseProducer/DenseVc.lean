/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.Filling
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.Load

@[expose] public section

/-!
# The dense producer on the padded blow-up `Vc n`

`dense_on_Vc`: for every `n ≥ 1` and every `D ⊆ Qc n`, the reserve `reserve (Qc n) Tc` and the
catalogue `catalogue dFace (Qc n) D` (fixed before the demand) satisfy

* the reserve is cyclically tripartite and arc-disjoint from `D`;
* every piece is nonempty, balanced, has at most `20` arcs and lies in `R ∪ D`;
* `|catalogue| ≤ Ccard · n²` and every vertex load is `≤ Cload · n`;
* every balanced `L ⊆ D` is exactly partitioned (together with `R`) by catalogue pieces.

The filling of `L` is `core_filling`; the positive realization is `positivization_exact_cover`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Positivization Cycles

/-- Catalogue size constant. -/
def Ccard : ℕ := 114 * Tc ^ 4 + 9 * Tc ^ 2 + 9

/-- Catalogue vertex-load constant. -/
def Cload : ℕ := (646 * Tc ^ 4 + Tc ^ 2 + 1) * (120 * Tc + 22)

theorem Tc_pos : 0 < Tc := by unfold Tc; norm_num

theorem exists_orientation {V : Type} (G : SimpleGraph V) :
    ∃ o : G.edgeSet → G.Dart, ∀ e, (o e).edge = e.val := by
  have : ∀ e : G.edgeSet, ∃ d : G.Dart, d.edge = e.val := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y => exact ⟨⟨(x, y), he⟩, rfl⟩
  choose o ho using this
  exact ⟨o, ho⟩

variable {n : ℕ} [NeZero n]

theorem card_Vc_arcs : Fintype.card (Vc n × Vc n) = 9 * n ^ 2 := by
  simp [Fintype.card_prod, ZMod.card]; ring

theorem Qc_touch (u : Vc n) :
    ((Qc n).filter (fun e => e.1 = u ∨ e.2 = u)).card ≤ 6 * n := by
  calc _ ≤ (({u} ×ˢ (univ : Finset (Vc n))) ∪ ((univ : Finset (Vc n)) ×ˢ {u})).card := by
        apply card_le_card
        intro e he
        simp only [mem_filter] at he
        rcases he.2 with h | h
        · exact mem_union_left _ (mem_product.mpr ⟨by simp [h], mem_univ _⟩)
        · exact mem_union_right _ (mem_product.mpr ⟨mem_univ _, by simp [h]⟩)
    _ ≤ ({u} ×ˢ (univ : Finset (Vc n))).card + ((univ : Finset (Vc n)) ×ˢ {u}).card :=
        card_union_le _ _
    _ = 6 * n := by simp [card_product, ZMod.card]; ring

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (o : G.edgeSet → G.Dart)
    (ho : ∀ e, (o e).edge = e.val)

theorem card_edgeSet_le (hdeg : ∀ v, G.degree v ≤ 8) : Fintype.card G.edgeSet ≤ 4 * n := by
  have h := G.sum_degrees_eq_twice_card_edges
  rw [SimpleGraph.edgeFinset_card] at h
  have : ∑ v, G.degree v ≤ ∑ _v : Fin n, 8 := Finset.sum_le_sum fun v _ => hdeg v
  simp at this
  omega

theorem card_FIdx_le (hdeg : ∀ v, G.degree v ≤ 8) : Fintype.card (FIdx G) ≤ 57 * n ^ 2 := by
  have hE := card_edgeSet_le G hdeg
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  nlinarith

include ho in
theorem dFace_count (hdeg : ∀ v, G.degree v ≤ 8) (e : Vc n × Vc n) :
    (univ.filter (fun φ => e ∈ (dFace G o φ).supp)).card ≤ 323 := by
  have h := faceFun_count G o ho hdeg e
  have h2 : ((univ.filter (fun φ => e ∈ (dFace G o φ).supp)).card : ℤ) ≤
      ∑ φ, |faceFun G o φ e| := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_le_sum
    intro φ _
    split_ifs with hφ
    · rw [dFace, mem_faceOf_supp] at hφ
      rcases faceFun_unit G o φ e with h | h | h
      · rw [h]; norm_num
      · exact absurd h hφ
      · rw [h]; norm_num
    · exact abs_nonneg _
  have : ((univ.filter (fun φ => e ∈ (dFace G o φ).supp)).card : ℤ) ≤ 323 := by linarith
  exact_mod_cast this

/-- **The dense producer on the padded blow-up.** -/
theorem dense_on_Vc (D : Finset (Vc n × Vc n)) (hDQ : D ⊆ Qc n) :
    ∃ (R : Finset (XV (Vc n) Tc × XV (Vc n) Tc))
      (lib : Finset (Finset (XV (Vc n) Tc × XV (Vc n) Tc))),
      IsCyc (Sum.elim (fun v : Vc n => v.1) (privColor (fun v : Vc n => v.1))) R ∧
      Disjoint R (D.map (liftArc (Vc n) (Priv (Vc n) Tc))) ∧
      (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪ D.map (liftArc (Vc n) (Priv (Vc n) Tc)) ∧
        P.card ≤ 20 ∧ Balanced P) ∧
      lib.card ≤ Ccard * n ^ 2 ∧
      (∀ v, catalogLoad lib v ≤ Cload * n) ∧
      ∀ L ⊆ D, Balanced L →
        ∃ P ⊆ lib, (P : Set (Finset (XV (Vc n) Tc × XV (Vc n) Tc))).PairwiseDisjoint id ∧
          P.biUnion id = R ∪ L.map (liftArc (Vc n) (Priv (Vc n) Tc)) := by
  classical
  obtain ⟨G, hdec, hdeg, hexp, hconn⟩ := exists_good_expander n
  obtain ⟨o, ho⟩ := exists_orientation G
  have hT : 0 < Tc := Tc_pos
  let face := dFace G o
  have hsupp : ∀ φ, (face φ).supp ⊆ Qc n := dFace_supp_subset G o
  have hprops := catalogue_props (fun v : Vc n => v.1) (Qc n) D (Qc_isCyc n) hDQ hT face hsupp
    (dFace_nonempty G o) (dFace_isCirc G o) 4 (dFace_card G o)
  refine ⟨reserve (Qc n) Tc, catalogue face (Qc n) D hT, reserve_isCyc _ _ (Qc_isCyc n),
    reserve_disjoint_lift _ _, fun P hP => ?_, ?_, fun v => ?_, fun L hLD hbal => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := hprops P hP
    exact ⟨h1, h2, h3.trans (by norm_num), h4⟩
  · refine (catalogue_card_le (Qc n) D hT face).trans ?_
    have h1 : ∑ φ, 2 * Tc ^ (face φ).supp.card ≤ ∑ _φ : FIdx G, 2 * Tc ^ 4 :=
      Finset.sum_le_sum fun φ _ =>
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT (dFace_card G o φ))
    have h2 : ∑ _φ : FIdx G, 2 * Tc ^ 4 ≤ 57 * n ^ 2 * (2 * Tc ^ 4) := by
      rw [sum_const, card_univ, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_FIdx_le G hdeg)
    have h3 : (Qc n).card ≤ 9 * n ^ 2 := by
      rw [← card_Vc_arcs]; exact card_le_univ _
    have h4 : D.card ≤ 9 * n ^ 2 := (card_le_card hDQ).trans h3
    have h5 : (Qc n).card * Tc ^ 2 ≤ 9 * n ^ 2 * Tc ^ 2 := Nat.mul_le_mul_right _ h3
    unfold Ccard
    nlinarith
  · have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    refine (catalogue_load_le (Qc n) D hDQ hT face hsupp 4 323 (6 * n) (dFace_card G o)
      (dFace_count G o ho hdeg) Qc_touch v).trans ?_
    unfold Cload
    have : 2 * (5 * (2 * Tc * (6 * n) + 1) + 6 * n) ≤ (120 * Tc + 22) * n := by nlinarith
    calc _ ≤ (2 * 323 * Tc ^ 4 + Tc ^ 2 + 1) * ((120 * Tc + 22) * n) :=
          Nat.mul_le_mul_left _ this
      _ = _ := by ring
  · obtain ⟨a, hfill, hload⟩ := core_filling G o ho hdeg hexp hconn L (hLD.trans hDQ) hbal
    refine positivization_exact_cover (Qc n) D hDQ hT face hsupp L hLD a ?_ ?_
    · intro e _
      simp only [face, dFace_val]
      exact hfill e
    · intro e _
      simp only [face, dFace_val]
      exact_mod_cast hload e

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
