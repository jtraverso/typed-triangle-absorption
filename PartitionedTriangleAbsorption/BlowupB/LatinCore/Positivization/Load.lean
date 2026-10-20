/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.ExactCover
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoscopicSpec

@[expose] public section

/-!
# Vertex loads of the positive catalogue (§8)

`catalogue_load_le`: if every arc of `Q` lies in at most `m` faces, every face has at most `k`
arcs and every base vertex meets at most `q` arcs of `Q`, then at every vertex `v` of the
extended digraph

  `catalogLoad (catalogue face Q D hT) v ≤ (2 m T^k + T^2 + 1) * (2 * (10 T q + q + 5))`.

The proof double counts (piece, arc) incidences: the load is the sum, over the arcs of
`reserve ∪ D` at `v`, of the number of catalogue pieces containing the arc.  Each arc lies in at
most `2 m T^k + T^2 + 1` pieces, and at most `2 (10 T q + q + 5)` arcs meet `v`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization

open Finset PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

section DoubleCounting

variable {W : Type} [DecidableEq W]

theorem sum_card_filter_eq (lib : Finset (Finset (W × W))) (U : Finset (W × W))
    (hU : ∀ P ∈ lib, P ⊆ U) (pr : W × W → Prop) [DecidablePred pr] :
    ∑ P ∈ lib, (P.filter pr).card = ∑ α ∈ U.filter pr, (lib.filter (fun P => α ∈ P)).card := by
  have h1 : ∀ P ∈ lib, (P.filter pr).card = ∑ α ∈ U.filter pr, if α ∈ P then 1 else 0 := by
    intro P hP
    rw [Finset.sum_boole]
    congr 1
    ext α
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨hU P hP h1, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_boole]
  simp

theorem catalogLoad_le_mult (lib : Finset (Finset (W × W))) (U : Finset (W × W))
    (hU : ∀ P ∈ lib, P ⊆ U) (M : ℕ) (hM : ∀ α ∈ U, (lib.filter (fun P => α ∈ P)).card ≤ M)
    (v : W) :
    catalogLoad lib v ≤ M * ((U.filter (fun α => α.2 = v)).card +
      (U.filter (fun α => α.1 = v)).card) := by
  unfold catalogLoad deg inDeg outDeg
  rw [Finset.sum_add_distrib, sum_card_filter_eq lib U hU, sum_card_filter_eq lib U hU, mul_add]
  apply add_le_add
  · calc _ ≤ ∑ _α ∈ U.filter (fun α => α.2 = v), M :=
          Finset.sum_le_sum fun α hα => hM α (mem_filter.mp hα).1
      _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]
  · calc _ ≤ ∑ _α ∈ U.filter (fun α => α.1 = v), M :=
          Finset.sum_le_sum fun α hα => hM α (mem_filter.mp hα).1
      _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]

theorem card_filter_image_le {X Y : Type} [DecidableEq Y] (g : X → Finset Y) (S : Finset X)
    (y : Y) : ((S.image g).filter (fun P => y ∈ P)).card ≤ (S.filter (fun x => y ∈ g x)).card := by
  classical
  rw [Finset.filter_image]
  exact card_image_le

end DoubleCounting

variable {H : Type} [Fintype H] [DecidableEq H] {T : ℕ}
variable {Φ : Type} [Fintype Φ] [DecidableEq Φ]

section Channels

omit [Fintype H] [DecidableEq H] in
theorem chanVert_inl {e : H × H} {b : Bool} {i : Fin T} {j : ℕ} {u : H}
    (h : chanVert e b i j = Sum.inl u) : u = e.1 ∨ u = e.2 := by
  unfold chanVert at h
  split_ifs at h with h0 h1
  · cases h; unfold chanStart; split_ifs <;> simp
  · cases h; unfold chanEnd; split_ifs <;> simp

omit [Fintype H] in
theorem chan_arc_inl {e : H × H} {b : Bool} {i : Fin T} {α : XV H T × XV H T}
    (hα : α ∈ chan e b i) {u : H} (hu : α.1 = Sum.inl u ∨ α.2 = Sum.inl u) :
    u = e.1 ∨ u = e.2 := by
  obtain ⟨j, -, rfl⟩ := mem_chan.mp hα
  rcases hu with hu | hu
  · exact chanVert_inl (j := j) hu
  · exact chanVert_inl (j := j + 1) hu

omit [Fintype H] in
theorem chan_arc_inr {e : H × H} {b : Bool} {i : Fin T} {α : XV H T × XV H T}
    (hα : α ∈ chan e b i) {p : Priv H T} (hp : α.1 = Sum.inr p ∨ α.2 = Sum.inr p) :
    privTok p = (e, b, i) := by
  obtain ⟨-, h1, h2⟩ := chan_arc_priv hα
  rcases hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

/-- Whether the channel `t` can carry an arc at `v`. -/
def Touches (v : XV H T) (t : (H × H) × Bool × Fin T) : Prop :=
  match v with
  | Sum.inl u => t.1.1 = u ∨ t.1.2 = u
  | Sum.inr p => privTok p = t

instance (v : XV H T) : DecidablePred (Touches v) := by
  intro t; cases v <;> unfold Touches <;> infer_instance

omit [Fintype H] in
theorem touches_of_mem {t : (H × H) × Bool × Fin T} {α : XV H T × XV H T}
    (hα : α ∈ chan t.1 t.2.1 t.2.2) {v : XV H T} (hv : α.1 = v ∨ α.2 = v) : Touches v t := by
  rcases v with u | p
  · have := chan_arc_inl hα hv
    unfold Touches; rcases this with h | h <;> simp [h]
  · exact chan_arc_inr hα hv

omit [Fintype H] in
theorem card_chan_filter_le (t : (H × H) × Bool × Fin T) (v : XV H T)
    (pr : XV H T × XV H T → Prop) [DecidablePred pr] (hpr : ∀ α, pr α → α.1 = v ∨ α.2 = v) :
    ((chan t.1 t.2.1 t.2.2).filter pr).card ≤ if Touches v t then 5 else 0 := by
  split_ifs with h
  · exact (card_filter_le _ _).trans (chan_card_le _ _ _)
  · apply le_of_eq
    rw [card_eq_zero, filter_eq_empty_iff]
    intro α hα hp
    exact h (touches_of_mem hα (hpr α hp))

omit [Fintype H] in
theorem card_touches_le (Q : Finset (H × H)) (q : ℕ)
    (hq : ∀ u, (Q.filter (fun e => e.1 = u ∨ e.2 = u)).card ≤ q) (v : XV H T) :
    ((Q ×ˢ (univ : Finset (Bool × Fin T))).filter (Touches v)).card ≤ 2 * T * q + 1 := by
  rcases v with u | p
  · have : (Q ×ˢ (univ : Finset (Bool × Fin T))).filter (Touches (Sum.inl u)) =
        (Q.filter (fun e => e.1 = u ∨ e.2 = u)) ×ˢ (univ : Finset (Bool × Fin T)) := by
      ext t; simp [Touches, and_comm]
    rw [this, card_product, card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    have := hq u
    calc _ ≤ q * (2 * T) := Nat.mul_le_mul_right _ this
      _ ≤ 2 * T * q + 1 := by rw [mul_comm]; omega
  · calc _ ≤ ({privTok p} : Finset _).card := by
          apply card_le_card
          intro t ht
          simp only [mem_filter, Touches] at ht
          simp [ht.2]
      _ ≤ 2 * T * q + 1 := by simp

end Channels

section Reserve

omit [Fintype H] in
theorem card_reserve_filter_le (Q : Finset (H × H)) (q : ℕ)
    (hq : ∀ u, (Q.filter (fun e => e.1 = u ∨ e.2 = u)).card ≤ q) (v : XV H T)
    (pr : XV H T × XV H T → Prop) [DecidablePred pr] (hpr : ∀ α, pr α → α.1 = v ∨ α.2 = v) :
    ((reserve Q T).filter pr).card ≤ 5 * (2 * T * q + 1) := by
  unfold reserve
  rw [filter_biUnion]
  calc _ ≤ ∑ t ∈ Q ×ˢ (univ : Finset (Bool × Fin T)), ((chan t.1 t.2.1 t.2.2).filter pr).card :=
        card_biUnion_le
    _ ≤ ∑ t ∈ Q ×ˢ (univ : Finset (Bool × Fin T)), if Touches v t then 5 else 0 :=
        Finset.sum_le_sum fun t _ => card_chan_filter_le t v pr hpr
    _ = 5 * ((Q ×ˢ (univ : Finset (Bool × Fin T))).filter (Touches v)).card := by
        rw [← Finset.sum_filter, sum_const, smul_eq_mul, mul_comm]
    _ ≤ 5 * (2 * T * q + 1) := Nat.mul_le_mul_left _ (card_touches_le Q q hq v)

omit [Fintype H] in
theorem card_lift_filter_le (D : Finset (H × H)) (q : ℕ)
    (hq : ∀ u, (D.filter (fun e => e.1 = u ∨ e.2 = u)).card ≤ q) (v : XV H T)
    (pr : XV H T × XV H T → Prop) [DecidablePred pr] (hpr : ∀ α, pr α → α.1 = v ∨ α.2 = v) :
    ((D.map (liftArc H (Priv H T))).filter pr).card ≤ q := by
  rcases v with u | p
  · rw [filter_map, card_map]
    refine le_trans (card_le_card ?_) (hq u)
    intro e he
    simp only [mem_filter, Function.comp] at he ⊢
    refine ⟨he.1, ?_⟩
    rcases hpr _ he.2 with h | h
    · left; exact Sum.inl.inj h
    · right; exact Sum.inl.inj h
  · apply le_of_eq_of_le _ (Nat.zero_le q)
    rw [card_eq_zero, filter_eq_empty_iff]
    intro α hα hp
    obtain ⟨e, -, rfl⟩ := mem_map.mp hα
    rcases hpr _ hp with h | h <;> simp [liftArc] at h

end Reserve

section Mult

variable (Q D : Finset (H × H)) (hT : 0 < T) (face : Φ → Face H)

omit [Fintype H] [DecidableEq Φ] in
theorem card_faceLib_filter_le (m k : ℕ) (hk : ∀ φ, (face φ).supp.card ≤ k)
    (hm : ∀ e, (univ.filter (fun φ => e ∈ (face φ).supp)).card ≤ m) (hT1 : 1 ≤ T)
    (α : XV H T × XV H T) (hα : α ∈ reserve Q T ∪ D.map (liftArc H (Priv H T))) :
    ((faceLib face T).filter (fun P => α ∈ P)).card ≤ 2 * m * T ^ k := by
  classical
  unfold faceLib
  refine (card_filter_image_le _ _ α).trans ?_
  rcases mem_union.mp hα with hα | hα
  · obtain ⟨e0, -, b0, i0, hα0⟩ := mem_reserve.mp hα
    have hsub : (univ : Finset (Σ φ : Φ, Bool × ({e // e ∈ (face φ).supp} → Fin T))).filter
        (fun x => α ∈ facePiece (face x.1) x.2.1 x.2.2) ⊆
        (univ.filter (fun φ => e0 ∈ (face φ).supp)).sigma (fun _ => univ) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      obtain ⟨e, he, hαe⟩ := mem_facePiece.mp hx
      have := chan_eq_of_mem (t := (e0, b0, i0)) (t' := (e, _, _)) hα0 hαe
      simp only [Prod.mk.injEq] at this
      simp only [mem_sigma, mem_filter, mem_univ, true_and, and_true]
      rw [this.1]; exact he
    refine (card_le_card hsub).trans ?_
    rw [card_sigma]
    calc _ ≤ ∑ _φ ∈ univ.filter (fun φ => e0 ∈ (face φ).supp), 2 * T ^ k := by
          apply Finset.sum_le_sum
          intro φ _
          rw [card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_coe]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT1 (hk φ))
      _ = (univ.filter (fun φ => e0 ∈ (face φ).supp)).card * (2 * T ^ k) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ m * (2 * T ^ k) := Nat.mul_le_mul_right _ (hm e0)
      _ = 2 * m * T ^ k := by ring
  · obtain ⟨f, -, rfl⟩ := mem_map.mp hα
    apply le_of_eq_of_le _ (Nat.zero_le _)
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    obtain ⟨e, he, hαe⟩ := mem_facePiece.mp hx
    exact liftArc_not_mem_chan _ _ _ _ hαe

omit [Fintype H] in
theorem card_pairLib_filter_le (α : XV H T × XV H T) :
    ((pairLib Q T).filter (fun P => α ∈ P)).card ≤ T ^ 2 := by
  classical
  unfold pairLib
  refine (card_filter_image_le _ _ α).trans ?_
  by_cases hα : ∃ e b i, α ∈ chan e b i
  · obtain ⟨e0, b0, i0, hα0⟩ := hα
    have hsub : (Q ×ˢ (univ : Finset (Fin T × Fin T))).filter
        (fun x => α ∈ pairPiece x.1 x.2.1 x.2.2) ⊆ {e0} ×ˢ univ := by
      intro x hx
      simp only [mem_filter, pairPiece, mem_union] at hx
      simp only [mem_product, mem_singleton, mem_univ, and_true]
      rcases hx.2 with h | h
      · have := chan_eq_of_mem (t := (e0, b0, i0)) (t' := (x.1, true, x.2.1)) hα0 h
        simp only [Prod.mk.injEq] at this; exact this.1.symm
      · have := chan_eq_of_mem (t := (e0, b0, i0)) (t' := (x.1, false, x.2.2)) hα0 h
        simp only [Prod.mk.injEq] at this; exact this.1.symm
    refine (card_le_card hsub).trans ?_
    simp [sq]
  · apply le_of_eq_of_le _ (Nat.zero_le _)
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    simp only [pairPiece, mem_union] at hx
    rcases hx with h | h
    · exact hα ⟨_, _, _, h⟩
    · exact hα ⟨_, _, _, h⟩

omit [Fintype H] in
theorem card_tailLib_filter_le (α : XV H T × XV H T) :
    ((tailLib D hT).filter (fun P => α ∈ P)).card ≤ 1 := by
  classical
  unfold tailLib
  refine (card_filter_image_le _ _ α).trans ?_
  rw [card_le_one]
  intro e he e' he'
  simp only [mem_filter, tailPiece, mem_insert] at he he'
  rcases he.2 with h | h <;> rcases he'.2 with h' | h'
  · exact (liftArc H (Priv H T)).injective (h.symm.trans h')
  · rw [h] at h'; exact absurd h' (liftArc_not_mem_chan _ _ _ _)
  · rw [h'] at h; exact absurd h (liftArc_not_mem_chan _ _ _ _)
  · have := chan_eq_of_mem (t := (e, false, ⟨0, hT⟩)) (t' := (e', false, ⟨0, hT⟩)) h h'
    simp only [Prod.mk.injEq] at this; exact this.1

end Mult

omit [Fintype H] [DecidableEq Φ] in
/-- **Vertex load of the positive catalogue.** -/
theorem catalogue_load_le (Q D : Finset (H × H)) (hDQ : D ⊆ Q) (hT : 0 < T) (face : Φ → Face H)
    (hsupp : ∀ φ, (face φ).supp ⊆ Q) (k m q : ℕ) (hk : ∀ φ, (face φ).supp.card ≤ k)
    (hm : ∀ e, (univ.filter (fun φ => e ∈ (face φ).supp)).card ≤ m)
    (hq : ∀ u, (Q.filter (fun e => e.1 = u ∨ e.2 = u)).card ≤ q) (v : XV H T) :
    catalogLoad (catalogue face Q D hT) v ≤
      (2 * m * T ^ k + T ^ 2 + 1) * (2 * (5 * (2 * T * q + 1) + q)) := by
  classical
  have hsub : ∀ P ∈ catalogue face Q D hT, P ⊆ reserve Q T ∪ D.map (liftArc H (Priv H T)) := by
    intro P hP
    rcases mem_union.mp hP with hP | hP
    · rcases mem_union.mp hP with hP | hP
      · obtain ⟨x, -, rfl⟩ := mem_image.mp hP
        intro α hα
        obtain ⟨e, he, hαe⟩ := mem_facePiece.mp hα
        exact mem_union_left _ (mem_reserve.mpr ⟨e, hsupp _ he, _, _, hαe⟩)
      · obtain ⟨⟨e, i, j⟩, hx, rfl⟩ := mem_image.mp hP
        have he := (mem_product.mp hx).1
        intro α hα
        rcases mem_union.mp hα with hα | hα
        · exact mem_union_left _ (mem_reserve.mpr ⟨e, he, _, _, hα⟩)
        · exact mem_union_left _ (mem_reserve.mpr ⟨e, he, _, _, hα⟩)
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hP
      intro α hα
      rcases mem_insert.mp hα with rfl | hα
      · exact mem_union_right _ (mem_map_of_mem _ he)
      · exact mem_union_left _ (mem_reserve.mpr ⟨e, hDQ he, _, _, hα⟩)
  have hmult : ∀ α ∈ reserve Q T ∪ D.map (liftArc H (Priv H T)),
      ((catalogue face Q D hT).filter (fun P => α ∈ P)).card ≤ 2 * m * T ^ k + T ^ 2 + 1 := by
    intro α hα
    unfold catalogue
    rw [filter_union, filter_union]
    refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact card_faceLib_filter_le Q D face m k hk hm hT α hα
    · exact card_pairLib_filter_le Q α
    · exact card_tailLib_filter_le D hT α
  have hqD : ∀ u, (D.filter (fun e => e.1 = u ∨ e.2 = u)).card ≤ q :=
    fun u => (card_le_card (filter_subset_filter _ hDQ)).trans (hq u)
  refine (catalogLoad_le_mult _ _ hsub _ hmult v).trans (Nat.mul_le_mul_left _ ?_)
  have h1 : ∀ (pr : XV H T × XV H T → Prop) [DecidablePred pr],
      (∀ α, pr α → α.1 = v ∨ α.2 = v) →
      ((reserve Q T ∪ D.map (liftArc H (Priv H T))).filter pr).card ≤
        5 * (2 * T * q + 1) + q := by
    intro pr _ hpr
    rw [filter_union]
    exact (card_union_le _ _).trans (add_le_add (card_reserve_filter_le Q q hq v pr hpr)
      (card_lift_filter_le D q hqD v pr hpr))
  have h2 := h1 (fun α => α.2 = v) (fun α h => Or.inr h)
  have h3 := h1 (fun α => α.1 = v) (fun α h => Or.inl h)
  omega

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization
