/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Decomp

/-! # Budgets of the certificate absorber

* `absorber_no_old_edge`: no edge of `A` joins two original vertices;
* `card_absorber`: `|A| = 9k + 21k⁻` (hence `≤ 30k`);
* `card_ext`: the extended vertex type has exactly `|W| + 9k` vertices;
* `incidentLoad_absorber`: `incidentLoad A (x) ≤ 4 · occ(x)` for every original `x`.
-/

@[expose] public section

namespace PaperII.CertAbsorber

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection

variable {W : Type*} [DecidableEq W] {t : ℕ}
variable {p : W → Fin t} {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
variable {c : SignedCert p F P}

/-- **No edge of `A` has both endpoints in `W`.** -/
theorem absorber_no_old_edge (M : Matching c) :
    ∀ e ∈ M.absorber, ∀ x y : W, e ≠ s(Sum.inl x, Sum.inl y) := by
  intro e he x y
  obtain ⟨σ, hσ, rfl⟩ := mem_image.mp he
  rcases σ with ⟨s, x'⟩ | ⟨i, m⟩ | ⟨s, κ⟩ | e'
  · simp [Matching.ed, occV]
  · simp [Matching.ed, occV]
  · cases κ <;> simp [Matching.ed, Matching.hEdge, occV, hngV]
  · exact absurd hσ (not_mem_aSlots_pe e')

/-- `A` and the image of `P` are edge-disjoint. -/
theorem absorber_disjoint_P (M : Matching c) :
    Disjoint M.absorber (P.image (Sym2.map Sum.inl)) := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨e', -, rfl⟩ := mem_image.mp he'
  induction e' using Sym2.ind with
  | _ x y => exact absurd rfl (absorber_no_old_edge M _ he x y)

lemma card_occSlots (i : Fin c.k) : (c.occSlots i).card = 9 := by
  unfold SignedCert.occSlots
  rw [card_biUnion]
  · have h3 : ∀ m : Fin 3, ({Slot.wv (i, m) (c.U (i, m)), Slot.wv (i, m) (c.V (i, m)),
        Slot.y i m} : Finset (Slot W c.k)).card = 3 := by
      intro m
      have := c.U_ne_V (i, m)
      rw [card_insert_of_notMem (by simp [this]), card_insert_of_notMem (by simp),
        card_singleton]
    simp [h3]
  · intro m _ m' _ hmm
    simp [disjoint_insert_right, Ne.symm hmm]

lemma card_hSlots (s : Fin c.k × Fin 3) : (c.hSlots s).card = 7 := by
  simp [SignedCert.hSlots]

lemma card_negS : c.negS.card = 3 * c.negCount := by
  have : c.negS = (univ.filter fun i => c.pos i = false) ×ˢ (univ : Finset (Fin 3)) := by
    ext s; simp [SignedCert.negS]
  rw [this, card_product, card_univ, Fintype.card_fin, SignedCert.negCount, mul_comm]

lemma card_aSlots : c.aSlots.card = 9 * c.k + 21 * c.negCount := by
  unfold SignedCert.aSlots
  rw [card_union_of_disjoint, card_biUnion, card_biUnion]
  · simp only [card_occSlots, card_hSlots, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      card_negS]
    ring
  · intro s _ s' _ hss
    simp [Function.onFun, SignedCert.hSlots, disjoint_insert_right, Ne.symm hss]
  · intro i _ i' _ hii
    simp only [Function.onFun, SignedCert.occSlots, disjoint_left, mem_biUnion, mem_univ,
      true_and, mem_insert, mem_singleton, not_exists]
    intro σ ⟨m, hσ⟩ m'
    rcases hσ with rfl | rfl | rfl <;> simp [hii]
  · rw [disjoint_left]
    intro σ hσ hσ'
    simp only [mem_biUnion, SignedCert.occSlots, SignedCert.hSlots, mem_insert,
      mem_singleton, mem_univ, true_and] at hσ hσ'
    obtain ⟨i, m, hσ⟩ := hσ
    obtain ⟨s, -, hσ'⟩ := hσ'
    rcases hσ with rfl | rfl | rfl <;> simp at hσ'

/-- **Exact edge count**: `|A| = 9k + 21k⁻`, where `k⁻` is the number of negative
occurrences. -/
theorem card_absorber (M : Matching c) : M.absorber.card = 9 * c.k + 21 * c.negCount := by
  rw [Matching.absorber, card_image_of_injective _ M.ed_injective, card_aSlots]

/-- **Edge budget** `|A| ≤ 30 k`. -/
theorem card_absorber_le (M : Matching c) : M.absorber.card ≤ 30 * c.k := by
  have h : c.negCount ≤ c.k := by
    unfold SignedCert.negCount
    exact (card_filter_le _ _).trans (by simp)
  rw [card_absorber]; omega

/-- **Vertex budget**: exactly `9k` vertices are added (`3k` occurrence clones and `6k`
hinge clones; only the `6k⁻` hinge clones of negative sides are used by `A`). -/
theorem card_ext [Fintype W] : Fintype.card (Ext W c.k) = Fintype.card W + 9 * c.k := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- **Load budget**: every original vertex `x` meets at most `4 · occ(x)` edges of `A`. -/
theorem incidentLoad_absorber [Fintype W] (M : Matching c) (x : W) :
    incidentLoad M.absorber (Sum.inl x) ≤ 4 * c.occCount x := by
  classical
  let S : Fin c.k → Finset (Slot W c.k) := fun i =>
    (univ.filter fun j => c.vtx i j = x).biUnion fun j =>
      {Slot.wv (i, j + 1) x, Slot.wv (i, j + 2) x, Slot.h (i, j + 2) .ub, Slot.h (i, j + 1) .av}
  have hS : ∀ i, (S i).card ≤ 4 * (if x ∈ univ.image (c.vtx i) then 1 else 0) := by
    intro i
    have hle1 : (univ.filter fun j => c.vtx i j = x).card ≤ 1 :=
      card_le_one.mpr fun a ha b hb => c.inj i ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
    refine (card_biUnion_le).trans ?_
    have h4 : ∀ j, ({Slot.wv (i, j + 1) x, Slot.wv (i, j + 2) x, Slot.h (i, j + 2) .ub,
        Slot.h (i, j + 1) .av} : Finset (Slot W c.k)).card ≤ 4 := fun j =>
      (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
        (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))
    refine (sum_le_sum fun j _ => h4 j).trans ?_
    rw [sum_const, smul_eq_mul]
    split_ifs with hx
    · nlinarith
    · have : (univ.filter fun j => c.vtx i j = x) = ∅ :=
        filter_eq_empty_iff.mpr fun j _ hj => hx (mem_image.mpr ⟨j, mem_univ _, hj⟩)
      simp [this]
  have hsub : c.aSlots.filter (fun σ => Sum.inl x ∈ M.ed σ) ⊆ univ.biUnion S := by
    intro σ hσ
    obtain ⟨hσA, hx⟩ := mem_filter.mp hσ
    simp only [mem_biUnion, mem_univ, true_and, S, mem_filter, mem_insert, mem_singleton]
    rcases σ with ⟨s, x'⟩ | ⟨i, m⟩ | ⟨s, κ⟩ | e
    · rw [mem_aSlots_wv] at hσA
      simp [Matching.ed, occV] at hx
      subst hx
      rcases hσA with h | h
      · exact ⟨s.1, s.2 + 1, h.symm, Or.inr (Or.inl (by simp))⟩
      · exact ⟨s.1, s.2 + 2, h.symm, Or.inl (by simp)⟩
    · simp [Matching.ed, occV] at hx
    · cases κ <;> simp [Matching.ed, Matching.hEdge, occV, hngV] at hx
      · exact ⟨s.1, s.2 + 1, hx.symm, by simp⟩
      · exact ⟨s.1, s.2 + 2, hx.symm, by simp⟩
    · exact absurd hσA (not_mem_aSlots_pe e)
  unfold incidentLoad Matching.absorber
  rw [filter_image]
  refine card_image_le.trans ((card_le_card hsub).trans (card_biUnion_le.trans ?_))
  refine (sum_le_sum fun i _ => hS i).trans ?_
  rw [← mul_sum, SignedCert.occCount, card_filter]

end PaperII.CertAbsorber
