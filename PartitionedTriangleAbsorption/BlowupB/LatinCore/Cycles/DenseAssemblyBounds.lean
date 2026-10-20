/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseReduction

@[expose] public section

/-! Shared construction bounds, separated to avoid an import cycle with the old-vertex load estimate. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace DenseRed

open Hub (ne_of_cyc deg_biUnion)
open MesoCutHub (dPairs deg_mono deg_union_le sum_union_le' sum_image_le'
  sum_filter_prod_fst_le sum_filter_prod_snd_le outDeg_le_of_maxDeg inDeg_le_of_maxDeg
  card_dPairs_le MesoscopicFor load_sq_le)

section Assembly

variable {V P U' : Type} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
  [Fintype U'] [DecidableEq U'] (p : V → P)

omit [Fintype V] [Fintype P] [Fintype U'] in
lemma tcol_ι (c : V → ZMod 3) (col : P → ZMod 3) (cU : U' → ZMod 3) (y : P ⊕ U') :
    tcol c col cU (ι y) = Sum.elim col cU y := by
  rcases y with a | u <;> rfl

omit [Fintype V] [Fintype P] [Fintype U'] in
lemma deg_Tcyc_le' (e : V × V) (w : TV V P U') :
    deg (Tcyc (P := P) (U' := U') e) w ≤
      deg (Ccyc p e) w + deg {((old e.1, old e.2) : TV V P U' × TV V P U')} w := by
  have hsub : Tcyc (P := P) (U' := U') e ⊆ Ccyc p e ∪ {((old e.1, old e.2) : TV V P U' × TV V P U')} := by
    intro a ha
    simp only [Tcyc, Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ ((mem_Ccyc p).2 (Or.inl ha))
  exact (deg_mono hsub w).trans (deg_union_le _ _ w)

omit [Fintype V] [Fintype P] [Fintype U'] in
lemma deg_Dcyc_le' (e f : V × V) (w : TV V P U') :
    deg (Dcyc (U' := U') p e f) w ≤ deg (Ccyc p e) w + deg (Ccyc p f) w := by
  have hsub : Dcyc (U' := U') p e f ⊆ Ccyc p e ∪ Ccyc p f := by
    intro a ha
    simp only [Dcyc, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact Finset.mem_union_left _ ((mem_Ccyc p).2 (Or.inr (Or.inr (Or.inr ha))))
    · exact Finset.mem_union_right _ ((mem_Ccyc p).2 (Or.inr (Or.inl ha)))
  exact (deg_mono hsub w).trans (deg_union_le _ _ w)

omit [Fintype V] [Fintype P] [Fintype U'] in
lemma sum_deg_single_lift' (Y : Finset (V × V)) (w : TV V P U') :
    ∑ e ∈ Y, deg {((old e.1, old e.2) : TV V P U' × TV V P U')} w =
      deg (Y.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U')))) w := by
  have hY : Y.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U'))) =
      Y.biUnion (fun e => {((old e.1, old e.2) : TV V P U' × TV V P U')}) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_biUnion, Finset.mem_singleton, liftArc,
      Function.Embedding.coeFn_mk, old]
    exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩
  rw [hY, deg_biUnion]
  intro i _ j _ hij
  rw [Finset.disjoint_singleton]
  intro h
  simp only [old, Prod.mk.injEq, Sum.inl.injEq] at h
  exact hij (Prod.ext h.1 h.2)

/-- The first-level count at a vertex: the number of basal pieces through `w`. -/
lemma count_basal_le (c : V → ZMod 3) {Y : Finset (V × V)} (hdeg : MaxDegLE Y 17)
    (w : TV V P U') :
    (Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e))).card ≤
      17 + (match w with
        | Sum.inr (Sum.inl a) => (Y.filter (fun e => p e.1 = a ∨ p e.2 = a)).card
        | _ => 0) := by
  rcases w with v | a | x | u
  · have hsub : Y.filter (fun e => (Sum.inl v : TV V P U') ∈ Set.range (f9 (U' := U') p e)) ⊆
        Y.filter (fun e => e.2 = v) ∪ Y.filter (fun e => e.1 = v) := by
      intro e he
      obtain ⟨he, hw⟩ := Finset.mem_filter.1 he
      rcases mem_range_f9 p hw with h | h | h | h | ⟨k, h⟩ <;>
        simp [old, hub, pv] at h
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, h.symm⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h.symm⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h17 := hdeg v
    unfold deg inDeg outDeg at h17
    exact le_trans (show _ ≤ 17 by change _ ≤ 17 at *; omega) (Nat.le_add_right _ _)
  · have hsub : Y.filter (fun e => (hub a : TV V P U') ∈ Set.range (f9 (U' := U') p e)) ⊆
        Y.filter (fun e => p e.1 = a ∨ p e.2 = a) := by
      intro e he
      obtain ⟨he, hw⟩ := Finset.mem_filter.1 he
      refine Finset.mem_filter.2 ⟨he, ?_⟩
      rcases mem_range_f9 p hw with h | h | h | h | ⟨k, h⟩ <;>
        simp [old, hub, pv] at h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    exact (Finset.card_le_card hsub).trans (Nat.le_add_left _ _)
  · have hsub : Y.filter (fun e => (Sum.inr (Sum.inr (Sum.inl x)) : TV V P U') ∈
        Set.range (f9 (U' := U') p e)) ⊆ {x.1} := by
      intro e he
      obtain ⟨he, hw⟩ := Finset.mem_filter.1 he
      rcases mem_range_f9 p hw with h | h | h | h | ⟨k, h⟩ <;>
        simp [old, hub, pv] at h
      rw [Finset.mem_singleton]
      rcases x with ⟨e', k'⟩
      simp only [Prod.mk.injEq] at h
      exact h.1.symm
    have := (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
    simp only; omega
  · have : Y.filter (fun e => (Sum.inr (Sum.inr (Sum.inr u)) : TV V P U') ∈
        Set.range (f9 (U' := U') p e)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e _ hw
      rcases mem_range_f9 p hw with h | h | h | h | ⟨k, h⟩ <;> simp [old, hub, pv] at h
    rw [this]; simp

end Assembly

end DenseRed

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
