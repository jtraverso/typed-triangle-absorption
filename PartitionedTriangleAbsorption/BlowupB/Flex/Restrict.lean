/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.Relabel
public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.ComponentsT

@[expose] public section

/-!
# Restricting a family to one component

* `isIntDiv_restrict`: an `F`-divisible edge set inside component `k` is divisible for the family
  `K ⊆ F` of the types inside `k` (every type of `F` lies in one component).
* `hasDecomp_mono`: decompositions for a subfamily are decompositions for the family.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem hasDecomp_mono (p : V → Fin t) {K F : Finset (Multiset (Fin t))} (h : K ⊆ F)
    {E : Finset (Sym2 V)} (hE : HasDecomp p K E) : HasDecomp p F E := by
  obtain ⟨D, hT, hP, hU⟩ := hE
  exact ⟨D, fun s hs => ⟨(hT s hs).1, h (hT s hs).2⟩, hP, hU⟩

theorem edgeVec_zero_outside (p : V → Fin t) (c : Fin t → Fin t) (k : Fin t) (L : Finset (Sym2 V))
    (hL : ∀ e ∈ L, CompT.InsideE p c k e) (i j : Fin t) (hij : c i ≠ k ∨ c j ≠ k) :
    edgeVec p L i j = 0 := by
  unfold edgeVec
  rw [Finset.sum_apply, Finset.sum_apply]
  refine sum_eq_zero fun e he => ?_
  have h := hL e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb⟩ := (CompT.insideE_mk p c k a b).mp h
    simp only [pairVec, Sym2.lift_mk]
    rcases hij with hi | hj
    · have h1 : p a ≠ i := fun e => hi (e ▸ ha)
      have h2 : p b ≠ i := fun e => hi (e ▸ hb)
      simp [h1, h2]
    · have h1 : p b ≠ j := fun e => hj (e ▸ hb)
      have h2 : p a ≠ j := fun e => hj (e ▸ ha)
      simp [h1, h2]

theorem degVec_zero_outside (p : V → Fin t) (c : Fin t → Fin t) (k : Fin t) (L : Finset (Sym2 V))
    (hL : ∀ e ∈ L, CompT.InsideE p c k e) (v : V) (hv : c (p v) ≠ k) : degVec p L v = 0 := by
  funext j
  unfold degVec
  rw [Finset.sum_apply]
  refine sum_eq_zero fun e he => ?_
  have h := hL e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb⟩ := (CompT.insideE_mk p c k a b).mp h
    simp only [degContrib, Sym2.lift_mk]
    have h1 : a ≠ v := fun e => hv (e ▸ ha)
    have h2 : b ≠ v := fun e => hv (e ▸ hb)
    simp [h1, h2]

/-- **Divisibility restricts to the family of a component.** -/
theorem isIntDiv_restrict (p : V → Fin t) (F K : Finset (Multiset (Fin t))) (c : Fin t → Fin t)
    (k : Fin t) (hτ : CompT.TypesInside F c) (hKsub : K ⊆ F)
    (hKin : ∀ τ ∈ K, ∀ i ∈ τ, c i = k) (hKall : ∀ τ ∈ F, (∀ i ∈ τ, c i = k) → τ ∈ K)
    (L : Finset (Sym2 V)) (hL : ∀ e ∈ L, CompT.InsideE p c k e) (h : IsIntDiv p F L) :
    IsIntDiv p K L := by
  classical
  obtain ⟨⟨w, hw⟩, hdeg⟩ := h
  -- a type of `F` meeting component `k` lies in `K`
  have hmeet : ∀ τ ∈ F, ∀ i ∈ τ, c i = k → τ ∈ K := by
    intro τ hτF i hi hik
    refine hKall τ hτF fun j hj => ?_
    rw [← hik]
    exact hτ τ hτF j i (Multiset.count_pos.mpr hj) (Multiset.count_pos.mpr hi)
  refine ⟨⟨w, ?_⟩, fun v => ?_⟩
  · funext i j
    have hw' := congrFun (congrFun hw i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw' ⊢
    by_cases hij : c i = k ∧ c j = k
    · rw [hw']
      symm
      refine sum_subset hKsub fun τ hτF hτK => ?_
      have hci : τ.count i = 0 := Multiset.count_eq_zero.mpr fun hi => hτK (hmeet τ hτF i hi hij.1)
      rw [typeEdgeVec_eq_zero_of_count hci, mul_zero]
    · have h0 : c i ≠ k ∨ c j ≠ k := by tauto
      rw [edgeVec_zero_outside p c k L hL i j h0]
      refine (sum_eq_zero fun τ hτ => ?_).symm
      rcases h0 with hi | hj
      · have : τ.count i = 0 := Multiset.count_eq_zero.mpr fun hm => hi (hKin τ hτ i hm)
        rw [typeEdgeVec_eq_zero_of_count this, mul_zero]
      · have : τ.count j = 0 := Multiset.count_eq_zero.mpr fun hm => hj (hKin τ hτ j hm)
        have hz : typeEdgeVec τ i j = 0 := by
          unfold typeEdgeVec
          by_cases h : i = j
          · subst h; simp [this]
          · simp [this, h]
        rw [hz, mul_zero]
  · by_cases hv : c (p v) = k
    · obtain ⟨wv, hwv⟩ := hdeg v
      refine ⟨wv, ?_⟩
      rw [hwv]
      congr 1
      ext τ
      simp only [mem_filter]
      constructor
      · rintro ⟨hτF, hpv⟩
        exact ⟨hmeet τ hτF (p v) hpv hv, hpv⟩
      · rintro ⟨hτK, hpv⟩
        exact ⟨hKsub hτK, hpv⟩
    · refine ⟨0, ?_⟩
      rw [degVec_zero_outside p c k L hL v hv]
      simp

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.isIntDiv_restrict
