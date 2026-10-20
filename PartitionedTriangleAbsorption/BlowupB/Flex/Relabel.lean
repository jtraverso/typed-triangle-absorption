/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Div
public import PartitionedTriangleAbsorption.TypedCoarseningStage81

@[expose] public section

/-!
# Relabelling the parts along a map `g : Fin t → Fin u`

* `isIntDiv_push`: integral divisibility (Definition 13.5) is pushed forward along ANY label map
  `g` with `τ.map g ∈ F'` for `τ ∈ F` (edge and degree vectors push forward linearly, and so do
  the type vectors: `count_map_int`, `typeEdgeVec_push`, `typeDegVec_push`).
* `isIntDiv_filter`: when every label lies in a component `P` (closed along the types of `F`),
  only the types inside `P` are needed.
* `hasDecomp_relabel`: decompositions are relabelled along `g` when the labels lie in `P` and
  `g` maps the types of `F` inside `P` into `F'`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption

section Push

variable {t u : ℕ} (g : Fin t → Fin u)

theorem count_map_int (τ : Multiset (Fin t)) (a : Fin u) :
    ((τ.map g).count a : ℤ) = ∑ i, (if g i = a then (1 : ℤ) else 0) * (τ.count i : ℤ) := by
  induction τ using Multiset.induction_on with
  | empty => simp
  | cons x τ ih =>
    simp only [Multiset.map_cons, Multiset.count_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, mul_add, sum_add_distrib, ih]
    congr 1
    rw [Fintype.sum_eq_single x (fun i hi => by simp [hi])]
    by_cases h : g x = a
    · simp [h]
    · simp [h, Ne.symm h]

theorem sum_sum_ind2 (a b : Fin u) (x y : Fin t) :
    (∑ i, ∑ j, (if g i = a ∧ g j = b then (1 : ℤ) else 0) * (if x = i ∧ y = j then 1 else 0)) =
      if g x = a ∧ g y = b then 1 else 0 := by
  rw [Fintype.sum_eq_single x, Fintype.sum_eq_single y]
  · simp
  · intro j hj; simp [Ne.symm hj]
  · intro i hi; refine Fintype.sum_eq_zero _ fun j => ?_; simp [Ne.symm hi]

theorem sum_ind1 (a : Fin u) (P : Prop) [Decidable P] (y : Fin t) :
    (∑ i, (if g i = a then (1 : ℤ) else 0) * (if P ∧ y = i then 1 else 0)) =
      if P ∧ g y = a then 1 else 0 := by
  rw [Fintype.sum_eq_single y]
  · by_cases hP : P <;> simp [hP]
  · intro i hi; simp [Ne.symm hi]

theorem typeDegVec_push (τ : Multiset (Fin t)) (r : Fin t) (a : Fin u) :
    typeDegVec (τ.map g) (g r) a =
      ∑ i, (if g i = a then (1 : ℤ) else 0) * typeDegVec τ r i := by
  unfold typeDegVec
  simp only [mul_sub, sum_sub_distrib]
  rw [count_map_int]
  congr 1
  rw [Fintype.sum_eq_single r (fun i hi => by simp [hi])]
  by_cases h : g r = a
  · simp [h]
  · simp [h, Ne.symm h]

theorem typeEdgeVec_push (τ : Multiset (Fin t)) (a b : Fin u) :
    typeEdgeVec (τ.map g) a b =
      ∑ i, ∑ j, (if g i = a ∧ g j = b then (1 : ℤ) else 0) * typeEdgeVec τ i j := by
  have hpt : ∀ i j, (if g i = a ∧ g j = b then (1 : ℤ) else 0) * typeEdgeVec τ i j =
      ((if g i = a then (1 : ℤ) else 0) * (τ.count i : ℤ)) *
        ((if g j = b then (1 : ℤ) else 0) * (τ.count j : ℤ)) -
      if i = j then (if g i = a ∧ g i = b then (τ.count i : ℤ) else 0) else 0 := by
    intro i j
    unfold typeEdgeVec
    by_cases hij : i = j
    · subst hij
      by_cases h1 : g i = a
      · by_cases h2 : g i = b
        · obtain rfl : a = b := h1.symm.trans h2
          simp [h1] <;> ring
        · have hab : ¬ a = b := fun h => h2 (h1.trans h)
          simp [h1, h2, hab]
      · simp [h1]
    · by_cases h1 : g i = a <;> by_cases h2 : g j = b <;> simp [h1, h2, hij]
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => hpt i j]
  simp only [sum_sub_distrib, ← mul_sum, ← sum_mul, sum_ite_eq, mem_univ, if_true]
  unfold typeEdgeVec
  rw [count_map_int, count_map_int]
  congr 1
  by_cases hab : a = b
  · subst hab
    simp only [if_true, and_self]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : g i = a <;> simp [h]
  · rw [if_neg hab]
    refine (Fintype.sum_eq_zero _ fun i => ?_).symm
    by_cases h : g i = a
    · have : ¬ g i = b := fun h' => hab (h.symm.trans h')
      simp [h, this, hab]
    · simp [h]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairVec_push (p : V → Fin t) (e : Sym2 V) (a b : Fin u) :
    pairVec (g ∘ p) e a b =
      ∑ i, ∑ j, (if g i = a ∧ g j = b then (1 : ℤ) else 0) * pairVec p e i j := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [pairVec, Sym2.lift_mk, Function.comp_apply, mul_add, sum_add_distrib]
    rw [sum_sum_ind2 g a b (p x) (p y), sum_sum_ind2 g a b (p y) (p x)]

theorem degContrib_push (p : V → Fin t) (v : V) (e : Sym2 V) (a : Fin u) :
    degContrib (g ∘ p) v e a = ∑ i, (if g i = a then (1 : ℤ) else 0) * degContrib p v e i := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [degContrib, Sym2.lift_mk, Function.comp_apply, mul_add, sum_add_distrib]
    rw [sum_ind1 g a (x = v) (p y), sum_ind1 g a (y = v) (p x)]

/-- **Integral divisibility is pushed forward along a label map.** -/
theorem isIntDiv_push (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (F' : Finset (Multiset (Fin u))) (hmap : ∀ τ ∈ F, τ.map g ∈ F') {L : Finset (Sym2 V)}
    (h : IsIntDiv p F L) : IsIntDiv (g ∘ p) F' L := by
  classical
  obtain ⟨⟨w, hw⟩, hdeg⟩ := h
  refine ⟨⟨fun σ => ∑ τ ∈ F with τ.map g = σ, w τ, ?_⟩, fun v => ?_⟩
  · funext a b
    have hw' : ∀ i j, edgeVec p L i j = ∑ τ ∈ F, w τ * typeEdgeVec τ i j := by
      intro i j
      have := congrFun (congrFun hw i) j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc edgeVec (g ∘ p) L a b
        = ∑ i, ∑ j, (if g i = a ∧ g j = b then (1 : ℤ) else 0) * edgeVec p L i j := by
          simp only [edgeVec, Finset.sum_apply, pairVec_push g p, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [sum_comm]
      _ = ∑ τ ∈ F, w τ * typeEdgeVec (τ.map g) a b := by
          have hij : ∀ i j, (if g i = a ∧ g j = b then (1 : ℤ) else 0) * edgeVec p L i j =
              ∑ τ ∈ F, w τ * ((if g i = a ∧ g j = b then (1 : ℤ) else 0) * typeEdgeVec τ i j) := by
            intro i j
            rw [hw', mul_sum]
            refine sum_congr rfl fun τ _ => ?_
            ring
          simp only [hij, typeEdgeVec_push g, mul_sum]
          simp only [Finset.sum_comm (s := (univ : Finset (Fin t))) (t := F)]
      _ = ∑ σ ∈ F', (∑ τ ∈ F with τ.map g = σ, w τ) * typeEdgeVec σ a b := by
          rw [← sum_fiberwise_of_maps_to (g := fun τ : Multiset (Fin t) => τ.map g) hmap]
          refine sum_congr rfl fun σ _ => ?_
          rw [sum_mul]
          refine sum_congr rfl fun τ hτ => ?_
          rw [(mem_filter.mp hτ).2]
  · obtain ⟨wv, hwv⟩ := hdeg v
    refine ⟨fun σ => ∑ τ ∈ F with p v ∈ τ ∧ τ.map g = σ, wv τ, ?_⟩
    funext a
    have hwv' : ∀ i, degVec p L v i = ∑ τ ∈ F with p v ∈ τ, wv τ * typeDegVec τ (p v) i := by
      intro i
      have := congrFun hwv i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hmaps : ∀ τ ∈ F.filter (fun τ => p v ∈ τ),
        τ.map g ∈ F'.filter (fun σ => (g ∘ p) v ∈ σ) := by
      intro τ hτ
      obtain ⟨hτF, hpv⟩ := mem_filter.mp hτ
      exact mem_filter.mpr ⟨hmap τ hτF, Multiset.mem_map_of_mem g hpv⟩
    calc degVec (g ∘ p) L v a
        = ∑ i, (if g i = a then (1 : ℤ) else 0) * degVec p L v i := by
          simp only [degVec, Finset.sum_apply, degContrib_push g p, mul_sum]
          rw [sum_comm]
      _ = ∑ τ ∈ F with p v ∈ τ, wv τ * typeDegVec (τ.map g) (g (p v)) a := by
          simp only [hwv', mul_sum, typeDegVec_push g]
          rw [sum_comm]
          refine sum_congr rfl fun τ _ => ?_
          refine sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ σ ∈ F' with (g ∘ p) v ∈ σ,
            (∑ τ ∈ F with p v ∈ τ ∧ τ.map g = σ, wv τ) * typeDegVec σ ((g ∘ p) v) a := by
          rw [← sum_fiberwise_of_maps_to (g := fun τ : Multiset (Fin t) => τ.map g) hmaps]
          refine sum_congr rfl fun σ _ => ?_
          rw [sum_mul, filter_filter]
          refine sum_congr rfl fun τ hτ => ?_
          rw [(mem_filter.mp hτ).2.2]
          rfl

end Push

section Filter

variable {t u : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem typeEdgeVec_eq_zero_of_count {τ : Multiset (Fin t)} {i : Fin t} (hi : τ.count i = 0)
    (j : Fin t) : typeEdgeVec τ i j = 0 := by
  unfold typeEdgeVec; simp [hi]

theorem edgeVec_eq_zero_of_label (p : V → Fin t) (L : Finset (Sym2 V)) {i : Fin t}
    (hi : ∀ v, p v ≠ i) (j : Fin t) : edgeVec p L i j = 0 := by
  unfold edgeVec
  rw [Finset.sum_apply, Finset.sum_apply]
  refine sum_eq_zero fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y => simp [pairVec, hi]

/-- **Only the types inside the label component are needed.** -/
theorem isIntDiv_filter (p : V → Fin t) (P : Fin t → Prop) [DecidablePred P]
    (hp : ∀ v, P (p v)) (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, ∀ i ∈ τ, P i → ∀ j ∈ τ, P j) {L : Finset (Sym2 V)}
    (h : IsIntDiv p F L) : IsIntDiv p (F.filter fun τ => ∀ i ∈ τ, P i) L := by
  classical
  obtain ⟨⟨w, hw⟩, hdeg⟩ := h
  refine ⟨⟨w, ?_⟩, fun v => ?_⟩
  · funext i j
    have hw' := congrFun (congrFun hw i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw' ⊢
    by_cases hi : P i
    · rw [hw']
      refine (sum_filter_of_ne fun τ hτ hne => ?_).symm
      have hc : τ.count i ≠ 0 := fun hc => hne (by rw [typeEdgeVec_eq_zero_of_count hc, mul_zero])
      exact hF τ hτ i (Multiset.count_ne_zero.mp hc) hi
    · rw [edgeVec_eq_zero_of_label p L (i := i) (fun v hv => hi (hv ▸ hp v)) j]
      refine (sum_eq_zero fun τ hτ => ?_).symm
      have hc : τ.count i = 0 :=
        Multiset.count_eq_zero.mpr fun hmem => hi ((mem_filter.mp hτ).2 i hmem)
      rw [typeEdgeVec_eq_zero_of_count hc, mul_zero]
  · obtain ⟨wv, hwv⟩ := hdeg v
    refine ⟨wv, ?_⟩
    rw [hwv, filter_filter]
    congr 1
    ext τ
    simp only [mem_filter]
    constructor
    · rintro ⟨hτ, hpv⟩
      exact ⟨hτ, hF τ hτ (p v) hpv (hp v), hpv⟩
    · rintro ⟨hτ, -, hpv⟩
      exact ⟨hτ, hpv⟩

/-- **Decompositions are relabelled inside a label component.** -/
theorem hasDecomp_relabel (p : V → Fin t) (g : Fin t → Fin u) (P : Fin t → Prop)
    (hp : ∀ v, P (p v)) (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, (∀ i ∈ τ, P i) → τ.map g ∈ F') {E : Finset (Sym2 V)}
    (h : HasDecomp p F E) : HasDecomp (g ∘ p) F' E := by
  obtain ⟨D, hT, hP, hU⟩ := h
  refine ⟨D, fun s hs => ⟨(hT s hs).1, ?_⟩, hP, hU⟩
  have := hmap _ (hT s hs).2 (fun i hi => by
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hi
    exact hp v)
  simpa only [Multiset.map_map] using this

end Filter

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.isIntDiv_push
#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.isIntDiv_filter
#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.hasDecomp_relabel
