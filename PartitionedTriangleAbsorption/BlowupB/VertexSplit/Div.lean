/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Basic

@[expose] public section

/-!
# Vertex splitting: integral divisibility is transported (Lemma 3, `⇒`)

`isIntDiv_split`: if `E` is `F`-divisible (Definition 13.5) then the split edge set `φ(E)` is
`F'`-divisible, given the finite compatibility `S.Compat` of `sig` with the two counting maps
`M(x)(i',j') = ∑_{i,j} [cls i j = i' ∧ cls j i = j'] x(i,j)` (edge vectors) and
`N_j(d)(j') = ∑_s [cls r s = j ∧ cls s r = j'] d(s)` (degree vectors at a copy of class `j`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.VertexSplit

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer

variable {t t' : ℕ} {F : Finset (Multiset (Fin t))} (S : SplitData F t')
variable {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin t)

/-- `∑_{i,j} [C i j] · [a = i ∧ b = j] = [C a b]`. -/
theorem sum_sum_ind (C : Fin t → Fin t → Prop) [DecidableRel C] (a b : Fin t) :
    (∑ i, ∑ j, (if C i j then (1 : ℤ) else 0) * (if a = i ∧ b = j then 1 else 0)) =
      if C a b then 1 else 0 := by
  rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp
  · intro j hj; simp [Ne.symm hj]
  · intro i hi; refine Fintype.sum_eq_zero _ fun j => ?_; simp [Ne.symm hi]

theorem pairVec_splitEdge (e : Sym2 V) (i' j' : Fin t') :
    pairVec (sp S p) (splitEdge S p e) i' j' =
      ∑ i, ∑ j, (if S.cls' i j = i' ∧ S.cls' j i = j' then (1 : ℤ) else 0) * pairVec p e i j := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [splitEdge_mk, pairVec, Sym2.lift_mk, sp_cp, SplitData.cls, mul_add, sum_add_distrib]
    rw [sum_sum_ind (fun i j => S.cls' i j = i' ∧ S.cls' j i = j') (p u) (p v),
      sum_sum_ind (fun i j => S.cls' i j = i' ∧ S.cls' j i = j') (p v) (p u)]
    rfl

theorem edgeVec_splitE (E : Finset (Sym2 V)) (i' j' : Fin t') :
    edgeVec (sp S p) (splitE S p E) i' j' =
      ∑ i, ∑ j, (if S.cls' i j = i' ∧ S.cls' j i = j' then (1 : ℤ) else 0) * edgeVec p E i j := by
  unfold edgeVec splitE
  rw [sum_image fun _ _ _ _ h => splitEdge_injective S p h]
  simp only [sum_apply, pairVec_splitEdge, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]

theorem cp_eq_iff (u : V) (s : Fin t) (x : SV S p) :
    cp S p u s = x ↔ u = fstV S p x ∧ S.cls' (p u) s = sp S p x := by
  obtain ⟨⟨v, j⟩, hx⟩ := x
  constructor
  · intro h
    have h' := congrArg (fun y : SV S p => y.1) h
    simp only [cp, Prod.mk.injEq] at h'
    exact ⟨h'.1, h'.2⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    simp only [cp, fstV, sp] at h1 h2 ⊢
    subst h1
    show (u, S.cls' (p u) s) = (u, j)
    rw [h2]

theorem degContrib_splitEdge (x : SV S p) (e : Sym2 V) (j' : Fin t') :
    degContrib (sp S p) x (splitEdge S p e) j' =
      ∑ s, (if S.cls' (p (fstV S p x)) s = sp S p x ∧ S.cls' s (p (fstV S p x)) = j'
        then (1 : ℤ) else 0) * degContrib p (fstV S p x) e s := by
  induction e using Sym2.ind with
  | _ u w =>
    simp only [splitEdge_mk, degContrib, Sym2.lift_mk, sp_cp, SplitData.cls, mul_add,
      sum_add_distrib, cp_eq_iff]
    congr 1
    · by_cases hu : u = fstV S p x
      · subst hu
        rw [Fintype.sum_eq_single (p w)]
        · simp
        · intro s hs; simp [Ne.symm hs]
      · simp [hu]
    · by_cases hw : w = fstV S p x
      · subst hw
        rw [Fintype.sum_eq_single (p u)]
        · simp
        · intro s hs; simp [Ne.symm hs]
      · simp [hw]

theorem degVec_splitE (E : Finset (Sym2 V)) (x : SV S p) (j' : Fin t') :
    degVec (sp S p) (splitE S p E) x j' =
      ∑ s, (if S.cls' (p (fstV S p x)) s = sp S p x ∧ S.cls' s (p (fstV S p x)) = j'
        then (1 : ℤ) else 0) * degVec p E (fstV S p x) s := by
  unfold degVec splitE
  rw [sum_image fun _ _ _ _ h => splitEdge_injective S p h]
  simp only [sum_apply, degContrib_splitEdge, mul_sum]
  rw [sum_comm]

theorem p_fstV' (x : SV S p) : p (fstV S p x) = S.π (sp S p x) := by
  obtain ⟨⟨v, j⟩, s, hs⟩ := x
  simp only [fstV, sp] at hs ⊢
  rw [hs, S.π_cls]

/-- **Integral divisibility is transported to the split side.** -/
theorem isIntDiv_split (hC : S.Compat) {E : Finset (Sym2 V)} (h : IsIntDiv p F E) :
    IsIntDiv (sp S p) S.F' (splitE S p E) := by
  classical
  obtain ⟨⟨c, hc⟩, hdeg⟩ := h
  refine ⟨⟨fun τ' => ∑ τ ∈ F with S.sig τ = τ', c τ, ?_⟩, fun x => ?_⟩
  · funext i' j'
    rw [edgeVec_splitE, hc]
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    calc ∑ i, ∑ j, ∑ τ ∈ F, (if S.cls' i j = i' ∧ S.cls' j i = j' then (1 : ℤ) else 0) *
          (c τ * typeEdgeVec τ i j)
        = ∑ τ ∈ F, c τ * typeEdgeVec (S.sig τ) i' j' := by
          have hsw : ∀ i : Fin t, (∑ j, ∑ τ ∈ F,
              (if S.cls' i j = i' ∧ S.cls' j i = j' then (1 : ℤ) else 0) * (c τ * typeEdgeVec τ i j)) =
              ∑ τ ∈ F, ∑ j, (if S.cls' i j = i' ∧ S.cls' j i = j' then (1 : ℤ) else 0) *
                (c τ * typeEdgeVec τ i j) := fun i => sum_comm
          rw [sum_congr rfl fun i _ => hsw i, sum_comm]
          refine sum_congr rfl fun τ hτ => ?_
          rw [hC.edge τ hτ i' j', mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ = ∑ τ' ∈ S.F', ∑ τ ∈ F with S.sig τ = τ', c τ * typeEdgeVec τ' i' j' := by
          rw [← sum_fiberwise_of_maps_to (g := S.sig) (fun τ hτ => S.sig_mem τ hτ)]
          refine sum_congr rfl fun τ' _ => sum_congr rfl fun τ hτ => ?_
          rw [(mem_filter.mp hτ).2]
      _ = _ := by
          refine sum_congr rfl fun τ' _ => ?_
          rw [sum_mul]
  · set v := fstV S p x
    set r := p v
    set j := sp S p x
    have hπ : S.π j = r := (p_fstV' S p x).symm
    obtain ⟨cv, hcv⟩ := hdeg v
    refine ⟨fun τ' => ∑ τ ∈ F with r ∈ τ ∧ S.sig τ = τ', cv τ, ?_⟩
    funext j'
    rw [degVec_splitE, hcv]
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    calc ∑ s, ∑ τ ∈ F with r ∈ τ, (if S.cls' r s = j ∧ S.cls' s r = j' then (1 : ℤ) else 0) *
          (cv τ * typeDegVec τ r s)
        = ∑ τ ∈ F with r ∈ τ, cv τ * (if j ∈ S.sig τ then typeDegVec (S.sig τ) j j' else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun τ hτ => ?_
          obtain ⟨hτF, hrτ⟩ := mem_filter.mp hτ
          rw [← hC.deg τ hτF r hrτ j j' hπ, mul_sum]
          exact sum_congr rfl fun s _ => by ring
      _ = ∑ τ ∈ (F.filter fun τ => r ∈ τ).filter (fun τ => j ∈ S.sig τ),
            cv τ * typeDegVec (S.sig τ) j j' := by
          rw [sum_filter (s := F.filter fun τ => r ∈ τ) (p := fun τ => j ∈ S.sig τ)]
          refine sum_congr rfl fun τ _ => ?_
          split_ifs <;> simp
      _ = ∑ τ' ∈ S.F' with j ∈ τ', ∑ τ ∈ F with r ∈ τ ∧ S.sig τ = τ',
            cv τ * typeDegVec τ' j j' := by
          rw [← sum_fiberwise_of_maps_to (s := (F.filter fun τ => r ∈ τ).filter (fun τ => j ∈ S.sig τ))
            (t := S.F'.filter fun τ' => j ∈ τ') (g := S.sig) (fun τ hτ => by
              simp only [mem_filter] at hτ ⊢
              exact ⟨S.sig_mem τ hτ.1.1, hτ.2⟩)]
          refine sum_congr rfl fun τ' hτ' => ?_
          have hjτ' := (mem_filter.mp hτ').2
          refine sum_congr ?_ fun τ hτ => ?_
          · ext τ
            simp only [mem_filter]
            constructor
            · rintro ⟨⟨⟨h1, h2⟩, _⟩, h4⟩
              exact ⟨h1, h2, h4⟩
            · rintro ⟨h1, h2, h4⟩
              exact ⟨⟨⟨h1, h2⟩, h4 ▸ hjτ'⟩, h4⟩
          · rw [(mem_filter.mp hτ).2.2]
      _ = _ := by
          refine sum_congr rfl fun τ' _ => ?_
          rw [sum_mul]

end PartitionedTriangleAbsorption.BlowupB.VertexSplit

#print axioms PartitionedTriangleAbsorption.BlowupB.VertexSplit.isIntDiv_split
