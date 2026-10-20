/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.KeevashPadded

@[expose] public section

/-! Generic invariance under relabelling. Application corollaries are in
`KeevashPermApplications`; importing this module does not import that adapter. -/

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks

section Perm

variable {t : ℕ} (σ : Equiv.Perm (Fin t))

/-- The relabelled family. -/
def permFam (F : Finset (Multiset (Fin t))) : Finset (Multiset (Fin t)) :=
  F.map ⟨Multiset.map σ, Multiset.map_injective σ.injective⟩

theorem mem_permFam {F : Finset (Multiset (Fin t))} {τ : Multiset (Fin t)} :
    τ.map σ ∈ permFam σ F ↔ τ ∈ F :=
  Finset.mem_map' _

theorem exists_of_mem_permFam {F : Finset (Multiset (Fin t))} {τ' : Multiset (Fin t)}
    (h : τ' ∈ permFam σ F) : ∃ τ ∈ F, τ' = τ.map σ := by
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_map.mp h
  exact ⟨τ, hτ, rfl⟩

theorem count_perm (τ : Multiset (Fin t)) (c : Fin t) : (τ.map σ).count (σ c) = τ.count c :=
  Multiset.count_map_eq_count' _ _ σ.injective c

theorem typeEdgeVec_perm (τ : Multiset (Fin t)) (i j : Fin t) :
    typeEdgeVec (τ.map σ) (σ i) (σ j) = typeEdgeVec τ i j := by
  unfold typeEdgeVec
  simp only [count_perm, σ.injective.eq_iff]

theorem typeDegVec_perm (τ : Multiset (Fin t)) (a i : Fin t) :
    typeDegVec (τ.map σ) (σ a) (σ i) = typeDegVec τ a i := by
  unfold typeDegVec
  simp only [count_perm, σ.injective.eq_iff]

theorem map_symm_map (τ : Multiset (Fin t)) : (τ.map σ).map σ.symm = τ := by
  rw [Multiset.map_map]
  simp

theorem allowed_perm {F : Finset (Multiset (Fin t))} {a b : Fin t}
    (h : AllowedPair (permFam σ F) a b) : AllowedPair F (σ.symm a) (σ.symm b) := by
  obtain ⟨τ', hτ', hc, hle⟩ := h
  obtain ⟨τ, hτ, rfl⟩ := exists_of_mem_permFam σ hτ'
  refine ⟨τ, hτ, by simpa using hc, ?_⟩
  have := Multiset.map_le_map (f := σ.symm) hle
  rw [map_symm_map] at this
  simpa using this

theorem allowed_perm' {F : Finset (Multiset (Fin t))} {a b : Fin t}
    (h : AllowedPair F a b) : AllowedPair (permFam σ F) (σ a) (σ b) := by
  obtain ⟨τ, hτ, hc, hle⟩ := h
  refine ⟨τ.map σ, (mem_permFam σ).mpr hτ, by simpa using hc, ?_⟩
  have := Multiset.map_le_map (f := σ) hle
  simpa using this

variable {V : Type*} [DecidableEq V]

theorem pairVec_perm (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    pairVec (σ.symm ∘ p) e i j = pairVec p e (σ i) (σ j) := by
  induction e using Sym2.ind with
  | _ u v => simp [pairVec, Equiv.symm_apply_eq]

theorem degContrib_perm (p : V → Fin t) (v : V) (e : Sym2 V) (i : Fin t) :
    degContrib (σ.symm ∘ p) v e i = degContrib p v e (σ i) := by
  induction e using Sym2.ind with
  | _ a b => simp [degContrib, Equiv.symm_apply_eq]

theorem edgeVec_perm (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec (σ.symm ∘ p) E i j = edgeVec p E (σ i) (σ j) := by
  unfold edgeVec
  simp only [Finset.sum_apply, pairVec_perm]

theorem degVec_perm (p : V → Fin t) (E : Finset (Sym2 V)) (v : V) (i : Fin t) :
    degVec (σ.symm ∘ p) E v i = degVec p E v (σ i) := by
  unfold degVec
  simp only [Finset.sum_apply, degContrib_perm]

theorem isIntDiv_perm {p : V → Fin t} {F : Finset (Multiset (Fin t))} {E : Finset (Sym2 V)}
    (h : IsIntDiv p (permFam σ F) E) : IsIntDiv (σ.symm ∘ p) F E := by
  obtain ⟨⟨c, hc⟩, hdeg⟩ := h
  refine ⟨⟨fun τ => c (τ.map σ), ?_⟩, fun v => ?_⟩
  · funext i j
    rw [edgeVec_perm, hc]
    unfold permFam
    rw [sum_map]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.Embedding.coeFn_mk,
      typeEdgeVec_perm]
  · obtain ⟨c', hc'⟩ := hdeg v
    refine ⟨fun τ => c' (τ.map σ), ?_⟩
    funext i
    have hpv : p v = σ ((σ.symm ∘ p) v) := by simp
    rw [degVec_perm, hc']
    unfold permFam
    rw [filter_map, sum_map]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.Embedding.coeFn_mk,
      Function.comp_apply]
    rw [hpv]
    simp only [typeDegVec_perm, Multiset.mem_map_of_injective σ.injective,
      Equiv.symm_apply_apply]

theorem hasDecomp_perm {p : V → Fin t} {F : Finset (Multiset (Fin t))} {E : Finset (Sym2 V)}
    (h : HasDecomp (σ.symm ∘ p) F E) : HasDecomp p (permFam σ F) E := by
  obtain ⟨D, hT, hP, hU⟩ := h
  refine ⟨D, fun s hs => ⟨(hT s hs).1, ?_⟩, hP, hU⟩
  have h2 := (hT s hs).2
  have heq : s.val.map p = (s.val.map (σ.symm ∘ p)).map σ := by
    rw [Multiset.map_map]
    simp
  rw [heq]
  exact (mem_permFam σ).mpr h2

theorem classCard_perm [Fintype V] (p : V → Fin t) (i : Fin t) :
    (univ.filter fun v => (σ.symm ∘ p) v = i).card = (univ.filter fun v => p v = σ i).card := by
  congr 1
  ext v
  simp [Equiv.symm_apply_eq]

/-! ### Padded copies -/

/-- The position relabelling `(c, j) ↦ (σ c, j)`. -/
def sigP (m : ℕ) : PosT t m ≃ PosT t m := Equiv.prodCongr σ (Equiv.refl _)

theorem sigP_apply (m : ℕ) (x : PosT t m) : sigP σ m x = (σ x.1, x.2) := rfl

theorem patPosT_perm (m : ℕ) (τ : Multiset (Fin t)) :
    (patPosT m τ).image (sigP σ m) = patPosT m (τ.map σ) := by
  ext y
  obtain ⟨x, rfl⟩ := (sigP σ m).surjective y
  rw [(sigP σ m).injective.mem_finset_image]
  simp only [patPosT, mem_filter, mem_univ, true_and, sigP_apply, count_perm]

theorem copyTriT_perm (m : ℕ) (τ : Multiset (Fin t)) (φ : PosT t m → V) :
    copyTriT m τ (φ ∘ sigP σ m) = copyTriT m (τ.map σ) φ := by
  unfold copyTriT
  rw [← patPosT_perm, image_image]

theorem isEmb_perm (m : ℕ) (p : V → Fin t) (φ : PosT t m → V) :
    IsEmbT m (σ.symm ∘ p) (φ ∘ sigP σ m) ↔ IsEmbT m p φ := by
  unfold IsEmbT
  rw [EquivLike.injective_comp]
  refine and_congr_right fun _ => ⟨fun h y => ?_, fun h x => ?_⟩
  · obtain ⟨x, rfl⟩ := (sigP σ m).surjective y
    have := h x
    simp only [Function.comp_apply, Equiv.symm_apply_eq] at this
    rw [this, sigP_apply]
  · simp only [Function.comp_apply, Equiv.symm_apply_eq, h, sigP_apply]

theorem validCopy_perm (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V)) (τ : Multiset (Fin t))
    (φ : PosT t m → V) :
    ValidCopyT m (σ.symm ∘ p) J τ (φ ∘ sigP σ m) ↔ ValidCopyT m p J (τ.map σ) φ := by
  unfold ValidCopyT
  rw [isEmb_perm, copyTriT_perm]

theorem comp_sigP_symm (m : ℕ) (ψ : PosT t m → V) :
    (ψ ∘ (sigP σ m).symm) ∘ sigP σ m = ψ := by
  funext x
  simp

open Classical in
theorem paddedRegular_perm [Fintype V] {m : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω c : ℝ} (h : PaddedRegularT m p (permFam σ F) J ω c) :
    PaddedRegularT m (σ.symm ∘ p) F J ω c := by
  obtain ⟨y, hb, hl⟩ := h
  have hval : ∀ (τ : Multiset (Fin t)) (ψ : PosT t m → V), ValidCopyT m (σ.symm ∘ p) J τ ψ ↔
      ValidCopyT m p J (τ.map σ) (ψ ∘ (sigP σ m).symm) := by
    intro τ ψ
    rw [← validCopy_perm σ m p J τ (ψ ∘ (sigP σ m).symm), comp_sigP_symm]
  have htri : ∀ (τ : Multiset (Fin t)) (ψ : PosT t m → V), copyTriT m τ ψ = copyTriT m (τ.map σ) (ψ ∘ (sigP σ m).symm) := by
    intro τ ψ
    rw [← copyTriT_perm σ m τ (ψ ∘ (sigP σ m).symm), comp_sigP_symm]
  refine ⟨fun τ ψ => y (τ.map σ) (ψ ∘ (sigP σ m).symm), fun τ hτ ψ hv => ?_, fun e he => ?_⟩
  · exact hb _ ((mem_permFam σ).mpr hτ) _ ((hval τ ψ).mp hv)
  · have hsum := hl e he
    have key : ∀ τ : Multiset (Fin t),
        ∑ ψ ∈ univ.filter (fun ψ => ValidCopyT m (σ.symm ∘ p) J τ ψ ∧
            e ∈ triEdges (copyTriT m τ ψ)), y (τ.map σ) (ψ ∘ (sigP σ m).symm) =
        ∑ φ ∈ univ.filter (fun φ => ValidCopyT m p J (τ.map σ) φ ∧
            e ∈ triEdges (copyTriT m (τ.map σ) φ)), y (τ.map σ) φ := by
      intro τ
      refine Finset.sum_equiv ((sigP σ m).arrowCongr (Equiv.refl V)) (fun ψ => ?_)
        (fun _ _ => rfl)
      simp only [mem_filter, mem_univ, true_and]
      rw [hval, htri]
      exact Iff.rfl
    unfold permFam at hsum
    rw [sum_map] at hsum
    simp only [Function.Embedding.coeFn_mk] at hsum
    simp only [key]
    exact hsum

/-- `mem_filter` with an explicit decidability instance. -/
theorem mem_filter_inst {α : Type*} {s : Finset α} {P : α → Prop} (inst : DecidablePred P)
    {a : α} : a ∈ @Finset.filter α P inst s ↔ a ∈ s ∧ P a := @Finset.mem_filter α P inst s a

theorem extendable_perm [Fintype V] {K : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {J : Finset (Sym2 V)} {ω : ℝ} (h : ExtendableT K p (permFam σ F) J ω) :
    ExtendableT K (σ.symm ∘ p) F J ω := by
  intro k hk κ S T φ hinj hcls
  have h1 := h k hk (σ ∘ κ) S T φ hinj (fun x hx => by
    have := hcls x hx
    simp only [Function.comp_apply] at this ⊢
    exact (Equiv.symm_apply_eq σ).mp this)
  refine h1.trans ?_
  exact_mod_cast card_le_card (fun ψ hψ => by
    unfold goodExt at hψ ⊢
    rw [mem_filter_inst] at hψ ⊢
    obtain ⟨-, hfix, hinjψ, hclsψ, hJ⟩ := hψ
    refine ⟨mem_univ _, hfix, hinjψ, fun x => ?_, fun x y hxy hne hS hal => ?_⟩
    · have := hclsψ x
      simp only [Function.comp_apply] at this ⊢
      rw [this, Equiv.symm_apply_apply]
    · exact hJ x y hxy hne hS (allowed_perm' σ hal))

/-- **Relabelling invariance of the padded Keevash statement.** -/
theorem keevashPaddedSpec_perm {F : Finset (Multiset (Fin t))} (h : KeevashPaddedSpec F) :
    KeevashPaddedSpec (permFam σ F) := by
  intro m
  obtain ⟨ω0, hω0, n0, hm⟩ := h m
  refine ⟨ω0, hω0, n0, ?_⟩
  intro V _ _ hn ω hlo hhi p J hJ hadj hcls hdiv hreg hext
  refine hasDecomp_perm σ (hm hn ω hlo hhi (σ.symm ∘ p) J hJ
    (fun u v huv => allowed_perm σ (hadj u v huv)) (fun i => ?_) (isIntDiv_perm σ hdiv)
    (paddedRegular_perm σ hreg) (extendable_perm σ hext))
  rw [classCard_perm]
  exact hcls (σ i)

theorem card_three_perm {F : Finset (Multiset (Fin t))} (h : ∀ τ ∈ F, Multiset.card τ = 3) :
    ∀ τ ∈ permFam σ F, Multiset.card τ = 3 := by
  intro τ' hτ'
  obtain ⟨τ, hτ, rfl⟩ := exists_of_mem_permFam σ hτ'
  rw [Multiset.card_map]
  exact h τ hτ

/-- Completions of a pair transport along `σ`. -/
theorem completions_perm (F : Finset (Multiset (Fin t))) (a b : Fin t) :
    (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ permFam σ F).card =
      (univ.filter fun c => c ::ₘ ({σ.symm a, σ.symm b} : Multiset (Fin t)) ∈ F).card := by
  have heq : (univ.filter fun c => c ::ₘ ({a, b} : Multiset (Fin t)) ∈ permFam σ F) =
      (univ.filter fun c => c ::ₘ ({σ.symm a, σ.symm b} : Multiset (Fin t)) ∈ F).map
        σ.toEmbedding := by
    ext c
    rw [Finset.mem_map_equiv, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    have hc : c ::ₘ ({a, b} : Multiset (Fin t)) =
        (σ.symm c ::ₘ ({σ.symm a, σ.symm b} : Multiset (Fin t))).map σ := by
      simp
    rw [hc, mem_permFam]
  rw [heq, card_map]

end Perm

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_perm
