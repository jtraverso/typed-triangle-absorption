/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Robust.RMBG

@[expose] public section

/-!
# The two-sided robust matcher (`RMBG2`)

The vertex-link primitive of the balanced refiner. Positions on the `+` side are `Fin N` (the reserve
edges `X⁺`), on the `−` side `Fin N` (`X⁻`); the auxiliary positions are `D = Fin N` and `Y₁ = Fin N`
on the `+` side and `Z₁ = Fin (N + N)` on the `−` side. Edges come from a robust configuration
`c : Conf 2000 N` on `X₁ = X⁺ ⊔ D` (through `finSumFinEquiv`), `Y₁`, `Z₁`, plus the identity `X⁻ ↔ D`.

`exists_robust2`: for EVERY `S ⊆ X⁺` and `T ⊆ X⁻` with `|S| = |T|` there is an injection
`S ⊔ D ⊔ Y₁ → T ⊔ Z₁` along edges (cardinalities are equal: a perfect matching), and a selected
`+` position is never matched with a selected `−` position (`+` positions only meet auxiliaries).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Robust

open Finset

variable {N : ℕ}

/-- The `X⁺` copy and the `D` copy inside `X₁ = Fin (N + N)`. -/
def xl (s : Fin N) : Fin (N + N) := finSumFinEquiv (Sum.inl s)
def xr (δ : Fin N) : Fin (N + N) := finSumFinEquiv (Sum.inr δ)

theorem xl_inj : Function.Injective (xl (N := N)) := fun a b h => by
  unfold xl at h; simpa using finSumFinEquiv.injective h

theorem xr_inj : Function.Injective (xr (N := N)) := fun a b h => by
  unfold xr at h; simpa using finSumFinEquiv.injective h

theorem xl_ne_xr (a b : Fin N) : xl a ≠ xr b := by
  unfold xl xr; intro h; have := finSumFinEquiv.injective h; simp at this

theorem xr_ne_xl (a b : Fin N) : xr a ≠ xl b := fun h => xl_ne_xr b a h.symm

/-- The edges of the two-sided matcher, from a `+`-side position to a `−`-side position. -/
def Edge2 {d : ℕ} (c : Conf d N) (T : Finset (Fin N)) :
    (Fin N ⊕ (Fin N ⊕ Fin N)) → ({t // t ∈ T} ⊕ Fin (N + N)) → Prop
  | Sum.inl s, Sum.inr z => z ∈ NX c (xl s)
  | Sum.inr (Sum.inl δ), Sum.inl t => t.1 = δ
  | Sum.inr (Sum.inl δ), Sum.inr z => z ∈ NX c (xr δ)
  | Sum.inr (Sum.inr y), Sum.inr z => z ∈ NY c y
  | _, _ => False

/-- **Two-sided robust matching**, from any robust configuration. -/
theorem robust2_of_robust {d : ℕ} (c : Conf d N) (hc : Robust c) :
    ∀ S T : Finset (Fin N), #S = #T →
      ∃ f : ({s // s ∈ S} ⊕ (Fin N ⊕ Fin N)) → ({t // t ∈ T} ⊕ Fin (N + N)),
        Function.Injective f ∧
        (∀ s : {s // s ∈ S}, Edge2 c T (Sum.inl s.1) (f (Sum.inl s))) ∧
        (∀ a : Fin N ⊕ Fin N, Edge2 c T (Sum.inr a) (f (Sum.inr a))) := by
  classical
  intro S T hST
  let X' : Finset (Fin (N + N)) := S.image xl ∪ (univ \ T).image xr
  have hdisj : Disjoint (S.image xl) ((univ \ T).image xr) := by
    rw [disjoint_left]
    intro z h1 h2
    obtain ⟨a, -, rfl⟩ := mem_image.mp h1
    obtain ⟨b, -, h⟩ := mem_image.mp h2
    exact xl_ne_xr a b h.symm
  have hTN : #T ≤ N := by simpa using card_le_univ T
  have hX' : #X' = N := by
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ xl_inj,
      card_image_of_injective _ xr_inj, card_sdiff_of_subset (subset_univ _), card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨g, hg, hgX, hgY⟩ := hc X' hX'
  have hmemS : ∀ s ∈ S, xl s ∈ X' := fun s hs => mem_union_left _ (mem_image_of_mem _ hs)
  have hmemD : ∀ δ, δ ∉ T → xr δ ∈ X' := fun δ hδ =>
    mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨mem_univ _, hδ⟩))
  let e1 : ({s // s ∈ S} ⊕ (Fin N ⊕ Fin N)) → ({t // t ∈ T} ⊕ ({x // x ∈ X'} ⊕ Fin N)) := fun v =>
    match v with
    | Sum.inl s => Sum.inr (Sum.inl ⟨xl s.1, hmemS s.1 s.2⟩)
    | Sum.inr (Sum.inl δ) =>
        if h : δ ∈ T then Sum.inl ⟨δ, h⟩ else Sum.inr (Sum.inl ⟨xr δ, hmemD δ h⟩)
    | Sum.inr (Sum.inr y) => Sum.inr (Sum.inr y)
  let f := Sum.map id g ∘ e1
  let dec : ({t // t ∈ T} ⊕ ({x // x ∈ X'} ⊕ Fin N)) → ({s // s ∈ S} ⊕ (Fin N ⊕ Fin N)) := fun w =>
    match w with
    | Sum.inl t => Sum.inr (Sum.inl t.1)
    | Sum.inr (Sum.inr y) => Sum.inr (Sum.inr y)
    | Sum.inr (Sum.inl z) =>
        match finSumFinEquiv.symm z.1 with
        | Sum.inl s => if hs : s ∈ S then Sum.inl ⟨s, hs⟩ else Sum.inr (Sum.inl s)
        | Sum.inr δ => Sum.inr (Sum.inl δ)
  have hdec : Function.LeftInverse dec e1 := by
    rintro (s | δ | y)
    · have h1 : finSumFinEquiv.symm (xl s.1) = Sum.inl s.1 := by unfold xl; exact Equiv.symm_apply_apply _ _
      simp only [e1, dec, h1, dif_pos s.2]
    · by_cases hδ : δ ∈ T
      · simp only [e1, dif_pos hδ, dec]
      · have h1 : finSumFinEquiv.symm (xr δ) = Sum.inr δ := by unfold xr; exact Equiv.symm_apply_apply _ _
        simp only [e1, dif_neg hδ, dec, h1]
    · simp only [e1, dec]
  have he1 : Function.Injective e1 := hdec.injective
  refine ⟨f, (Sum.map_injective.mpr ⟨Function.injective_id, hg⟩).comp he1, ?_, ?_⟩
  · intro s
    exact hgX ⟨xl s.1, hmemS s.1 s.2⟩
  · rintro (δ | y)
    · simp only [f, e1, Function.comp_apply]
      split_ifs with h
      · simp [Edge2]
      · exact hgX ⟨xr δ, hmemD δ h⟩
    · exact hgY y

/-- **Two-sided robust matching** with degree `≤ 4000`. -/
theorem exists_robust2 (hN : 1 ≤ N) : ∃ c : Conf 2000 N,
    ∀ S T : Finset (Fin N), #S = #T →
      ∃ f : ({s // s ∈ S} ⊕ (Fin N ⊕ Fin N)) → ({t // t ∈ T} ⊕ Fin (N + N)),
        Function.Injective f ∧
        (∀ s : {s // s ∈ S}, Edge2 c T (Sum.inl s.1) (f (Sum.inl s))) ∧
        (∀ a : Fin N ⊕ Fin N, Edge2 c T (Sum.inr a) (f (Sum.inr a))) := by
  obtain ⟨c, hc⟩ := exists_robust hN
  exact ⟨c, robust2_of_robust c hc⟩

end PartitionedTriangleAbsorption.BlowupB.Robust

#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.exists_robust2
