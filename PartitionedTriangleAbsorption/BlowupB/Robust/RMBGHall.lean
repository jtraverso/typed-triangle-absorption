/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Robustly matchable bipartite graphs: the deterministic half

The bipartite graph of a configuration `c = (φ, ψ)` of `2d` permutations of `Fin (m + m)` has
left side `X ⊔ Y` with `X = Fin (m + m)`, `Y = Fin m` and right side `Z = Fin (m + m)`:
`x ~ φ i x` and `y ~ ψ i (inl y), ψ i (inr y)` (through `finSumFinEquiv`).
All degrees are at most `2d`.

`robust_of_good`: if `c` has the expansion properties `P1`, `P3`, `P4` (and `d ≥ 1`), then for EVERY
`X' ⊆ X` with `|X'| = m` there is an injection `X' ⊔ Y → Z` along edges, i.e. (cardinalities being
equal) a perfect matching between `X' ⊔ Y` and `Z` (Montgomery's robustly matchable bipartite graph).
The random half (`Robust.RMBGCount`) shows that good configurations exist.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Robust

open Finset

/-- A configuration: `d` permutations for `X → Z` and `d` permutations for `Y ⊔ Y → Z`. -/
abbrev Conf (d m : ℕ) := (Fin d → Equiv.Perm (Fin (m + m))) × (Fin d → Equiv.Perm (Fin (m + m)))

variable {d m : ℕ}

/-- The two copies of `y`. -/
def yl (y : Fin m) : Fin (m + m) := finSumFinEquiv (Sum.inl y)
def yr (y : Fin m) : Fin (m + m) := finSumFinEquiv (Sum.inr y)

theorem yl_ne_yr (y y' : Fin m) : yl y ≠ yr y' := by
  unfold yl yr
  intro h
  have := finSumFinEquiv.injective h
  simp at this

theorem yl_inj : Function.Injective (yl (m := m)) := fun a b h => by
  unfold yl at h; simpa using finSumFinEquiv.injective h

theorem yr_inj : Function.Injective (yr (m := m)) := fun a b h => by
  unfold yr at h; simpa using finSumFinEquiv.injective h

/-- Neighbours of `x ∈ X`. -/
def NX (c : Conf d m) (x : Fin (m + m)) : Finset (Fin (m + m)) := univ.image fun i => c.1 i x

/-- Neighbours of `y ∈ Y`. -/
def NY (c : Conf d m) (y : Fin m) : Finset (Fin (m + m)) :=
  (univ.image fun i => c.2 i (yl y)) ∪ (univ.image fun i => c.2 i (yr y))

/-- The `Y`-neighbours of a set `C ⊆ Z`. -/
def NYinv (c : Conf d m) (C : Finset (Fin (m + m))) : Finset (Fin m) :=
  univ.filter fun y => ∃ z ∈ C, z ∈ NY c y

/-- (P1) small sets of `X` double. -/
def P1 (c : Conf d m) : Prop :=
  ∀ A : Finset (Fin (m + m)), 1 ≤ #A → 10 * #A ≤ m → 2 * #A ≤ #(A.biUnion (NX c))

/-- (P3) small sets of `Z` have at least as many `Y`-neighbours. -/
def P3 (c : Conf d m) : Prop :=
  ∀ C : Finset (Fin (m + m)), 1 ≤ #C → 10 * #C ≤ m → #C ≤ #(NYinv c C)

/-- (P4) large sets on both sides are joined by an edge. -/
def P4 (c : Conf d m) : Prop :=
  ∀ (A1 : Finset (Fin (m + m))) (A2 : Finset (Fin m)) (C : Finset (Fin (m + m))),
    m ≤ 10 * (#A1 + #A2) → m ≤ 10 * #C →
      (∃ x ∈ A1, ∃ z ∈ C, z ∈ NX c x) ∨ (∃ y ∈ A2, ∃ z ∈ C, z ∈ NY c y)

def Good (c : Conf d m) : Prop := P1 c ∧ P3 c ∧ P4 c

/-- The robust matching property. -/
def Robust (c : Conf d m) : Prop :=
  ∀ X' : Finset (Fin (m + m)), #X' = m →
    ∃ f : {x // x ∈ X'} ⊕ Fin m → Fin (m + m), Function.Injective f ∧
      (∀ x, f (Sum.inl x) ∈ NX c x.1) ∧ (∀ y, f (Sum.inr y) ∈ NY c y)

/-- (P2) is deterministic: `ψ₀` alone doubles every set of `Y`. -/
theorem two_mul_le_NY (c : Conf d m) (hd : 0 < d) (B : Finset (Fin m)) :
    2 * #B ≤ #(B.biUnion (NY c)) := by
  classical
  let i0 : Fin d := ⟨0, hd⟩
  have hsub : (B.image fun y => c.2 i0 (yl y)) ∪ (B.image fun y => c.2 i0 (yr y)) ⊆
      B.biUnion (NY c) := by
    intro z hz
    rw [mem_biUnion]
    rcases mem_union.mp hz with h | h
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
      exact ⟨y, hy, mem_union_left _ (mem_image.mpr ⟨i0, mem_univ _, rfl⟩)⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
      exact ⟨y, hy, mem_union_right _ (mem_image.mpr ⟨i0, mem_univ _, rfl⟩)⟩
  have hdisj : Disjoint (B.image fun y => c.2 i0 (yl y)) (B.image fun y => c.2 i0 (yr y)) := by
    rw [disjoint_left]
    intro z h1 h2
    obtain ⟨y, -, rfl⟩ := mem_image.mp h1
    obtain ⟨y', -, h⟩ := mem_image.mp h2
    exact yl_ne_yr y y' ((c.2 i0).injective h).symm
  have h1 : #(B.image fun y => c.2 i0 (yl y)) = #B :=
    card_image_of_injective _ ((c.2 i0).injective.comp yl_inj)
  have h2 : #(B.image fun y => c.2 i0 (yr y)) = #B :=
    card_image_of_injective _ ((c.2 i0).injective.comp yr_inj)
  calc 2 * #B = #((B.image fun y => c.2 i0 (yl y)) ∪ (B.image fun y => c.2 i0 (yr y))) := by
        rw [card_union_of_disjoint hdisj, h1, h2]; ring
    _ ≤ _ := card_le_card hsub

/-- **Good configurations are robust.** -/
theorem robust_of_good (c : Conf d m) (hd : 0 < d) (hc : Good c) : Robust c := by
  classical
  obtain ⟨hP1, hP3, hP4⟩ := hc
  intro X' hX'
  let t : {x // x ∈ X'} ⊕ Fin m → Finset (Fin (m + m)) := fun v =>
    match v with
    | Sum.inl x => NX c x.1
    | Sum.inr y => NY c y
  suffices hall : ∀ s : Finset ({x // x ∈ X'} ⊕ Fin m), #s ≤ #(s.biUnion t) by
    obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
    exact ⟨f, hf, fun x => hft (Sum.inl x), fun y => hft (Sum.inr y)⟩
  intro s
  -- the two parts of `s`
  let S1 : Finset (Fin (m + m)) := (s.preimage Sum.inl (Sum.inl_injective.injOn)).map
    (Function.Embedding.subtype _)
  let S2 : Finset (Fin m) := s.preimage Sum.inr (Sum.inr_injective.injOn)
  have hS1 : #S1 = #(s.preimage Sum.inl (Sum.inl_injective.injOn)) := card_map _
  have hs : #s = #S1 + #S2 := by
    rw [hS1, ← card_disjSum]
    congr 1
    ext v; rcases v with x | y <;> simp [S2]
  have hS1X : S1 ⊆ X' := by
    intro x hx
    obtain ⟨x', -, rfl⟩ := mem_map.mp hx
    exact x'.2
  have hS1m : #S1 ≤ m := by have := card_le_card hS1X; omega
  have hN1 : S1.biUnion (NX c) ⊆ s.biUnion t := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_biUnion.mp hz
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    exact mem_biUnion.mpr ⟨Sum.inl x', by simpa using hx', hzx⟩
  have hN2 : S2.biUnion (NY c) ⊆ s.biUnion t := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_biUnion.mp hz
    exact mem_biUnion.mpr ⟨Sum.inr y, by simpa [S2] using hy, hzy⟩
  by_contra hlt
  push Not at hlt
  set N := s.biUnion t
  set T' : Finset (Fin (m + m)) := univ \ N
  have hT' : #T' = (m + m) - #N := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have hS2m : #S2 ≤ m := by simpa using card_le_univ S2
  have hNm : #N ≤ m + m := by simpa using card_le_univ N
  -- no edge from `s` to `T'`
  have hnoedge1 : ∀ x ∈ S1, ∀ z ∈ T', z ∉ NX c x := by
    intro x hx z hz hzx
    exact (mem_sdiff.mp hz).2 (hN1 (mem_biUnion.mpr ⟨x, hx, hzx⟩))
  have hnoedge2 : ∀ y ∈ S2, ∀ z ∈ T', z ∉ NY c y := by
    intro y hy z hz hzy
    exact (mem_sdiff.mp hz).2 (hN2 (mem_biUnion.mpr ⟨y, hy, hzy⟩))
  by_cases hsmall : 10 * #s ≤ m
  · -- small `s`: (P1) and (P2)
    have h2 := two_mul_le_NY c hd S2
    have h2' : 2 * #S2 ≤ #N := h2.trans (card_le_card hN2)
    rcases Nat.eq_zero_or_pos #S1 with h0 | hpos
    · omega
    · have h1 := hP1 S1 hpos (by omega)
      have h1' : 2 * #S1 ≤ #N := h1.trans (card_le_card hN1)
      omega
  · by_cases hTsmall : 10 * #T' ≤ m
    · -- small complement: (P3)
      have hT1 : 1 ≤ #T' := by omega
      have h3 := hP3 T' hT1 hTsmall
      have hsub : NYinv c T' ⊆ univ \ S2 := by
        intro y hy
        obtain ⟨z, hz, hzy⟩ := (mem_filter.mp hy).2
        refine mem_sdiff.mpr ⟨mem_univ _, fun hyS => hnoedge2 y hyS z hz hzy⟩
      have h4 := card_le_card hsub
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at h4
      omega
    · -- both large: (P4)
      rcases hP4 S1 S2 T' (by omega) (by omega) with ⟨x, hx, z, hz, hzx⟩ | ⟨y, hy, z, hz, hzy⟩
      · exact hnoedge1 x hx z hz hzx
      · exact hnoedge2 y hy z hz hzy

end PartitionedTriangleAbsorption.BlowupB.Robust

#print axioms PartitionedTriangleAbsorption.BlowupB.Robust.robust_of_good
