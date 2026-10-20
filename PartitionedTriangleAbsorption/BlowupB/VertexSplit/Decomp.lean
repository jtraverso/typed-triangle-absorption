/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Basic

@[expose] public section

/-!
# Vertex splitting: decompositions of the split edge set come from decompositions of the original

`hasDecomp_of_split` (Lemma 2(b,c) of the written proof): if `B` is loopless and the split edge set
`φ(B)` has an `F'`-decomposition, then `B` has an `F`-decomposition. Each split triangle is
projected to the original vertices: its three corners are copies of distinct vertices (the edges of
`φ(B)` join copies of distinct vertices), its type maps into `F` by `π`, and `φ` of the projected
edges are exactly the edges of the split triangle.
-/

namespace PartitionedTriangleAbsorption.BlowupB.VertexSplit

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer

variable {t t' : ℕ} {F : Finset (Multiset (Fin t))} (S : SplitData F t')
variable {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin t)

theorem p_fstV (x : SV S p) : p (fstV S p x) = S.π (sp S p x) := by
  obtain ⟨⟨v, j⟩, s, hs⟩ := x
  simp only [fstV, sp] at hs ⊢
  rw [hs, S.π_cls]

theorem mem_triEdges_mk' {D : Finset V} {u v : V} :
    s(u, v) ∈ triEdges D ↔ u ∈ D ∧ v ∈ D ∧ u ≠ v := by
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  tauto

/-- Projection of a split triangle all of whose edges lie in `φ(B)`. -/
theorem proj_tri {B : Finset (Sym2 V)} (hloop : ∀ e ∈ B, ¬ e.IsDiag) {s : Finset (SV S p)}
    (hs : IsTypedTri (sp S p) S.F' s) (hsub : triEdges s ⊆ splitE S p B) :
    Set.InjOn (fstV S p) s ∧ IsTypedTri p F (s.image (fstV S p)) ∧
      splitE S p (triEdges (s.image (fstV S p))) = triEdges s ∧
      triEdges (s.image (fstV S p)) ⊆ B := by
  have hinj : Set.InjOn (fstV S p) s := by
    intro x hx y hy hxy
    by_contra hne
    have hmem : s(x, y) ∈ triEdges s := mem_triEdges_mk'.mpr ⟨hx, hy, hne⟩
    exact fst_ne_of_mem_splitE S p hloop (hsub hmem) hxy
  refine ⟨hinj, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [card_image_of_injOn hinj]; exact hs.1
  · have h1 : (s.image (fstV S p)).val = s.val.map (fstV S p) := by
      rw [image_val_of_injOn hinj]
    rw [h1, Multiset.map_map]
    have h2 : (p ∘ fstV S p) = S.π ∘ sp S p := funext (p_fstV S p)
    rw [h2, ← Multiset.map_map]
    exact S.π_mem _ hs.2
  · ext f
    constructor
    · intro hf
      obtain ⟨e, he, rfl⟩ := mem_image.mp hf
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha, hb, hab⟩ := mem_triEdges_mk'.mp he
        obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
        have hxy : x ≠ y := fun h => hab (h ▸ rfl)
        have hmem : s(x, y) ∈ triEdges s := mem_triEdges_mk'.mpr ⟨hx, hy, hxy⟩
        have := (splitEdge_map_fst S p (hsub hmem)).1
        rw [Sym2.map_mk] at this
        rw [this]; exact hmem
    · intro hf
      refine mem_image.mpr ⟨Sym2.map (fstV S p) f, ?_, (splitEdge_map_fst S p (hsub hf)).1⟩
      induction f using Sym2.ind with
      | _ x y =>
        obtain ⟨hx, hy, hxy⟩ := mem_triEdges_mk'.mp hf
        rw [Sym2.map_mk]
        exact mem_triEdges_mk'.mpr ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hy,
          fun h => hxy (hinj hx hy h)⟩
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mem_triEdges_mk'.mp he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
      have hxy : x ≠ y := fun h => hab (h ▸ rfl)
      have := (splitEdge_map_fst S p (hsub (mem_triEdges_mk'.mpr ⟨hx, hy, hxy⟩))).2
      rwa [Sym2.map_mk] at this

/-- **Decompositions come back from the split side.** -/
theorem hasDecomp_of_split {B : Finset (Sym2 V)} (hloop : ∀ e ∈ B, ¬ e.IsDiag)
    (h : HasDecomp (sp S p) S.F' (splitE S p B)) : HasDecomp p F B := by
  classical
  obtain ⟨D', hD'typ, hD'dis, hD'U⟩ := h
  have hsub : ∀ s ∈ D', triEdges s ⊆ splitE S p B := fun s hs => by
    rw [← hD'U]; exact subset_biUnion_of_mem _ hs
  have hP := fun s (hs : s ∈ D') => proj_tri S p hloop (hD'typ s hs) (hsub s hs)
  -- nonempty edge sets of split triangles
  have hne : ∀ s ∈ D', (triEdges s).Nonempty := by
    intro s hs
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (hD'typ s hs).1
    exact ⟨s(x, y), mem_triEdges_mk'.mpr ⟨by simp, by simp, hxy⟩⟩
  refine ⟨D'.image fun s => s.image (fstV S p), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := mem_image.mp hs
    exact (hP s' hs').2.1
  · intro a ha b hb hab
    obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
    obtain ⟨s', hs', rfl⟩ := mem_image.mp hb
    have hss : s ≠ s' := fun h => hab (h ▸ rfl)
    rw [Function.onFun, disjoint_left]
    intro e he he'
    have h1 : splitEdge S p e ∈ triEdges s := by
      rw [← (hP s hs).2.2.1]; exact mem_image_of_mem _ he
    have h2 : splitEdge S p e ∈ triEdges s' := by
      rw [← (hP s' hs').2.2.1]; exact mem_image_of_mem _ he'
    exact disjoint_left.mp (hD'dis hs hs' hss) h1 h2
  · ext e
    constructor
    · intro he
      obtain ⟨a, ha, hea⟩ := mem_biUnion.mp he
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
      exact (hP s hs).2.2.2 hea
    · intro he
      have h1 : splitEdge S p e ∈ splitE S p B := mem_image_of_mem _ he
      rw [← hD'U] at h1
      obtain ⟨s, hs, hes⟩ := mem_biUnion.mp h1
      refine mem_biUnion.mpr ⟨s.image (fstV S p), mem_image_of_mem _ hs, ?_⟩
      rw [← (hP s hs).2.2.1] at hes
      exact (mem_splitE S p).mp hes

end PartitionedTriangleAbsorption.BlowupB.VertexSplit

#print axioms PartitionedTriangleAbsorption.BlowupB.VertexSplit.hasDecomp_of_split
