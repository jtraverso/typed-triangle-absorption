/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelCatalogue
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLiftCore

@[expose] public section

/-! A subset of the private-path network balanced at all private vertices
is a union of whole channel paths. This recovers the selected channels from
the balance witness, so unused channels can be covered as whole pieces. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.UnusedChannelSelection

open Finset Cycles

variable {P E : Type} [DecidableEq P] [Fintype E] [DecidableEq E]

def first (src : E → P) (e : E) : RootPaths.Vert P E × RootPaths.Vert P E :=
  (Sum.inl (src e), Sum.inr (e, 0))

def middle (e : E) : RootPaths.Vert P E × RootPaths.Vert P E :=
  (Sum.inr (e, 0), Sum.inr (e, 1))

def last (dst : E → P) (e : E) : RootPaths.Vert P E × RootPaths.Vert P E :=
  (Sum.inr (e, 1), Sum.inl (dst e))

private theorem member_iff_filter_pos {W : Type} [DecidableEq W]
    (N A : Finset W) (hAN : A ⊆ N) (f : W → Prop) [DecidablePred f]
    (a : W) (haN : a ∈ N) (hfa : f a) (hcard : (N.filter f).card = 1) :
    a ∈ A ↔ 0 < (A.filter f).card := by
  obtain ⟨b, hb⟩ := card_eq_one.mp hcard
  have hab : a = b := by
    have hh : a ∈ N.filter f := mem_filter.mpr ⟨haN, hfa⟩
    simpa only [hb, mem_singleton] using hh
  constructor
  · intro ha
    exact card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hfa⟩⟩
  · intro h
    obtain ⟨x, hx⟩ := card_pos.mp h
    have hxN : x ∈ N.filter f :=
      mem_filter.mpr ⟨hAN (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
    have hxb : x = b := by simpa only [hb, mem_singleton] using hxN
    simpa only [hxb, ← hab] using (mem_filter.mp hx).1

theorem exists_selected (src dst : E → P)
    (A : Finset (RootPaths.Vert P E × RootPaths.Vert P E))
    (hAN : A ⊆ RootPaths.arcs src dst)
    (haux : ∀ e i, inDeg A (Sum.inr (e, i)) = outDeg A (Sum.inr (e, i))) :
    ∃ T : Finset E, A = RootPaths.arcsOf src dst T := by
  let N := RootPaths.arcs src dst
  have hfirst : ∀ e, first src e ∈ N := by
    intro e
    exact mem_biUnion.mpr ⟨e, mem_univ _, by simp [RootPaths.pathArcs, first]⟩
  have hmiddle : ∀ e, middle e ∈ N := by
    intro e
    exact mem_biUnion.mpr ⟨e, mem_univ _, by simp [RootPaths.pathArcs, middle]⟩
  have hlast : ∀ e, last dst e ∈ N := by
    intro e
    exact mem_biUnion.mpr ⟨e, mem_univ _, by simp [RootPaths.pathArcs, last]⟩
  have hin : ∀ e i, (N.filter (fun a => a.2 = Sum.inr (e, i))).card = 1 := by
    intro e i
    simpa only [N, RootPaths.arcs, mem_univ, if_true] using
      RootPaths.card_in_aux src dst univ e i
  have hout : ∀ e i, (N.filter (fun a => a.1 = Sum.inr (e, i))).card = 1 := by
    intro e i
    simpa only [N, RootPaths.arcs, mem_univ, if_true] using
      RootPaths.card_out_aux src dst univ e i
  have h01 : ∀ e, first src e ∈ A ↔ middle e ∈ A := by
    intro e
    rw [member_iff_filter_pos N A hAN (fun a => a.2 = Sum.inr (e, 0))
        _ (hfirst e) rfl (hin e 0),
      member_iff_filter_pos N A hAN (fun a => a.1 = Sum.inr (e, 0))
        _ (hmiddle e) rfl (hout e 0)]
    change 0 < inDeg A (Sum.inr (e, 0)) ↔ 0 < outDeg A (Sum.inr (e, 0))
    rw [haux e 0]
  have h12 : ∀ e, middle e ∈ A ↔ last dst e ∈ A := by
    intro e
    rw [member_iff_filter_pos N A hAN (fun a => a.2 = Sum.inr (e, 1))
        _ (hmiddle e) rfl (hin e 1),
      member_iff_filter_pos N A hAN (fun a => a.1 = Sum.inr (e, 1))
        _ (hlast e) rfl (hout e 1)]
    change 0 < inDeg A (Sum.inr (e, 1)) ↔ 0 < outDeg A (Sum.inr (e, 1))
    rw [haux e 1]
  have hpath : ∀ e, ∀ a ∈ RootPaths.pathArcs src dst e,
      a ∈ A ↔ first src e ∈ A := by
    intro e a ha
    simp only [RootPaths.pathArcs, mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact (h01 e).symm
    · exact ((h01 e).trans (h12 e)).symm
  refine ⟨univ.filter (fun e => first src e ∈ A), ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨e, _, he⟩ := mem_biUnion.mp (hAN ha)
    exact mem_biUnion.mpr
      ⟨e, mem_filter.mpr ⟨mem_univ _, (hpath e a he).mp ha⟩, he⟩
  · intro ha
    obtain ⟨e, he, hea⟩ := mem_biUnion.mp ha
    exact (hpath e a hea).mpr (mem_filter.mp he).2

/-- The unused part of the fixed network has a partition into its original
private channel paths. Balance after root identification is proved separately. -/
theorem unused_partition (src dst : E → P)
    (A : Finset (RootPaths.Vert P E × RootPaths.Vert P E))
    (hAN : A ⊆ RootPaths.arcs src dst)
    (haux : ∀ e i, inDeg A (Sum.inr (e, i)) = outDeg A (Sum.inr (e, i))) :
    ∃ Q ⊆ ChannelCatalogue.pieces src dst,
      (Q : Set (Finset (RootPaths.Vert P E × RootPaths.Vert P E))).PairwiseDisjoint id ∧
      Q.biUnion id = RootPaths.arcs src dst \ A := by
  obtain ⟨T, hA⟩ := exists_selected src dst A hAN haux
  have hdis : Disjoint A (RootPaths.arcsOf src dst Tᶜ) := by
    rw [hA, disjoint_left]
    intro a ha hb
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    obtain ⟨f, hf, haf⟩ := mem_biUnion.mp hb
    have hef : e ≠ f := by
      intro h
      subst f
      exact (mem_compl.mp hf) he
    exact disjoint_left.mp (ChannelCatalogue.path_disjoint src dst hef) hae haf
  have hunion : A ∪ RootPaths.arcsOf src dst Tᶜ = RootPaths.arcs src dst := by
    rw [hA]
    change T.biUnion (RootPaths.pathArcs src dst) ∪
      Tᶜ.biUnion (RootPaths.pathArcs src dst) = univ.biUnion (RootPaths.pathArcs src dst)
    rw [← union_biUnion, union_compl]
  have hrest : RootPaths.arcs src dst \ A = RootPaths.arcsOf src dst Tᶜ := by
    ext a
    constructor
    · intro ha
      have hn := (mem_sdiff.mp ha).1
      rw [← hunion] at hn
      exact (mem_union.mp hn).resolve_left (mem_sdiff.mp ha).2
    · intro ha
      refine mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [← hunion]
        exact mem_union_right _ ha
      · intro h
        exact disjoint_left.mp hdis h ha
  refine ⟨Tᶜ.image (RootPaths.pathArcs src dst), ?_, ?_, ?_⟩
  · exact image_subset_image (subset_univ _)
  · intro Q hQ R hR hQR
    obtain ⟨e, _, rfl⟩ := mem_image.mp hQ
    obtain ⟨f, _, rfl⟩ := mem_image.mp hR
    apply ChannelCatalogue.path_disjoint src dst
    intro h
    subst f
    exact hQR rfl
  · rw [hrest, image_biUnion]
    rfl

/-- Apply the unused-channel partition directly to the completion supplied by
RootInput: the lifted input has no incidence at any private channel vertex. -/
theorem unused_of_completed (src dst : E → P)
    (S : Finset (P × P))
    (A : Finset (RootPaths.Vert P E × RootPaths.Vert P E))
    (hAN : A ⊆ RootPaths.arcs src dst)
    (hb : Balanced (A ∪ S.map (liftArc P (E × Fin 2)))) :
    ∃ Q ⊆ ChannelCatalogue.pieces src dst,
      (Q : Set (Finset (RootPaths.Vert P E × RootPaths.Vert P E))).PairwiseDisjoint id ∧
      Q.biUnion id = RootPaths.arcs src dst \ A := by
  have hdis : Disjoint A (S.map (liftArc P (E × Fin 2))) := by
    rw [disjoint_left]
    intro a ha hb
    obtain ⟨b, _, rfl⟩ := mem_map.mp hb
    exact RootLift.no_old_arc src dst b.1 b.2 (hAN ha)
  apply unused_partition src dst A hAN
  intro e i
  have h := hb (Sum.inr (e, i))
  rw [RootLift.inDeg_union_eq _ _ hdis, RootLift.outDeg_union_eq _ _ hdis,
    inDeg_map_liftArc, outDeg_map_liftArc] at h
  simpa only [Sum.elim_inr, Nat.add_zero] using h

end PartitionedTriangleAbsorption.BlowupB.LatinCore.UnusedChannelSelection

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.UnusedChannelSelection.exists_selected
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.UnusedChannelSelection.unused_partition
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.UnusedChannelSelection.unused_of_completed
