/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalEmbedding
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalInput
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootCatalogueTransport
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalCatalogueLoad
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueReserveSupport
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ReplacementPartition

@[expose] public section

/-! Assemble the fixed physical reserve and its balanced catalogue. The
same replacement is used for every residual partition of the input. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalRefiner

open Finset Cycles AntiEdgeSelection StructuralF3General PaddedNoCommon

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

theorem exists_refiner (p : V → Fin 3) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset (V × V)) (ω t n : ℝ)
    (hω : 0 < ω) (ht : 0 < t) (ht1 : t ≤ 1) (hn : 0 < n)
    (hsize : 1 ≤ t ^ 2 * n) (hsmall : 32 * (RootPhysicalEmbedding.factor : ℝ) * t ≤ ω)
    (hXcyc : IsCyc (CatalogueColours.colour ∘ p) X)
    (hXcard : (X.card : ℝ) ≤ t ^ 2 * n ^ 2)
    (hXdeg : ∀ r, (deg X r : ℝ) ≤ 2 * t ^ 2 * n)
    (hB : DegBounded (PhysicalPathArcs.forget X) (2 * t ^ 2 * n))
    (hs : GuardedSupply p G (fun i j => i ≠ j) 2 (ω * n)) :
    ∃ (R : Finset (V × V)) (lib : Finset (Finset (V × V))),
      (∀ e ∈ R, G.Adj e.1 e.2) ∧ IsCyc (CatalogueColours.colour ∘ p) R ∧ Disjoint R X ∧
      (∀ r, (deg R r : ℝ) ≤ 3 * (RootPhysicalEmbedding.factor : ℝ) * t * n) ∧
      (∀ P ∈ lib, P ⊆ R ∪ X ∧ P.card ≤ 80 ∧ Cycles.Balanced P) ∧
      lib.card ≤ (49 * RootCatalogueBudget.constant + 16) * X.card ∧
      (∀ r, (catalogLoad lib r : ℝ) ≤ 3 * (RootPhysicalEmbedding.factor : ℝ) * t * n) ∧
      ∀ L ⊆ X, Cycles.Balanced L →
        ∃ Q ⊆ lib, (Q : Set (Finset (V × V))).PairwiseDisjoint id ∧ Q.biUnion id = R ∪ L := by
  obtain ⟨σ, U, hUf, hUd, cU, R, lib, f, x, y, z, hRc, hRd, hp, hAc, hcount,
    hpin, hcolour, hpath, havoid, hdis, hload, hcover, hpart⟩ :=
      RootPhysicalEmbedding.exists_embedding p G X (PhysicalPathArcs.forget X) ω t n
        hω ht ht1 hn hsize hsmall hXcyc hXcard hXdeg hB hs
  let I0 := (RootCatalogueBudget.input X X σ).map (liftArc (RootCatalogueBudget.Vert X σ) U)
  let keep := (CatalogueWeights.arcs lib).filter (fun e => e ∈ I0)
  let R0 := R ∪ (RootCatalogueBudget.network X σ).map (liftArc (RootCatalogueBudget.Vert X σ) U)
  let blk := PhysicalReplacement.block keep f x y z
  let RP := (CatalogueWeights.arcs lib \ keep).biUnion blk
  let LP := lib.image (fun P => P.biUnion blk)
  have hsupport : ∀ P ∈ lib, P ⊆ R0 ∪ I0 := by
    intro P hP
    simpa only [R0, I0, map_union, union_assoc] using (hp P hP).2.1
  have hNI : Disjoint (RootCatalogueBudget.network X σ) (RootCatalogueBudget.input X X σ) :=
    RootLift.disjoint_input (RootChannels.src (SplitPorts.root X) σ)
      (RootChannels.dst (SplitPorts.root X) σ) (SplitPorts.arcs X)
  have hR0dis : Disjoint R0 I0 := disjoint_union_left.mpr
    ⟨hRd.mono_right (map_subset_map.mpr subset_union_right), (disjoint_map _).mpr hNI⟩
  have hE : CatalogueWeights.arcs lib \ keep = R0 :=
    CatalogueReserveSupport.reserve_eq lib R0 I0 hsupport hcover hR0dis
  have hinput : ∀ L ⊆ X,
      ((RootCatalogueBudget.input X L σ).map (liftArc (RootCatalogueBudget.Vert X σ) U)).image
        (arcImage f) = L := fun L hL => RootPhysicalInput.original_input_image X L hL σ f hpin
  have hkeep : keep ⊆ I0 := fun e he => (mem_filter.mp he).2
  have hkeepAll : keep ⊆ CatalogueWeights.arcs lib := filter_subset _ _
  have hinj : Set.InjOn (arcImage f) (keep : Set _) :=
    (RootPhysicalInput.injective_lifted_input (SplitPorts.arcs X) (SplitPorts.root X) f hpin
      (SplitPorts.root_injective X X)).mono hkeep
  have hinputMem : ∀ e ∈ keep, arcImage f e ∈ X := by
    intro e he
    have hsub : I0.image (arcImage f) ⊆ X := le_of_eq (hinput X subset_rfl)
    exact hsub (mem_image.mpr ⟨e, hkeep he, rfl⟩)
  have hinputEdge : ∀ e ∈ keep, s(f e.1,f e.2) ∈ PhysicalPathArcs.forget X := by
    intro e he
    exact mem_image.mpr ⟨arcImage f e, hinputMem e he, rfl⟩
  have hblocks : (CatalogueWeights.arcs lib : Set _).PairwiseDisjoint blk :=
    PhysicalReplacement.blocks_disjoint _ keep f x y z _ hinj hinputEdge havoid hdis
  have hnet := PhysicalReplacement.net_block (CatalogueWeights.arcs lib) keep f x y z G
    (fun e he => (hpath e he).2.2.2)
  have hbalanced : ∀ P ∈ lib, Cycles.Balanced (P.biUnion blk) :=
    RootCatalogueTransport.catalogue_balanced (SplitPorts.root X)
      (RootChannels.src (SplitPorts.root X) σ) (RootChannels.dst (SplitPorts.root X) σ)
      lib f blk hpin
      (fun e => (RootChannels.src_root _ _ e).trans (RootChannels.dst_root _ _ e).symm)
      (fun P hP => (hp P hP).2.2.2) hblocks hnet
  have hcf : ∀ a, CatalogueColours.colour (p (f a)) =
      Sum.elim (RootCatalogueBudget.colour X σ (CatalogueColours.colour ∘ p)) cU a := by
    intro a
    rw [hcolour a, CatalogueColours.colour_toFin]
  have hcyc : ∀ e ∈ CatalogueWeights.arcs lib, IsCyc (CatalogueColours.colour ∘ p) (blk e) := by
    intro e he
    by_cases hei : e ∈ keep
    · intro a ha
      have hae : a = arcImage f e := by simpa [blk, PhysicalReplacement.block, hei, arcImage] using ha
      subst a
      change CatalogueColours.colour (p (f e.2)) = CatalogueColours.colour (p (f e.1)) + 1
      rw [hcf, hcf]
      exact hAc e he
    · have hh := hpath e (mem_sdiff.mpr ⟨he, hei⟩)
      have hc := CatalogueColours.path_cyclic p (f e.1) (x e) (y e) (z e) (f e.2)
        _ _ (hcolour e.1) (hcolour e.2) hh.1 hh.2.1 hh.2.2.1
        (by simpa only [CatalogueColours.colour_toFin] using hAc e he)
      simpa only [blk, PhysicalReplacement.block, hei, ite_false] using hc
  have hLPload : ∀ r, (catalogLoad LP r : ℝ) ≤
      3 * (RootPhysicalEmbedding.factor : ℝ) * t * n :=
    PhysicalCatalogueLoad.load_le lib keep hkeepAll f x y z (CatalogueColours.colour ∘ p)
      hcyc _ hload
  have href : ∀ L ⊆ X, Cycles.Balanced L →
      ∃ Q ⊆ LP, (Q : Set (Finset (V × V))).PairwiseDisjoint id ∧ Q.biUnion id = RP ∪ L := by
    intro L hLX hb
    obtain ⟨Q, hQ, hQdis, hQeq⟩ := hpart L hLX hb
    let S := (RootCatalogueBudget.input X L σ).map (liftArc (RootCatalogueBudget.Vert X σ) U)
    have hQeq' : Q.biUnion id = R0 ∪ S := by
      simpa only [R0, S, map_union, union_assoc] using hQeq
    have hS : S ⊆ I0 := map_subset_map.mpr
      (map_subset_map.mpr (SplitPorts.arcsOf_subset X L))
    have hSkeep : S ⊆ keep := CatalogueReserveSupport.input_subset lib Q R0 I0 S hQ hS hQeq'
    obtain ⟨hsub, hpair, hU⟩ := ReplacementPartition.transport (CatalogueWeights.arcs lib) blk
      hblocks lib Q hQ (fun P hP a ha => mem_biUnion.mpr ⟨P,hP,ha⟩) hQdis
    refine ⟨Q.image (fun P => P.biUnion blk), hsub, hpair, ?_⟩
    calc
      _ = (Q.biUnion id).biUnion blk := hU
      _ = (R0 ∪ S).biUnion blk := by rw [hQeq']
      _ = R0.biUnion blk ∪ S.biUnion blk := union_biUnion
      _ = (CatalogueWeights.arcs lib \ keep).biUnion blk ∪ S.image (arcImage f) := by
        rw [← hE, PhysicalReplacement.input_union keep S hSkeep f x y z]
      _ = RP ∪ L := by rw [hinput L hLX]
  have hRPdeg : ∀ r, (deg RP r : ℝ) ≤ 3 * (RootPhysicalEmbedding.factor : ℝ) * t * n := by
    obtain ⟨Q, hQ, hpair, hU⟩ := href ∅ (empty_subset X) balanced_empty
    rw [union_empty] at hU
    intro r
    have hd : deg RP r ≤ catalogLoad LP r := by
      calc _ = ∑ P ∈ Q, deg P r := by
              rw [← hU]
              exact Hub.deg_biUnion Q id hpair r
        _ ≤ ∑ P ∈ LP, deg P r :=
          sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => Nat.zero_le _)
    have hdr : (deg RP r : ℝ) ≤ (catalogLoad LP r : ℝ) := by exact_mod_cast hd
    exact hdr.trans (hLPload r)
  refine ⟨RP, LP, ?_, ?_, ?_, hRPdeg, ?_, card_image_le.trans hcount, hLPload, href⟩
  · intro a ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    have hp' := (hpath e he).2.2.2
    have hm : a ∈ PhysicalPathArcs.arcs (f e.1) (x e) (y e) (z e) (f e.2) := by
      simpa only [blk, PhysicalReplacement.block, (mem_sdiff.mp he).2, ite_false] using hae
    exact PhysicalPathArcs.supported hp' a hm
  · intro a ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    exact hcyc e (mem_sdiff.mp he).1 a hae
  · rw [disjoint_left]
    intro a ha hax
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    have hm : s(a.1,a.2) ∈ pathEdges (f e.1) (x e) (y e) (z e) (f e.2) := by
      have himg : s(a.1,a.2) ∈ PhysicalPathArcs.forget (blk e) := mem_image.mpr ⟨a,hae,rfl⟩
      simpa only [blk, PhysicalReplacement.forget_block, (mem_sdiff.mp he).2, ite_false] using himg
    exact disjoint_left.mp (havoid e he) hm (mem_image.mpr ⟨a,hax,rfl⟩)
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
    refine ⟨?_, ?_, hbalanced Q hQ⟩
    · intro a ha
      obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
      have heAll : e ∈ CatalogueWeights.arcs lib := mem_biUnion.mpr ⟨Q,hQ,he⟩
      by_cases hei : e ∈ keep
      · have hae' : a = arcImage f e := by simpa [blk, PhysicalReplacement.block, hei, arcImage] using hae
        exact mem_union_right _ (by simpa only [hae'] using hinputMem e hei)
      · exact mem_union_left _ (mem_biUnion.mpr ⟨e,mem_sdiff.mpr ⟨heAll,hei⟩,hae⟩)
    · exact (ReplacementPartition.card_replace_le Q blk 4
        (fun e _ => PhysicalReplacement.card_block keep f x y z e)).trans
          (Nat.mul_le_mul_left 4 (hp Q hQ).2.2.1)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalRefiner

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalRefiner.exists_refiner
