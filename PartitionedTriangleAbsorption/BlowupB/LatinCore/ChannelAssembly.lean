/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLift

@[expose] public section

/-! Assemble the selected mesoscopic pieces and the unused channel paths in
one fixed catalogue. The latter become balanced only after root identification.
This module does not assume or assert a physical embedding into the host. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelAssembly

open Finset Cycles

variable {W : Type} [DecidableEq W]

theorem partition_union (Q T : Finset (Finset W))
    (hQ : (Q : Set (Finset W)).PairwiseDisjoint id)
    (hT : (T : Set (Finset W)).PairwiseDisjoint id)
    (hdis : Disjoint (Q.biUnion id) (T.biUnion id)) :
    ((Q ∪ T : Finset (Finset W)) : Set (Finset W)).PairwiseDisjoint id := by
  intro A hA B hB hne
  rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
  · exact hQ hA hB hne
  · exact hdis.mono (subset_biUnion_of_mem id hA) (subset_biUnion_of_mem id hB)
  · exact hdis.symm.mono (subset_biUnion_of_mem id hA) (subset_biUnion_of_mem id hB)
  · exact hT hA hB hne

theorem map_partition {Z : Type} [DecidableEq Z] (f : W ↪ Z)
    (Q : Finset (Finset W)) (hQ : (Q : Set (Finset W)).PairwiseDisjoint id) :
    ((Q.image (fun P => P.map f)) : Set (Finset Z)).PairwiseDisjoint id := by
  intro A hA B hB hne
  obtain ⟨P, hP, rfl⟩ := mem_image.mp hA
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hB
  have hPT : P ≠ T := fun h => hne (congrArg (fun P => P.map f) h)
  exact (disjoint_map f).mpr (hQ hP hT hPT)

theorem map_union {Z : Type} [DecidableEq Z] (f : W ↪ Z)
    (Q : Finset (Finset W)) :
    (Q.image (fun P => P.map f)).biUnion id = (Q.biUnion id).map f := by
  ext z
  constructor
  · intro hz
    obtain ⟨A, hA, hzA⟩ := mem_biUnion.mp hz
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hA
    obtain ⟨w, hw, hwz⟩ := mem_map.mp hzA
    exact mem_map.mpr ⟨w, mem_biUnion.mpr ⟨P, hP, hw⟩, hwz⟩
  · intro hz
    obtain ⟨w, hw, hwz⟩ := mem_map.mp hz
    obtain ⟨P, hP, hwP⟩ := mem_biUnion.mp hw
    exact mem_biUnion.mpr ⟨P.map f, mem_image.mpr ⟨P, hP, rfl⟩,
      mem_map.mpr ⟨w, hwP, hwz⟩⟩

/-- A mesoscopic partition of the completed demand, together with the unused
channels, partitions the SAME fixed reserve plus the original split demand. -/
theorem complete_partition {Z : Type} [DecidableEq Z] (f : W ↪ Z)
    (N I A : Finset W) (hAN : A ⊆ N) (hNI : Disjoint N I)
    (paths unused : Finset (Finset W)) (hsub : unused ⊆ paths)
    (hpair : (unused : Set (Finset W)).PairwiseDisjoint id) (heq : unused.biUnion id = N \ A)
    (R : Finset Z) (hRN : Disjoint R (N.map f))
    (lib Q : Finset (Finset Z))
    (hQlib : Q ⊆ lib)
    (hQdis : (Q : Set (Finset Z)).PairwiseDisjoint id)
    (hQeq : Q.biUnion id = R ∪ (A ∪ I).map f) :
    ∃ T : Finset (Finset Z), T ⊆ lib ∪ paths.image (fun P => P.map f) ∧
      (T : Set (Finset Z)).PairwiseDisjoint id ∧
      T.biUnion id = R ∪ (N ∪ I).map f := by
  let extra := unused.image (fun P => P.map f)
  have hextra : extra.biUnion id = (N \ A).map f := by
    rw [map_union, heq]
  have hdis : Disjoint (Q.biUnion id) (extra.biUnion id) := by
    rw [hQeq, hextra]
    apply disjoint_union_left.mpr
    refine ⟨hRN.mono_right (map_subset_map.mpr sdiff_subset), ?_⟩
    apply (disjoint_map f).mpr
    apply disjoint_union_left.mpr
    refine ⟨disjoint_sdiff_self_right, ?_⟩
    exact hNI.symm.mono_right sdiff_subset
  refine ⟨Q ∪ extra, union_subset (hQlib.trans subset_union_left) ?_,
    partition_union Q extra hQdis (map_partition f unused hpair) hdis, ?_⟩
  · exact (image_subset_image hsub).trans subset_union_right
  · have hsets : (A ∪ I) ∪ (N \ A) = N ∪ I := by
      ext e
      simp only [mem_union, mem_sdiff]
      have hh : e ∈ A → e ∈ N := fun h => hAN h
      tauto
    rw [union_biUnion, hQeq, hextra, union_assoc, ← Finset.map_union, hsets]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelAssembly

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelAssembly.complete_partition
