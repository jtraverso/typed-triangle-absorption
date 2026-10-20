/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue00
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue01
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue02
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue03
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue04
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue05
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue06
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue07
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue08
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue09
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue10
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue11
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue12
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue13
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue14
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue15
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue16
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue17
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue18
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue19
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue20
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue21
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue22
public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedCatalogue23
public import PartitionedTriangleAbsorption.BlowupB.Census.Complete

@[expose] public section

set_option maxRecDepth 100000

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

/-- The numerical representative is carried to a genuinely closed family. -/
theorem representative_closed765 (m : ℕ) (hm : m ∈ representativeMasks) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  have hall : ∀ a ∈ (checkedMasks00 ++ checkedMasks01 ++ checkedMasks02 ++ checkedMasks03 ++ checkedMasks04 ++ checkedMasks05 ++ checkedMasks06 ++ checkedMasks07 ++ checkedMasks08 ++ checkedMasks09 ++ checkedMasks10 ++ checkedMasks11 ++ checkedMasks12 ++ checkedMasks13 ++ checkedMasks14 ++ checkedMasks15 ++ checkedMasks16 ++ checkedMasks17 ++ checkedMasks18 ++ checkedMasks19 ++ checkedMasks20 ++ checkedMasks21 ++ checkedMasks22 ++ checkedMasks23), ∃ s : Equiv.Perm (Fin 4), Closed765 ((decode (decodeMask a)).image (Multiset.map s)) :=
    List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨checkedMasks00_closed, checkedMasks01_closed⟩, checkedMasks02_closed⟩, checkedMasks03_closed⟩, checkedMasks04_closed⟩, checkedMasks05_closed⟩, checkedMasks06_closed⟩, checkedMasks07_closed⟩, checkedMasks08_closed⟩, checkedMasks09_closed⟩, checkedMasks10_closed⟩, checkedMasks11_closed⟩, checkedMasks12_closed⟩, checkedMasks13_closed⟩, checkedMasks14_closed⟩, checkedMasks15_closed⟩, checkedMasks16_closed⟩, checkedMasks17_closed⟩, checkedMasks18_closed⟩, checkedMasks19_closed⟩, checkedMasks20_closed⟩, checkedMasks21_closed⟩, checkedMasks22_closed⟩, checkedMasks23_closed⟩
  rw [checkedMasks_append] at hall
  exact hall m hm

/-- Coverage by the actual existing construction predicate, up to relabelling.
This does not incorrectly assert that Closed765 itself is invariant under S4. -/
theorem admissible_has_closed765_relabelling (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, τ.card = 3)
    (hused : ∀ a : Fin 4, ∃ τ ∈ F, a ∈ τ)
    (hforbidden : ∀ a : Fin 4, ∃ b : Fin 4,
      ¬ ∃ z : Fin 4, ({a,b,z} : Multiset (Fin 4)) ∈ F) :
    ∃ s : Equiv.Perm (Fin 4), Closed765 (F.image (Multiset.map s)) := by
  obtain ⟨m, hm, s, hs⟩ := family_has_representative F hcard hused hforbidden
  obtain ⟨t, ht⟩ := representative_closed765 m hm
  refine ⟨s.trans t, ?_⟩
  simpa [hs, Finset.image_image, Multiset.map_map, Function.comp_def] using ht

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.representative_closed765
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.admissible_has_closed765_relabelling
