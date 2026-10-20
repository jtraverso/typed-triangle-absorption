/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks00
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks01
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks02
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks03
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks04
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks05
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks06
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks07
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks08
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks09
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks10
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks11
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks12
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks13
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks14
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks15
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks16
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks17
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks18
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks19
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks20
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks21
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks22
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks23

@[expose] public section

set_option maxRecDepth 100000

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem checkedMasks_append :
    checkedMasks00 ++ checkedMasks01 ++ checkedMasks02 ++ checkedMasks03 ++ checkedMasks04 ++ checkedMasks05 ++ checkedMasks06 ++ checkedMasks07 ++ checkedMasks08 ++ checkedMasks09 ++ checkedMasks10 ++ checkedMasks11 ++ checkedMasks12 ++ checkedMasks13 ++ checkedMasks14 ++ checkedMasks15 ++ checkedMasks16 ++ checkedMasks17 ++ checkedMasks18 ++ checkedMasks19 ++ checkedMasks20 ++ checkedMasks21 ++ checkedMasks22 ++ checkedMasks23 = representativeMasks := rfl

theorem representative_good (m : ℕ) (hm : m ∈ representativeMasks) :
    GoodRepresentative m := by
  have hall : ∀ a ∈ (checkedMasks00 ++ checkedMasks01 ++ checkedMasks02 ++ checkedMasks03 ++ checkedMasks04 ++ checkedMasks05 ++ checkedMasks06 ++ checkedMasks07 ++ checkedMasks08 ++ checkedMasks09 ++ checkedMasks10 ++ checkedMasks11 ++ checkedMasks12 ++ checkedMasks13 ++ checkedMasks14 ++ checkedMasks15 ++ checkedMasks16 ++ checkedMasks17 ++ checkedMasks18 ++ checkedMasks19 ++ checkedMasks20 ++ checkedMasks21 ++ checkedMasks22 ++ checkedMasks23), GoodRepresentative a :=
    List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨checkedMasks00_good, checkedMasks01_good⟩, checkedMasks02_good⟩, checkedMasks03_good⟩, checkedMasks04_good⟩, checkedMasks05_good⟩, checkedMasks06_good⟩, checkedMasks07_good⟩, checkedMasks08_good⟩, checkedMasks09_good⟩, checkedMasks10_good⟩, checkedMasks11_good⟩, checkedMasks12_good⟩, checkedMasks13_good⟩, checkedMasks14_good⟩, checkedMasks15_good⟩, checkedMasks16_good⟩, checkedMasks17_good⟩, checkedMasks18_good⟩, checkedMasks19_good⟩, checkedMasks20_good⟩, checkedMasks21_good⟩, checkedMasks22_good⟩, checkedMasks23_good⟩
  rw [checkedMasks_append] at hall
  exact hall m hm

theorem representative_unique (m n : ℕ)
    (hm : m ∈ representativeMasks) (hn : n ∈ representativeMasks)
    (s : Equiv.Perm (Fin 4))
    (h : decode (decodeMask n) =
      (decode (decodeMask m)).image (Multiset.map s)) : m = n := by
  obtain ⟨_, hmr, hml⟩ := representative_good m hm
  obtain ⟨_, hnr, hnl⟩ := representative_good n hn
  have he := least_orbit_unique (decodeMask m) (decodeMask n) hml hnl s h
  simpa only [hmr, hnr] using congrArg familyMask he

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.representative_good
#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.representative_unique
