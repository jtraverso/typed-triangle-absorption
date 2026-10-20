/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalPathArcs
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.PhysicalTransport

@[expose] public section

/-! A fixed physical replacement retains the input arcs and substitutes
every other catalogue arc by its constructed four-edge path. Its blocks
are disjoint and have the correct net incidence. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalReplacement

open Finset Cycles Positivization PaddedNoCommon PhysicalPathArcs

variable {A V : Type} [DecidableEq A] [DecidableEq V]

def block (I : Finset (A × A)) (f : A → V) (x y z : (A × A) → V)
    (e : A × A) : Finset (V × V) :=
  if e ∈ I then {(f e.1, f e.2)} else PhysicalPathArcs.arcs (f e.1) (x e) (y e) (z e) (f e.2)

theorem forget_block (I : Finset (A × A)) (f : A → V) (x y z : (A × A) → V)
    (e : A × A) :
    forget (block I f x y z e) =
      if e ∈ I then {s(f e.1,f e.2)} else pathEdges (f e.1) (x e) (y e) (z e) (f e.2) := by
  by_cases he : e ∈ I
  · simp [block, he, forget]
  · simp only [block, he, ite_false, PhysicalPathArcs.symImage_eq]

theorem card_block (I : Finset (A × A)) (f : A → V) (x y z : (A × A) → V)
    (e : A × A) : (block I f x y z e).card ≤ 4 := by
  by_cases he : e ∈ I
  · simp [block, he]
  · simpa only [block, he, ite_false] using PhysicalPathArcs.card_le (f e.1) (x e) (y e) (z e) (f e.2)

theorem blocks_disjoint (all I : Finset (A × A))
    (f : A → V) (x y z : (A × A) → V) (X : Finset (Sym2 V))
    (hinj : Set.InjOn (arcImage f) (I : Set (A × A)))
    (hinX : ∀ e ∈ I, s(f e.1,f e.2) ∈ X)
    (havoid : ∀ e ∈ all \ I,
      Disjoint (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) X)
    (hpaths : ∀ e ∈ all \ I, ∀ q ∈ all \ I, e ≠ q →
      Disjoint (pathEdges (f e.1) (x e) (y e) (z e) (f e.2))
        (pathEdges (f q.1) (x q) (y q) (z q) (f q.2))) :
    (all : Set (A × A)).PairwiseDisjoint (block I f x y z) := by
  intro e he q hq heq
  change Disjoint (block I f x y z e) (block I f x y z q)
  by_cases hei : e ∈ I <;> by_cases hqi : q ∈ I
  · rw [disjoint_left]
    intro a hae haq
    have hea : a = arcImage f e := by simpa [block, hei, arcImage] using hae
    have hqa : a = arcImage f q := by simpa [block, hqi, arcImage] using haq
    exact heq (hinj hei hqi (hea.symm.trans hqa))
  · apply PhysicalPathArcs.disjoint_of_sym
    rw [forget_block, forget_block]
    simp only [hei, hqi, ite_true, ite_false]
    exact (havoid q (mem_sdiff.mpr ⟨hq, hqi⟩)).symm.mono_left
      (singleton_subset_iff.mpr (hinX e hei))
  · apply PhysicalPathArcs.disjoint_of_sym
    rw [forget_block, forget_block]
    simp only [hei, hqi, ite_true, ite_false]
    exact (havoid e (mem_sdiff.mpr ⟨he, hei⟩)).mono_right
      (singleton_subset_iff.mpr (hinX q hqi))
  · apply PhysicalPathArcs.disjoint_of_sym
    rw [forget_block, forget_block]
    simp only [hei, hqi, ite_false]
    exact hpaths e (mem_sdiff.mpr ⟨he, hei⟩) q (mem_sdiff.mpr ⟨hq, hqi⟩) heq

theorem net_block (all I : Finset (A × A)) (f : A → V) (x y z : (A × A) → V)
    (G : SimpleGraph V)
    (hpath : ∀ e ∈ all \ I, IsPath4 G (f e.1) (x e) (y e) (z e) (f e.2)) :
    ∀ e ∈ all, ∀ r, net (block I f x y z e) r =
      (if f e.2 = r then 1 else 0) - (if f e.1 = r then 1 else 0) := by
  intro e he r
  by_cases hi : e ∈ I
  · simpa only [block, hi, ite_true] using PhysicalPathArcs.singleton_net (f e.1) (f e.2) r
  · simpa only [block, hi, ite_false] using
      PhysicalPathArcs.net_eq (hpath e (mem_sdiff.mpr ⟨he, hi⟩)) r

theorem input_union (I S : Finset (A × A)) (hS : S ⊆ I)
    (f : A → V) (x y z : (A × A) → V) :
    S.biUnion (block I f x y z) = S.image (arcImage f) := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    have heq : a = arcImage f e := by simpa [block, hS he, arcImage] using hae
    exact mem_image.mpr ⟨e, he, heq.symm⟩
  · intro ha
    obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    exact mem_biUnion.mpr ⟨e, he, by simp [block, hS he, arcImage]⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalReplacement

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalReplacement.blocks_disjoint
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalReplacement.net_block
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalReplacement.input_union
