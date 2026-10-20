/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelAssembly

@[expose] public section

/-! A single fixed edge-disjoint replacement transports every partition of a
catalogue. The blocks can be physical paths or retained singleton input arcs. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.ReplacementPartition

open Finset

variable {E A : Type} [DecidableEq E] [DecidableEq A]

theorem disjoint_replace (all P Q : Finset E) (block : E → Finset A)
    (hblocks : (all : Set E).PairwiseDisjoint block)
    (hP : P ⊆ all) (hQ : Q ⊆ all) (hPQ : Disjoint P Q) :
    Disjoint (P.biUnion block) (Q.biUnion block) := by
  rw [disjoint_left]
  intro a ha hb
  obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
  obtain ⟨f, hf, haf⟩ := mem_biUnion.mp hb
  have hne : e ≠ f := by
    intro h
    subst f
    exact disjoint_left.mp hPQ he hf
  exact disjoint_left.mp (hblocks (hP he) (hQ hf) hne) hae haf

theorem union_replace (Q : Finset (Finset E)) (block : E → Finset A) :
    (Q.image (fun P => P.biUnion block)).biUnion id = (Q.biUnion id).biUnion block := by
  ext a
  constructor
  · intro ha
    obtain ⟨B, hB, haB⟩ := mem_biUnion.mp ha
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hB
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp haB
    exact mem_biUnion.mpr ⟨e, mem_biUnion.mpr ⟨P, hP, he⟩, hae⟩
  · intro ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    obtain ⟨P, hP, heP⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨P.biUnion block, mem_image.mpr ⟨P, hP, rfl⟩,
      mem_biUnion.mpr ⟨e, heP, hae⟩⟩

theorem transport (all : Finset E) (block : E → Finset A)
    (hblocks : (all : Set E).PairwiseDisjoint block)
    (lib Q : Finset (Finset E)) (hQ : Q ⊆ lib)
    (hsupport : ∀ P ∈ lib, P ⊆ all)
    (hpart : (Q : Set (Finset E)).PairwiseDisjoint id) :
    Q.image (fun P => P.biUnion block) ⊆ lib.image (fun P => P.biUnion block) ∧
    ((Q.image (fun P => P.biUnion block)) : Set (Finset A)).PairwiseDisjoint id ∧
    (Q.image (fun P => P.biUnion block)).biUnion id = (Q.biUnion id).biUnion block := by
  refine ⟨image_subset_image hQ, ?_, union_replace Q block⟩
  intro B hB D hD hBD
  obtain ⟨P, hP, rfl⟩ := mem_image.mp hB
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hD
  have hPT : P ≠ T := fun h => hBD (congrArg (fun P => P.biUnion block) h)
  exact disjoint_replace all P T block hblocks (hsupport P (hQ hP))
    (hsupport T (hQ hT)) (hpart hP hT hPT)

theorem card_replace_le (P : Finset E) (block : E → Finset A) (k : ℕ)
    (h : ∀ e ∈ P, (block e).card ≤ k) : (P.biUnion block).card ≤ k * P.card := by
  calc
    _ ≤ ∑ e ∈ P, (block e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ P, k := sum_le_sum h
    _ = _ := by simp [mul_comm]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.ReplacementPartition

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ReplacementPartition.transport
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.ReplacementPartition.card_replace_le
