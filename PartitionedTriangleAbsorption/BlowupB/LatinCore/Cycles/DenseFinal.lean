/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseAssembly
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.GreedyPartition

@[expose] public section

/-!
# `DenseRefiner → MesoscopicRefiner`

The exact remaining lemma of the mesoscopic producer is the dense hub-level refiner
`DenseRefiner` (`DenseSpec.lean`, OPEN).  This file proves, without `sorry`, that it implies the
primary target `MesoscopicRefiner`, with explicit constants:

* `C' = denseConst C goodConst`, `K' = max 9 K`.

Proof: if `Y = ∅` the empty reserve and empty library work (`mesoscopicFor_empty`); otherwise the
greedy good hub partition (`Greedy.hasGoodPartition`) feeds the hub-level assembly
(`mesoscopicFor_of_dense`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open DenseRed MesoCutHub

/-- Explicit-constant form of the reduction. -/
theorem mesoscopicRefinerWith_of_denseRefinerWith (C K : ℕ) (hD : DenseRefinerWith C K) :
    MesoscopicRefinerWith (denseConst C Greedy.goodConst) (max 9 K) := by
  rw [mesoscopicRefinerWith_iff]
  intro V _ _ c Y hY hdeg
  rcases Y.eq_empty_or_nonempty with rfl | hne
  · exact mesoscopicFor_empty _ _ V c
  · exact mesoscopicFor_of_dense C K _ hD V c Y hY hdeg (Greedy.hasGoodPartition c Y hY hdeg hne)

/-- **Reduction of the primary target to the dense hub-level refiner.** -/
theorem mesoscopicRefiner_of_denseRefiner (h : DenseRefiner) : MesoscopicRefiner := by
  obtain ⟨C, K, -, -, hD⟩ := h
  refine ⟨denseConst C Greedy.goodConst, max 9 K, ?_, ?_,
    mesoscopicRefinerWith_of_denseRefinerWith C K hD⟩
  · unfold denseConst; omega
  · omega

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
