/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.Main

@[expose] public section

/-! The proved dense producer supplies a single mesoscopic witness with both the
square-root global load and the linear original-vertex load. No producer is a premise. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Cycles Cycles.DenseRed Cycles.MesoCutHub

theorem rootedMesoscopicFor
    (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V))
    (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17) :
    RootedMesoscopicFor (denseConst Cdense Greedy.goodConst) 20 c Y := by
  classical
  rcases Y.eq_empty_or_nonempty with rfl | hne
  · refine ⟨Empty, inferInstance, inferInstance, Empty.elim, ∅, ∅, by simp [IsCyc],
      by simp, by simp, by simp, by simp [catalogLoad], ?_, ?_⟩
    · intro L hL _
      have : L = ∅ := Finset.subset_empty.1 hL
      subst this
      exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · simp [catalogLoad]
  · exact rootedMesoscopicFor_of_dense Cdense 20 Greedy.goodConst denseRefinerWith
      V c Y hY hdeg (Greedy.hasGoodPartition c Y hY hdeg hne)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
