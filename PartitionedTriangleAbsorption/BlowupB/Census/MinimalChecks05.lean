/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Uniqueness

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem good_05_0 : GoodRepresentative 6157 := by decide +kernel

theorem good_05_1 : GoodRepresentative 6273 := by decide +kernel

theorem good_05_2 : GoodRepresentative 6277 := by decide +kernel

theorem good_05_3 : GoodRepresentative 6280 := by decide +kernel

theorem good_05_4 : GoodRepresentative 6281 := by decide +kernel

theorem good_05_5 : GoodRepresentative 6284 := by decide +kernel

theorem good_05_6 : GoodRepresentative 6285 := by decide +kernel

theorem good_05_7 : GoodRepresentative 6401 := by decide +kernel

theorem good_05_8 : GoodRepresentative 6405 := by decide +kernel

theorem good_05_9 : GoodRepresentative 6412 := by decide +kernel

theorem good_05_10 : GoodRepresentative 6413 := by decide +kernel

theorem good_05_11 : GoodRepresentative 6784 := by decide +kernel

theorem good_05_12 : GoodRepresentative 6785 := by decide +kernel

theorem good_05_13 : GoodRepresentative 6788 := by decide +kernel

theorem good_05_14 : GoodRepresentative 6789 := by decide +kernel

theorem good_05_15 : GoodRepresentative 6796 := by decide +kernel

theorem good_05_16 : GoodRepresentative 6797 := by decide +kernel

theorem good_05_17 : GoodRepresentative 7181 := by decide +kernel

theorem good_05_18 : GoodRepresentative 7297 := by decide +kernel

theorem good_05_19 : GoodRepresentative 7301 := by decide +kernel

theorem good_05_20 : GoodRepresentative 7304 := by decide +kernel

theorem good_05_21 : GoodRepresentative 7305 := by decide +kernel

theorem good_05_22 : GoodRepresentative 7308 := by decide +kernel

theorem good_05_23 : GoodRepresentative 7309 := by decide +kernel

theorem good_05_24 : GoodRepresentative 7425 := by decide +kernel

theorem good_05_25 : GoodRepresentative 7429 := by decide +kernel

theorem good_05_26 : GoodRepresentative 7436 := by decide +kernel

theorem good_05_27 : GoodRepresentative 7437 := by decide +kernel

theorem good_05_28 : GoodRepresentative 7808 := by decide +kernel

theorem good_05_29 : GoodRepresentative 7809 := by decide +kernel

theorem good_05_30 : GoodRepresentative 7812 := by decide +kernel

theorem good_05_31 : GoodRepresentative 7813 := by decide +kernel

def checkedMasks05 : List ℕ := [6157,6273,6277,6280,6281,6284,6285,6401,6405,6412,6413,6784,6785,6788,6789,6796,6797,7181,7297,7301,7304,7305,7308,7309,7425,7429,7436,7437,7808,7809,7812,7813]

theorem checkedMasks05_good : ∀ m ∈ checkedMasks05, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks05, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_05_0
  · exact good_05_1
  · exact good_05_2
  · exact good_05_3
  · exact good_05_4
  · exact good_05_5
  · exact good_05_6
  · exact good_05_7
  · exact good_05_8
  · exact good_05_9
  · exact good_05_10
  · exact good_05_11
  · exact good_05_12
  · exact good_05_13
  · exact good_05_14
  · exact good_05_15
  · exact good_05_16
  · exact good_05_17
  · exact good_05_18
  · exact good_05_19
  · exact good_05_20
  · exact good_05_21
  · exact good_05_22
  · exact good_05_23
  · exact good_05_24
  · exact good_05_25
  · exact good_05_26
  · exact good_05_27
  · exact good_05_28
  · exact good_05_29
  · exact good_05_30
  · exact good_05_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks05_good
