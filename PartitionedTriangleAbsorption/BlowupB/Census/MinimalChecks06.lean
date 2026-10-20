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

theorem good_06_0 : GoodRepresentative 7820 := by decide +kernel

theorem good_06_1 : GoodRepresentative 7821 := by decide +kernel

theorem good_06_2 : GoodRepresentative 9352 := by decide +kernel

theorem good_06_3 : GoodRepresentative 9353 := by decide +kernel

theorem good_06_4 : GoodRepresentative 9356 := by decide +kernel

theorem good_06_5 : GoodRepresentative 9357 := by decide +kernel

theorem good_06_6 : GoodRepresentative 9729 := by decide +kernel

theorem good_06_7 : GoodRepresentative 9731 := by decide +kernel

theorem good_06_8 : GoodRepresentative 9732 := by decide +kernel

theorem good_06_9 : GoodRepresentative 9733 := by decide +kernel

theorem good_06_10 : GoodRepresentative 9736 := by decide +kernel

theorem good_06_11 : GoodRepresentative 9737 := by decide +kernel

theorem good_06_12 : GoodRepresentative 9738 := by decide +kernel

theorem good_06_13 : GoodRepresentative 9739 := by decide +kernel

theorem good_06_14 : GoodRepresentative 9740 := by decide +kernel

theorem good_06_15 : GoodRepresentative 9741 := by decide +kernel

theorem good_06_16 : GoodRepresentative 9747 := by decide +kernel

theorem good_06_17 : GoodRepresentative 9752 := by decide +kernel

theorem good_06_18 : GoodRepresentative 9753 := by decide +kernel

theorem good_06_19 : GoodRepresentative 9754 := by decide +kernel

theorem good_06_20 : GoodRepresentative 9755 := by decide +kernel

theorem good_06_21 : GoodRepresentative 9856 := by decide +kernel

theorem good_06_22 : GoodRepresentative 9857 := by decide +kernel

theorem good_06_23 : GoodRepresentative 9860 := by decide +kernel

theorem good_06_24 : GoodRepresentative 9861 := by decide +kernel

theorem good_06_25 : GoodRepresentative 9864 := by decide +kernel

theorem good_06_26 : GoodRepresentative 9865 := by decide +kernel

theorem good_06_27 : GoodRepresentative 9868 := by decide +kernel

theorem good_06_28 : GoodRepresentative 9869 := by decide +kernel

theorem good_06_29 : GoodRepresentative 9872 := by decide +kernel

theorem good_06_30 : GoodRepresentative 9888 := by decide +kernel

theorem good_06_31 : GoodRepresentative 9904 := by decide +kernel

def checkedMasks06 : List ℕ := [7820,7821,9352,9353,9356,9357,9729,9731,9732,9733,9736,9737,9738,9739,9740,9741,9747,9752,9753,9754,9755,9856,9857,9860,9861,9864,9865,9868,9869,9872,9888,9904]

theorem checkedMasks06_good : ∀ m ∈ checkedMasks06, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks06, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_06_0
  · exact good_06_1
  · exact good_06_2
  · exact good_06_3
  · exact good_06_4
  · exact good_06_5
  · exact good_06_6
  · exact good_06_7
  · exact good_06_8
  · exact good_06_9
  · exact good_06_10
  · exact good_06_11
  · exact good_06_12
  · exact good_06_13
  · exact good_06_14
  · exact good_06_15
  · exact good_06_16
  · exact good_06_17
  · exact good_06_18
  · exact good_06_19
  · exact good_06_20
  · exact good_06_21
  · exact good_06_22
  · exact good_06_23
  · exact good_06_24
  · exact good_06_25
  · exact good_06_26
  · exact good_06_27
  · exact good_06_28
  · exact good_06_29
  · exact good_06_30
  · exact good_06_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks06_good
