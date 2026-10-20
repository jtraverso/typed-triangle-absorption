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

theorem good_04_0 : GoodRepresentative 3594 := by decide +kernel

theorem good_04_1 : GoodRepresentative 3595 := by decide +kernel

theorem good_04_2 : GoodRepresentative 3596 := by decide +kernel

theorem good_04_3 : GoodRepresentative 3597 := by decide +kernel

theorem good_04_4 : GoodRepresentative 3601 := by decide +kernel

theorem good_04_5 : GoodRepresentative 3603 := by decide +kernel

theorem good_04_6 : GoodRepresentative 3608 := by decide +kernel

theorem good_04_7 : GoodRepresentative 3609 := by decide +kernel

theorem good_04_8 : GoodRepresentative 3610 := by decide +kernel

theorem good_04_9 : GoodRepresentative 3611 := by decide +kernel

theorem good_04_10 : GoodRepresentative 3712 := by decide +kernel

theorem good_04_11 : GoodRepresentative 3713 := by decide +kernel

theorem good_04_12 : GoodRepresentative 3716 := by decide +kernel

theorem good_04_13 : GoodRepresentative 3717 := by decide +kernel

theorem good_04_14 : GoodRepresentative 3720 := by decide +kernel

theorem good_04_15 : GoodRepresentative 3721 := by decide +kernel

theorem good_04_16 : GoodRepresentative 3724 := by decide +kernel

theorem good_04_17 : GoodRepresentative 3725 := by decide +kernel

theorem good_04_18 : GoodRepresentative 3728 := by decide +kernel

theorem good_04_19 : GoodRepresentative 3744 := by decide +kernel

theorem good_04_20 : GoodRepresentative 3760 := by decide +kernel

theorem good_04_21 : GoodRepresentative 3841 := by decide +kernel

theorem good_04_22 : GoodRepresentative 3844 := by decide +kernel

theorem good_04_23 : GoodRepresentative 3845 := by decide +kernel

theorem good_04_24 : GoodRepresentative 3848 := by decide +kernel

theorem good_04_25 : GoodRepresentative 3849 := by decide +kernel

theorem good_04_26 : GoodRepresentative 3852 := by decide +kernel

theorem good_04_27 : GoodRepresentative 3853 := by decide +kernel

theorem good_04_28 : GoodRepresentative 3856 := by decide +kernel

theorem good_04_29 : GoodRepresentative 3872 := by decide +kernel

theorem good_04_30 : GoodRepresentative 3888 := by decide +kernel

theorem good_04_31 : GoodRepresentative 6156 := by decide +kernel

def checkedMasks04 : List ℕ := [3594,3595,3596,3597,3601,3603,3608,3609,3610,3611,3712,3713,3716,3717,3720,3721,3724,3725,3728,3744,3760,3841,3844,3845,3848,3849,3852,3853,3856,3872,3888,6156]

theorem checkedMasks04_good : ∀ m ∈ checkedMasks04, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks04, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_04_0
  · exact good_04_1
  · exact good_04_2
  · exact good_04_3
  · exact good_04_4
  · exact good_04_5
  · exact good_04_6
  · exact good_04_7
  · exact good_04_8
  · exact good_04_9
  · exact good_04_10
  · exact good_04_11
  · exact good_04_12
  · exact good_04_13
  · exact good_04_14
  · exact good_04_15
  · exact good_04_16
  · exact good_04_17
  · exact good_04_18
  · exact good_04_19
  · exact good_04_20
  · exact good_04_21
  · exact good_04_22
  · exact good_04_23
  · exact good_04_24
  · exact good_04_25
  · exact good_04_26
  · exact good_04_27
  · exact good_04_28
  · exact good_04_29
  · exact good_04_30
  · exact good_04_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks04_good
