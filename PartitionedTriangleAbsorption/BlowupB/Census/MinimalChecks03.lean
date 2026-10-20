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

theorem good_03_0 : GoodRepresentative 2817 := by decide +kernel

theorem good_03_1 : GoodRepresentative 2821 := by decide +kernel

theorem good_03_2 : GoodRepresentative 2824 := by decide +kernel

theorem good_03_3 : GoodRepresentative 2825 := by decide +kernel

theorem good_03_4 : GoodRepresentative 2828 := by decide +kernel

theorem good_03_5 : GoodRepresentative 2829 := by decide +kernel

theorem good_03_6 : GoodRepresentative 2832 := by decide +kernel

theorem good_03_7 : GoodRepresentative 2848 := by decide +kernel

theorem good_03_8 : GoodRepresentative 2864 := by decide +kernel

theorem good_03_9 : GoodRepresentative 3081 := by decide +kernel

theorem good_03_10 : GoodRepresentative 3083 := by decide +kernel

theorem good_03_11 : GoodRepresentative 3084 := by decide +kernel

theorem good_03_12 : GoodRepresentative 3085 := by decide +kernel

theorem good_03_13 : GoodRepresentative 3099 := by decide +kernel

theorem good_03_14 : GoodRepresentative 3208 := by decide +kernel

theorem good_03_15 : GoodRepresentative 3209 := by decide +kernel

theorem good_03_16 : GoodRepresentative 3212 := by decide +kernel

theorem good_03_17 : GoodRepresentative 3213 := by decide +kernel

theorem good_03_18 : GoodRepresentative 3329 := by decide +kernel

theorem good_03_19 : GoodRepresentative 3333 := by decide +kernel

theorem good_03_20 : GoodRepresentative 3336 := by decide +kernel

theorem good_03_21 : GoodRepresentative 3337 := by decide +kernel

theorem good_03_22 : GoodRepresentative 3340 := by decide +kernel

theorem good_03_23 : GoodRepresentative 3341 := by decide +kernel

theorem good_03_24 : GoodRepresentative 3344 := by decide +kernel

theorem good_03_25 : GoodRepresentative 3376 := by decide +kernel

theorem good_03_26 : GoodRepresentative 3585 := by decide +kernel

theorem good_03_27 : GoodRepresentative 3587 := by decide +kernel

theorem good_03_28 : GoodRepresentative 3588 := by decide +kernel

theorem good_03_29 : GoodRepresentative 3589 := by decide +kernel

theorem good_03_30 : GoodRepresentative 3592 := by decide +kernel

theorem good_03_31 : GoodRepresentative 3593 := by decide +kernel

def checkedMasks03 : List ℕ := [2817,2821,2824,2825,2828,2829,2832,2848,2864,3081,3083,3084,3085,3099,3208,3209,3212,3213,3329,3333,3336,3337,3340,3341,3344,3376,3585,3587,3588,3589,3592,3593]

theorem checkedMasks03_good : ∀ m ∈ checkedMasks03, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks03, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_03_0
  · exact good_03_1
  · exact good_03_2
  · exact good_03_3
  · exact good_03_4
  · exact good_03_5
  · exact good_03_6
  · exact good_03_7
  · exact good_03_8
  · exact good_03_9
  · exact good_03_10
  · exact good_03_11
  · exact good_03_12
  · exact good_03_13
  · exact good_03_14
  · exact good_03_15
  · exact good_03_16
  · exact good_03_17
  · exact good_03_18
  · exact good_03_19
  · exact good_03_20
  · exact good_03_21
  · exact good_03_22
  · exact good_03_23
  · exact good_03_24
  · exact good_03_25
  · exact good_03_26
  · exact good_03_27
  · exact good_03_28
  · exact good_03_29
  · exact good_03_30
  · exact good_03_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks03_good
