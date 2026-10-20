/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.FastMinimal

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem good_13_0 : GoodRepresentative 69145 := by
  apply goodRepresentative_of_list [0,3,4,9,10,11,16] 69145
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_1 : GoodRepresentative 69146 := by
  apply goodRepresentative_of_list [1,3,4,9,10,11,16] 69146
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_2 : GoodRepresentative 69147 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,11,16] 69147
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_3 : GoodRepresentative 69152 := by
  apply goodRepresentative_of_list [5,9,10,11,16] 69152
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_4 : GoodRepresentative 69168 := by
  apply goodRepresentative_of_list [4,5,9,10,11,16] 69168
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_5 : GoodRepresentative 69248 := by
  apply goodRepresentative_of_list [7,9,10,11,16] 69248
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_6 : GoodRepresentative 69249 := by
  apply goodRepresentative_of_list [0,7,9,10,11,16] 69249
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_7 : GoodRepresentative 69252 := by
  apply goodRepresentative_of_list [2,7,9,10,11,16] 69252
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_8 : GoodRepresentative 69253 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,16] 69253
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_9 : GoodRepresentative 69256 := by
  apply goodRepresentative_of_list [3,7,9,10,11,16] 69256
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_10 : GoodRepresentative 69257 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,16] 69257
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_11 : GoodRepresentative 69260 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,16] 69260
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_12 : GoodRepresentative 69261 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,16] 69261
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_13 : GoodRepresentative 69264 := by
  apply goodRepresentative_of_list [4,7,9,10,11,16] 69264
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_14 : GoodRepresentative 69280 := by
  apply goodRepresentative_of_list [5,7,9,10,11,16] 69280
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_15 : GoodRepresentative 69296 := by
  apply goodRepresentative_of_list [4,5,7,9,10,11,16] 69296
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_16 : GoodRepresentative 69642 := by
  apply goodRepresentative_of_list [1,3,12,16] 69642
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_17 : GoodRepresentative 69643 := by
  apply goodRepresentative_of_list [0,1,3,12,16] 69643
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_18 : GoodRepresentative 69657 := by
  apply goodRepresentative_of_list [0,3,4,12,16] 69657
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_19 : GoodRepresentative 69658 := by
  apply goodRepresentative_of_list [1,3,4,12,16] 69658
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_20 : GoodRepresentative 69659 := by
  apply goodRepresentative_of_list [0,1,3,4,12,16] 69659
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_21 : GoodRepresentative 69706 := by
  apply goodRepresentative_of_list [1,3,6,12,16] 69706
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_22 : GoodRepresentative 69707 := by
  apply goodRepresentative_of_list [0,1,3,6,12,16] 69707
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_23 : GoodRepresentative 69721 := by
  apply goodRepresentative_of_list [0,3,4,6,12,16] 69721
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_24 : GoodRepresentative 69722 := by
  apply goodRepresentative_of_list [1,3,4,6,12,16] 69722
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_25 : GoodRepresentative 69723 := by
  apply goodRepresentative_of_list [0,1,3,4,6,12,16] 69723
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_26 : GoodRepresentative 69765 := by
  apply goodRepresentative_of_list [0,2,7,12,16] 69765
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_27 : GoodRepresentative 69767 := by
  apply goodRepresentative_of_list [0,1,2,7,12,16] 69767
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_28 : GoodRepresentative 69773 := by
  apply goodRepresentative_of_list [0,2,3,7,12,16] 69773
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_29 : GoodRepresentative 69781 := by
  apply goodRepresentative_of_list [0,2,4,7,12,16] 69781
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_30 : GoodRepresentative 69783 := by
  apply goodRepresentative_of_list [0,1,2,4,7,12,16] 69783
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_13_31 : GoodRepresentative 70021 := by
  apply goodRepresentative_of_list [0,2,7,8,12,16] 70021
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks13 : List ℕ := [69145,69146,69147,69152,69168,69248,69249,69252,69253,69256,69257,69260,69261,69264,69280,69296,69642,69643,69657,69658,69659,69706,69707,69721,69722,69723,69765,69767,69773,69781,69783,70021]

theorem checkedMasks13_good : ∀ m ∈ checkedMasks13, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks13, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_13_0
  · exact good_13_1
  · exact good_13_2
  · exact good_13_3
  · exact good_13_4
  · exact good_13_5
  · exact good_13_6
  · exact good_13_7
  · exact good_13_8
  · exact good_13_9
  · exact good_13_10
  · exact good_13_11
  · exact good_13_12
  · exact good_13_13
  · exact good_13_14
  · exact good_13_15
  · exact good_13_16
  · exact good_13_17
  · exact good_13_18
  · exact good_13_19
  · exact good_13_20
  · exact good_13_21
  · exact good_13_22
  · exact good_13_23
  · exact good_13_24
  · exact good_13_25
  · exact good_13_26
  · exact good_13_27
  · exact good_13_28
  · exact good_13_29
  · exact good_13_30
  · exact good_13_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks13_good
