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

theorem good_14_0 : GoodRepresentative 70029 := by
  apply goodRepresentative_of_list [0,2,3,7,8,12,16] 70029
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_1 : GoodRepresentative 70146 := by
  apply goodRepresentative_of_list [1,9,12,16] 70146
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_2 : GoodRepresentative 70147 := by
  apply goodRepresentative_of_list [0,1,9,12,16] 70147
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_3 : GoodRepresentative 70154 := by
  apply goodRepresentative_of_list [1,3,9,12,16] 70154
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_4 : GoodRepresentative 70155 := by
  apply goodRepresentative_of_list [0,1,3,9,12,16] 70155
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_5 : GoodRepresentative 70161 := by
  apply goodRepresentative_of_list [0,4,9,12,16] 70161
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_6 : GoodRepresentative 70163 := by
  apply goodRepresentative_of_list [0,1,4,9,12,16] 70163
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_7 : GoodRepresentative 70168 := by
  apply goodRepresentative_of_list [3,4,9,12,16] 70168
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_8 : GoodRepresentative 70169 := by
  apply goodRepresentative_of_list [0,3,4,9,12,16] 70169
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_9 : GoodRepresentative 70170 := by
  apply goodRepresentative_of_list [1,3,4,9,12,16] 70170
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_10 : GoodRepresentative 70171 := by
  apply goodRepresentative_of_list [0,1,3,4,9,12,16] 70171
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_11 : GoodRepresentative 70210 := by
  apply goodRepresentative_of_list [1,6,9,12,16] 70210
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_12 : GoodRepresentative 70211 := by
  apply goodRepresentative_of_list [0,1,6,9,12,16] 70211
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_13 : GoodRepresentative 70218 := by
  apply goodRepresentative_of_list [1,3,6,9,12,16] 70218
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_14 : GoodRepresentative 70219 := by
  apply goodRepresentative_of_list [0,1,3,6,9,12,16] 70219
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_15 : GoodRepresentative 70225 := by
  apply goodRepresentative_of_list [0,4,6,9,12,16] 70225
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_16 : GoodRepresentative 70227 := by
  apply goodRepresentative_of_list [0,1,4,6,9,12,16] 70227
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_17 : GoodRepresentative 70232 := by
  apply goodRepresentative_of_list [3,4,6,9,12,16] 70232
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_18 : GoodRepresentative 70233 := by
  apply goodRepresentative_of_list [0,3,4,6,9,12,16] 70233
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_19 : GoodRepresentative 70234 := by
  apply goodRepresentative_of_list [1,3,4,6,9,12,16] 70234
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_20 : GoodRepresentative 70235 := by
  apply goodRepresentative_of_list [0,1,3,4,6,9,12,16] 70235
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_21 : GoodRepresentative 70277 := by
  apply goodRepresentative_of_list [0,2,7,9,12,16] 70277
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_22 : GoodRepresentative 70285 := by
  apply goodRepresentative_of_list [0,2,3,7,9,12,16] 70285
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_23 : GoodRepresentative 70288 := by
  apply goodRepresentative_of_list [4,7,9,12,16] 70288
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_24 : GoodRepresentative 70352 := by
  apply goodRepresentative_of_list [4,6,7,9,12,16] 70352
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_25 : GoodRepresentative 70665 := by
  apply goodRepresentative_of_list [0,3,10,12,16] 70665
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_26 : GoodRepresentative 70667 := by
  apply goodRepresentative_of_list [0,1,3,10,12,16] 70667
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_27 : GoodRepresentative 70668 := by
  apply goodRepresentative_of_list [2,3,10,12,16] 70668
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_28 : GoodRepresentative 70669 := by
  apply goodRepresentative_of_list [0,2,3,10,12,16] 70669
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_29 : GoodRepresentative 70683 := by
  apply goodRepresentative_of_list [0,1,3,4,10,12,16] 70683
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_30 : GoodRepresentative 70729 := by
  apply goodRepresentative_of_list [0,3,6,10,12,16] 70729
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_14_31 : GoodRepresentative 70731 := by
  apply goodRepresentative_of_list [0,1,3,6,10,12,16] 70731
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks14 : List ℕ := [70029,70146,70147,70154,70155,70161,70163,70168,70169,70170,70171,70210,70211,70218,70219,70225,70227,70232,70233,70234,70235,70277,70285,70288,70352,70665,70667,70668,70669,70683,70729,70731]

theorem checkedMasks14_good : ∀ m ∈ checkedMasks14, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks14, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_14_0
  · exact good_14_1
  · exact good_14_2
  · exact good_14_3
  · exact good_14_4
  · exact good_14_5
  · exact good_14_6
  · exact good_14_7
  · exact good_14_8
  · exact good_14_9
  · exact good_14_10
  · exact good_14_11
  · exact good_14_12
  · exact good_14_13
  · exact good_14_14
  · exact good_14_15
  · exact good_14_16
  · exact good_14_17
  · exact good_14_18
  · exact good_14_19
  · exact good_14_20
  · exact good_14_21
  · exact good_14_22
  · exact good_14_23
  · exact good_14_24
  · exact good_14_25
  · exact good_14_26
  · exact good_14_27
  · exact good_14_28
  · exact good_14_29
  · exact good_14_30
  · exact good_14_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks14_good
