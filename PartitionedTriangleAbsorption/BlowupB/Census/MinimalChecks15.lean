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

theorem good_15_0 : GoodRepresentative 70747 := by
  apply goodRepresentative_of_list [0,1,3,4,6,10,12,16] 70747
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_1 : GoodRepresentative 70789 := by
  apply goodRepresentative_of_list [0,2,7,10,12,16] 70789
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_2 : GoodRepresentative 70791 := by
  apply goodRepresentative_of_list [0,1,2,7,10,12,16] 70791
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_3 : GoodRepresentative 70792 := by
  apply goodRepresentative_of_list [3,7,10,12,16] 70792
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_4 : GoodRepresentative 70793 := by
  apply goodRepresentative_of_list [0,3,7,10,12,16] 70793
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_5 : GoodRepresentative 70796 := by
  apply goodRepresentative_of_list [2,3,7,10,12,16] 70796
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_6 : GoodRepresentative 70797 := by
  apply goodRepresentative_of_list [0,2,3,7,10,12,16] 70797
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_7 : GoodRepresentative 70805 := by
  apply goodRepresentative_of_list [0,2,4,7,10,12,16] 70805
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_8 : GoodRepresentative 70807 := by
  apply goodRepresentative_of_list [0,1,2,4,7,10,12,16] 70807
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_9 : GoodRepresentative 70913 := by
  apply goodRepresentative_of_list [0,8,10,12,16] 70913
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_10 : GoodRepresentative 70917 := by
  apply goodRepresentative_of_list [0,2,8,10,12,16] 70917
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_11 : GoodRepresentative 70921 := by
  apply goodRepresentative_of_list [0,3,8,10,12,16] 70921
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_12 : GoodRepresentative 70924 := by
  apply goodRepresentative_of_list [2,3,8,10,12,16] 70924
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_13 : GoodRepresentative 70925 := by
  apply goodRepresentative_of_list [0,2,3,8,10,12,16] 70925
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_14 : GoodRepresentative 71045 := by
  apply goodRepresentative_of_list [0,2,7,8,10,12,16] 71045
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_15 : GoodRepresentative 71048 := by
  apply goodRepresentative_of_list [3,7,8,10,12,16] 71048
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_16 : GoodRepresentative 71049 := by
  apply goodRepresentative_of_list [0,3,7,8,10,12,16] 71049
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_17 : GoodRepresentative 71052 := by
  apply goodRepresentative_of_list [2,3,7,8,10,12,16] 71052
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_18 : GoodRepresentative 71053 := by
  apply goodRepresentative_of_list [0,2,3,7,8,10,12,16] 71053
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_19 : GoodRepresentative 71169 := by
  apply goodRepresentative_of_list [0,9,10,12,16] 71169
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_20 : GoodRepresentative 71171 := by
  apply goodRepresentative_of_list [0,1,9,10,12,16] 71171
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_21 : GoodRepresentative 71172 := by
  apply goodRepresentative_of_list [2,9,10,12,16] 71172
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_22 : GoodRepresentative 71173 := by
  apply goodRepresentative_of_list [0,2,9,10,12,16] 71173
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_23 : GoodRepresentative 71177 := by
  apply goodRepresentative_of_list [0,3,9,10,12,16] 71177
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_24 : GoodRepresentative 71178 := by
  apply goodRepresentative_of_list [1,3,9,10,12,16] 71178
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_25 : GoodRepresentative 71179 := by
  apply goodRepresentative_of_list [0,1,3,9,10,12,16] 71179
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_26 : GoodRepresentative 71180 := by
  apply goodRepresentative_of_list [2,3,9,10,12,16] 71180
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_27 : GoodRepresentative 71181 := by
  apply goodRepresentative_of_list [0,2,3,9,10,12,16] 71181
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_28 : GoodRepresentative 71185 := by
  apply goodRepresentative_of_list [0,4,9,10,12,16] 71185
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_29 : GoodRepresentative 71187 := by
  apply goodRepresentative_of_list [0,1,4,9,10,12,16] 71187
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_30 : GoodRepresentative 71192 := by
  apply goodRepresentative_of_list [3,4,9,10,12,16] 71192
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_15_31 : GoodRepresentative 71193 := by
  apply goodRepresentative_of_list [0,3,4,9,10,12,16] 71193
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks15 : List ℕ := [70747,70789,70791,70792,70793,70796,70797,70805,70807,70913,70917,70921,70924,70925,71045,71048,71049,71052,71053,71169,71171,71172,71173,71177,71178,71179,71180,71181,71185,71187,71192,71193]

theorem checkedMasks15_good : ∀ m ∈ checkedMasks15, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks15, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_15_0
  · exact good_15_1
  · exact good_15_2
  · exact good_15_3
  · exact good_15_4
  · exact good_15_5
  · exact good_15_6
  · exact good_15_7
  · exact good_15_8
  · exact good_15_9
  · exact good_15_10
  · exact good_15_11
  · exact good_15_12
  · exact good_15_13
  · exact good_15_14
  · exact good_15_15
  · exact good_15_16
  · exact good_15_17
  · exact good_15_18
  · exact good_15_19
  · exact good_15_20
  · exact good_15_21
  · exact good_15_22
  · exact good_15_23
  · exact good_15_24
  · exact good_15_25
  · exact good_15_26
  · exact good_15_27
  · exact good_15_28
  · exact good_15_29
  · exact good_15_30
  · exact good_15_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks15_good
