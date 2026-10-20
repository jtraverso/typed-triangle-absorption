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

theorem good_20_0 : GoodRepresentative 99977 := by
  apply goodRepresentative_of_list [0,3,7,9,10,15,16] 99977
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_1 : GoodRepresentative 99980 := by
  apply goodRepresentative_of_list [2,3,7,9,10,15,16] 99980
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_2 : GoodRepresentative 99981 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,15,16] 99981
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_3 : GoodRepresentative 99984 := by
  apply goodRepresentative_of_list [4,7,9,10,15,16] 99984
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_4 : GoodRepresentative 100048 := by
  apply goodRepresentative_of_list [4,6,7,9,10,15,16] 100048
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_5 : GoodRepresentative 101893 := by
  apply goodRepresentative_of_list [0,2,9,10,11,15,16] 101893
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_6 : GoodRepresentative 101897 := by
  apply goodRepresentative_of_list [0,3,9,10,11,15,16] 101897
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_7 : GoodRepresentative 101900 := by
  apply goodRepresentative_of_list [2,3,9,10,11,15,16] 101900
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_8 : GoodRepresentative 101901 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,15,16] 101901
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_9 : GoodRepresentative 102017 := by
  apply goodRepresentative_of_list [0,7,9,10,11,15,16] 102017
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_10 : GoodRepresentative 102021 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,15,16] 102021
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_11 : GoodRepresentative 102025 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,15,16] 102025
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_12 : GoodRepresentative 102028 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,15,16] 102028
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_13 : GoodRepresentative 102029 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,15,16] 102029
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_14 : GoodRepresentative 102938 := by
  apply goodRepresentative_of_list [1,3,4,9,12,15,16] 102938
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_15 : GoodRepresentative 102939 := by
  apply goodRepresentative_of_list [0,1,3,4,9,12,15,16] 102939
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_16 : GoodRepresentative 103002 := by
  apply goodRepresentative_of_list [1,3,4,6,9,12,15,16] 103002
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_17 : GoodRepresentative 103003 := by
  apply goodRepresentative_of_list [0,1,3,4,6,9,12,15,16] 103003
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_18 : GoodRepresentative 103056 := by
  apply goodRepresentative_of_list [4,7,9,12,15,16] 103056
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_19 : GoodRepresentative 103120 := by
  apply goodRepresentative_of_list [4,6,7,9,12,15,16] 103120
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_20 : GoodRepresentative 103945 := by
  apply goodRepresentative_of_list [0,3,9,10,12,15,16] 103945
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_21 : GoodRepresentative 103947 := by
  apply goodRepresentative_of_list [0,1,3,9,10,12,15,16] 103947
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_22 : GoodRepresentative 103949 := by
  apply goodRepresentative_of_list [0,2,3,9,10,12,15,16] 103949
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_23 : GoodRepresentative 103963 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,12,15,16] 103963
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_24 : GoodRepresentative 104009 := by
  apply goodRepresentative_of_list [0,3,6,9,10,12,15,16] 104009
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_25 : GoodRepresentative 104011 := by
  apply goodRepresentative_of_list [0,1,3,6,9,10,12,15,16] 104011
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_26 : GoodRepresentative 104027 := by
  apply goodRepresentative_of_list [0,1,3,4,6,9,10,12,15,16] 104027
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_27 : GoodRepresentative 104065 := by
  apply goodRepresentative_of_list [0,7,9,10,12,15,16] 104065
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_28 : GoodRepresentative 104069 := by
  apply goodRepresentative_of_list [0,2,7,9,10,12,15,16] 104069
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_29 : GoodRepresentative 104073 := by
  apply goodRepresentative_of_list [0,3,7,9,10,12,15,16] 104073
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_30 : GoodRepresentative 104076 := by
  apply goodRepresentative_of_list [2,3,7,9,10,12,15,16] 104076
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_20_31 : GoodRepresentative 104077 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,12,15,16] 104077
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks20 : List ℕ := [99977,99980,99981,99984,100048,101893,101897,101900,101901,102017,102021,102025,102028,102029,102938,102939,103002,103003,103056,103120,103945,103947,103949,103963,104009,104011,104027,104065,104069,104073,104076,104077]

theorem checkedMasks20_good : ∀ m ∈ checkedMasks20, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks20, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_20_0
  · exact good_20_1
  · exact good_20_2
  · exact good_20_3
  · exact good_20_4
  · exact good_20_5
  · exact good_20_6
  · exact good_20_7
  · exact good_20_8
  · exact good_20_9
  · exact good_20_10
  · exact good_20_11
  · exact good_20_12
  · exact good_20_13
  · exact good_20_14
  · exact good_20_15
  · exact good_20_16
  · exact good_20_17
  · exact good_20_18
  · exact good_20_19
  · exact good_20_20
  · exact good_20_21
  · exact good_20_22
  · exact good_20_23
  · exact good_20_24
  · exact good_20_25
  · exact good_20_26
  · exact good_20_27
  · exact good_20_28
  · exact good_20_29
  · exact good_20_30
  · exact good_20_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks20_good
