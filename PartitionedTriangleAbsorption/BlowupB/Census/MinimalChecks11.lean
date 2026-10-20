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

theorem good_11_0 : GoodRepresentative 67075 := by
  apply goodRepresentative_of_list [0,1,9,10,16] 67075
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_1 : GoodRepresentative 67080 := by
  apply goodRepresentative_of_list [3,9,10,16] 67080
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_2 : GoodRepresentative 67081 := by
  apply goodRepresentative_of_list [0,3,9,10,16] 67081
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_3 : GoodRepresentative 67082 := by
  apply goodRepresentative_of_list [1,3,9,10,16] 67082
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_4 : GoodRepresentative 67083 := by
  apply goodRepresentative_of_list [0,1,3,9,10,16] 67083
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_5 : GoodRepresentative 67088 := by
  apply goodRepresentative_of_list [4,9,10,16] 67088
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_6 : GoodRepresentative 67089 := by
  apply goodRepresentative_of_list [0,4,9,10,16] 67089
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_7 : GoodRepresentative 67090 := by
  apply goodRepresentative_of_list [1,4,9,10,16] 67090
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_8 : GoodRepresentative 67091 := by
  apply goodRepresentative_of_list [0,1,4,9,10,16] 67091
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_9 : GoodRepresentative 67096 := by
  apply goodRepresentative_of_list [3,4,9,10,16] 67096
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_10 : GoodRepresentative 67097 := by
  apply goodRepresentative_of_list [0,3,4,9,10,16] 67097
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_11 : GoodRepresentative 67098 := by
  apply goodRepresentative_of_list [1,3,4,9,10,16] 67098
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_12 : GoodRepresentative 67099 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,16] 67099
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_13 : GoodRepresentative 67104 := by
  apply goodRepresentative_of_list [5,9,10,16] 67104
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_14 : GoodRepresentative 67120 := by
  apply goodRepresentative_of_list [4,5,9,10,16] 67120
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_15 : GoodRepresentative 67137 := by
  apply goodRepresentative_of_list [0,6,9,10,16] 67137
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_16 : GoodRepresentative 67138 := by
  apply goodRepresentative_of_list [1,6,9,10,16] 67138
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_17 : GoodRepresentative 67139 := by
  apply goodRepresentative_of_list [0,1,6,9,10,16] 67139
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_18 : GoodRepresentative 67144 := by
  apply goodRepresentative_of_list [3,6,9,10,16] 67144
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_19 : GoodRepresentative 67145 := by
  apply goodRepresentative_of_list [0,3,6,9,10,16] 67145
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_20 : GoodRepresentative 67146 := by
  apply goodRepresentative_of_list [1,3,6,9,10,16] 67146
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_21 : GoodRepresentative 67147 := by
  apply goodRepresentative_of_list [0,1,3,6,9,10,16] 67147
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_22 : GoodRepresentative 67152 := by
  apply goodRepresentative_of_list [4,6,9,10,16] 67152
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_23 : GoodRepresentative 67153 := by
  apply goodRepresentative_of_list [0,4,6,9,10,16] 67153
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_24 : GoodRepresentative 67154 := by
  apply goodRepresentative_of_list [1,4,6,9,10,16] 67154
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_25 : GoodRepresentative 67155 := by
  apply goodRepresentative_of_list [0,1,4,6,9,10,16] 67155
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_26 : GoodRepresentative 67160 := by
  apply goodRepresentative_of_list [3,4,6,9,10,16] 67160
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_27 : GoodRepresentative 67161 := by
  apply goodRepresentative_of_list [0,3,4,6,9,10,16] 67161
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_28 : GoodRepresentative 67162 := by
  apply goodRepresentative_of_list [1,3,4,6,9,10,16] 67162
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_29 : GoodRepresentative 67163 := by
  apply goodRepresentative_of_list [0,1,3,4,6,9,10,16] 67163
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_30 : GoodRepresentative 67216 := by
  apply goodRepresentative_of_list [4,7,9,10,16] 67216
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_11_31 : GoodRepresentative 67248 := by
  apply goodRepresentative_of_list [4,5,7,9,10,16] 67248
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks11 : List ℕ := [67075,67080,67081,67082,67083,67088,67089,67090,67091,67096,67097,67098,67099,67104,67120,67137,67138,67139,67144,67145,67146,67147,67152,67153,67154,67155,67160,67161,67162,67163,67216,67248]

theorem checkedMasks11_good : ∀ m ∈ checkedMasks11, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks11, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_11_0
  · exact good_11_1
  · exact good_11_2
  · exact good_11_3
  · exact good_11_4
  · exact good_11_5
  · exact good_11_6
  · exact good_11_7
  · exact good_11_8
  · exact good_11_9
  · exact good_11_10
  · exact good_11_11
  · exact good_11_12
  · exact good_11_13
  · exact good_11_14
  · exact good_11_15
  · exact good_11_16
  · exact good_11_17
  · exact good_11_18
  · exact good_11_19
  · exact good_11_20
  · exact good_11_21
  · exact good_11_22
  · exact good_11_23
  · exact good_11_24
  · exact good_11_25
  · exact good_11_26
  · exact good_11_27
  · exact good_11_28
  · exact good_11_29
  · exact good_11_30
  · exact good_11_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks11_good
