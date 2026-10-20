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

theorem good_21_0 : GoodRepresentative 104080 := by
  apply goodRepresentative_of_list [4,7,9,10,12,15,16] 104080
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_1 : GoodRepresentative 104144 := by
  apply goodRepresentative_of_list [4,6,7,9,10,12,15,16] 104144
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_2 : GoodRepresentative 104973 := by
  apply goodRepresentative_of_list [0,2,3,9,11,12,15,16] 104973
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_3 : GoodRepresentative 105093 := by
  apply goodRepresentative_of_list [0,2,7,9,11,12,15,16] 105093
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_4 : GoodRepresentative 105101 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,12,15,16] 105101
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_5 : GoodRepresentative 105997 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,12,15,16] 105997
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_6 : GoodRepresentative 106113 := by
  apply goodRepresentative_of_list [0,7,9,10,11,12,15,16] 106113
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_7 : GoodRepresentative 106117 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,12,15,16] 106117
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_8 : GoodRepresentative 106121 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,12,15,16] 106121
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_9 : GoodRepresentative 106124 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,12,15,16] 106124
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_10 : GoodRepresentative 106125 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,15,16] 106125
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_11 : GoodRepresentative 108161 := by
  apply goodRepresentative_of_list [0,7,9,10,13,15,16] 108161
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_12 : GoodRepresentative 108165 := by
  apply goodRepresentative_of_list [0,2,7,9,10,13,15,16] 108165
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_13 : GoodRepresentative 108169 := by
  apply goodRepresentative_of_list [0,3,7,9,10,13,15,16] 108169
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_14 : GoodRepresentative 108173 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,13,15,16] 108173
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_15 : GoodRepresentative 110213 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,13,15,16] 110213
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_16 : GoodRepresentative 110217 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,13,15,16] 110217
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_17 : GoodRepresentative 110221 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,13,15,16] 110221
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_18 : GoodRepresentative 112265 := by
  apply goodRepresentative_of_list [0,3,7,9,10,12,13,15,16] 112265
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_19 : GoodRepresentative 112269 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,12,13,15,16] 112269
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_20 : GoodRepresentative 113293 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,12,13,15,16] 113293
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_21 : GoodRepresentative 114317 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,13,15,16] 114317
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_22 : GoodRepresentative 201737 := by
  apply goodRepresentative_of_list [0,3,10,12,16,17] 201737
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_23 : GoodRepresentative 201739 := by
  apply goodRepresentative_of_list [0,1,3,10,12,16,17] 201739
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_24 : GoodRepresentative 201755 := by
  apply goodRepresentative_of_list [0,1,3,4,10,12,16,17] 201755
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_25 : GoodRepresentative 201801 := by
  apply goodRepresentative_of_list [0,3,6,10,12,16,17] 201801
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_26 : GoodRepresentative 201803 := by
  apply goodRepresentative_of_list [0,1,3,6,10,12,16,17] 201803
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_27 : GoodRepresentative 201819 := by
  apply goodRepresentative_of_list [0,1,3,4,6,10,12,16,17] 201819
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_28 : GoodRepresentative 590849 := by
  apply goodRepresentative_of_list [0,10,16,19] 590849
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_29 : GoodRepresentative 590851 := by
  apply goodRepresentative_of_list [0,1,10,16,19] 590851
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_30 : GoodRepresentative 590855 := by
  apply goodRepresentative_of_list [0,1,2,10,16,19] 590855
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_21_31 : GoodRepresentative 590867 := by
  apply goodRepresentative_of_list [0,1,4,10,16,19] 590867
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks21 : List ℕ := [104080,104144,104973,105093,105101,105997,106113,106117,106121,106124,106125,108161,108165,108169,108173,110213,110217,110221,112265,112269,113293,114317,201737,201739,201755,201801,201803,201819,590849,590851,590855,590867]

theorem checkedMasks21_good : ∀ m ∈ checkedMasks21, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks21, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_21_0
  · exact good_21_1
  · exact good_21_2
  · exact good_21_3
  · exact good_21_4
  · exact good_21_5
  · exact good_21_6
  · exact good_21_7
  · exact good_21_8
  · exact good_21_9
  · exact good_21_10
  · exact good_21_11
  · exact good_21_12
  · exact good_21_13
  · exact good_21_14
  · exact good_21_15
  · exact good_21_16
  · exact good_21_17
  · exact good_21_18
  · exact good_21_19
  · exact good_21_20
  · exact good_21_21
  · exact good_21_22
  · exact good_21_23
  · exact good_21_24
  · exact good_21_25
  · exact good_21_26
  · exact good_21_27
  · exact good_21_28
  · exact good_21_29
  · exact good_21_30
  · exact good_21_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks21_good
