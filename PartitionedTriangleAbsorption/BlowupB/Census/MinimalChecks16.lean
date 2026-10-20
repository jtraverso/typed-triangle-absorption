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

theorem good_16_0 : GoodRepresentative 71194 := by
  apply goodRepresentative_of_list [1,3,4,9,10,12,16] 71194
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_1 : GoodRepresentative 71195 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,12,16] 71195
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_2 : GoodRepresentative 71233 := by
  apply goodRepresentative_of_list [0,6,9,10,12,16] 71233
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_3 : GoodRepresentative 71235 := by
  apply goodRepresentative_of_list [0,1,6,9,10,12,16] 71235
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_4 : GoodRepresentative 71241 := by
  apply goodRepresentative_of_list [0,3,6,9,10,12,16] 71241
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_5 : GoodRepresentative 71242 := by
  apply goodRepresentative_of_list [1,3,6,9,10,12,16] 71242
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_6 : GoodRepresentative 71243 := by
  apply goodRepresentative_of_list [0,1,3,6,9,10,12,16] 71243
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_7 : GoodRepresentative 71249 := by
  apply goodRepresentative_of_list [0,4,6,9,10,12,16] 71249
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_8 : GoodRepresentative 71251 := by
  apply goodRepresentative_of_list [0,1,4,6,9,10,12,16] 71251
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_9 : GoodRepresentative 71256 := by
  apply goodRepresentative_of_list [3,4,6,9,10,12,16] 71256
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_10 : GoodRepresentative 71257 := by
  apply goodRepresentative_of_list [0,3,4,6,9,10,12,16] 71257
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_11 : GoodRepresentative 71258 := by
  apply goodRepresentative_of_list [1,3,4,6,9,10,12,16] 71258
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_12 : GoodRepresentative 71259 := by
  apply goodRepresentative_of_list [0,1,3,4,6,9,10,12,16] 71259
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_13 : GoodRepresentative 71297 := by
  apply goodRepresentative_of_list [0,7,9,10,12,16] 71297
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_14 : GoodRepresentative 71300 := by
  apply goodRepresentative_of_list [2,7,9,10,12,16] 71300
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_15 : GoodRepresentative 71301 := by
  apply goodRepresentative_of_list [0,2,7,9,10,12,16] 71301
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_16 : GoodRepresentative 71304 := by
  apply goodRepresentative_of_list [3,7,9,10,12,16] 71304
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_17 : GoodRepresentative 71305 := by
  apply goodRepresentative_of_list [0,3,7,9,10,12,16] 71305
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_18 : GoodRepresentative 71308 := by
  apply goodRepresentative_of_list [2,3,7,9,10,12,16] 71308
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_19 : GoodRepresentative 71309 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,12,16] 71309
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_20 : GoodRepresentative 71312 := by
  apply goodRepresentative_of_list [4,7,9,10,12,16] 71312
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_21 : GoodRepresentative 71376 := by
  apply goodRepresentative_of_list [4,6,7,9,10,12,16] 71376
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_22 : GoodRepresentative 71693 := by
  apply goodRepresentative_of_list [0,2,3,11,12,16] 71693
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_23 : GoodRepresentative 71817 := by
  apply goodRepresentative_of_list [0,3,7,11,12,16] 71817
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_24 : GoodRepresentative 71821 := by
  apply goodRepresentative_of_list [0,2,3,7,11,12,16] 71821
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_25 : GoodRepresentative 72193 := by
  apply goodRepresentative_of_list [0,9,11,12,16] 72193
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_26 : GoodRepresentative 72197 := by
  apply goodRepresentative_of_list [0,2,9,11,12,16] 72197
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_27 : GoodRepresentative 72201 := by
  apply goodRepresentative_of_list [0,3,9,11,12,16] 72201
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_28 : GoodRepresentative 72205 := by
  apply goodRepresentative_of_list [0,2,3,9,11,12,16] 72205
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_29 : GoodRepresentative 72321 := by
  apply goodRepresentative_of_list [0,7,9,11,12,16] 72321
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_30 : GoodRepresentative 72325 := by
  apply goodRepresentative_of_list [0,2,7,9,11,12,16] 72325
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_16_31 : GoodRepresentative 72329 := by
  apply goodRepresentative_of_list [0,3,7,9,11,12,16] 72329
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks16 : List ℕ := [71194,71195,71233,71235,71241,71242,71243,71249,71251,71256,71257,71258,71259,71297,71300,71301,71304,71305,71308,71309,71312,71376,71693,71817,71821,72193,72197,72201,72205,72321,72325,72329]

theorem checkedMasks16_good : ∀ m ∈ checkedMasks16, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks16, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_16_0
  · exact good_16_1
  · exact good_16_2
  · exact good_16_3
  · exact good_16_4
  · exact good_16_5
  · exact good_16_6
  · exact good_16_7
  · exact good_16_8
  · exact good_16_9
  · exact good_16_10
  · exact good_16_11
  · exact good_16_12
  · exact good_16_13
  · exact good_16_14
  · exact good_16_15
  · exact good_16_16
  · exact good_16_17
  · exact good_16_18
  · exact good_16_19
  · exact good_16_20
  · exact good_16_21
  · exact good_16_22
  · exact good_16_23
  · exact good_16_24
  · exact good_16_25
  · exact good_16_26
  · exact good_16_27
  · exact good_16_28
  · exact good_16_29
  · exact good_16_30
  · exact good_16_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks16_good
