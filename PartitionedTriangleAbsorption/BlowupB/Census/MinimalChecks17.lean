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

theorem good_17_0 : GoodRepresentative 72333 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,12,16] 72333
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_1 : GoodRepresentative 72717 := by
  apply goodRepresentative_of_list [0,2,3,10,11,12,16] 72717
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_2 : GoodRepresentative 72840 := by
  apply goodRepresentative_of_list [3,7,10,11,12,16] 72840
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_3 : GoodRepresentative 72841 := by
  apply goodRepresentative_of_list [0,3,7,10,11,12,16] 72841
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_4 : GoodRepresentative 72844 := by
  apply goodRepresentative_of_list [2,3,7,10,11,12,16] 72844
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_5 : GoodRepresentative 72845 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,12,16] 72845
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_6 : GoodRepresentative 73217 := by
  apply goodRepresentative_of_list [0,9,10,11,12,16] 73217
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_7 : GoodRepresentative 73220 := by
  apply goodRepresentative_of_list [2,9,10,11,12,16] 73220
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_8 : GoodRepresentative 73221 := by
  apply goodRepresentative_of_list [0,2,9,10,11,12,16] 73221
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_9 : GoodRepresentative 73225 := by
  apply goodRepresentative_of_list [0,3,9,10,11,12,16] 73225
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_10 : GoodRepresentative 73228 := by
  apply goodRepresentative_of_list [2,3,9,10,11,12,16] 73228
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_11 : GoodRepresentative 73229 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,12,16] 73229
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_12 : GoodRepresentative 73344 := by
  apply goodRepresentative_of_list [7,9,10,11,12,16] 73344
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_13 : GoodRepresentative 73345 := by
  apply goodRepresentative_of_list [0,7,9,10,11,12,16] 73345
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_14 : GoodRepresentative 73348 := by
  apply goodRepresentative_of_list [2,7,9,10,11,12,16] 73348
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_15 : GoodRepresentative 73349 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,12,16] 73349
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_16 : GoodRepresentative 73352 := by
  apply goodRepresentative_of_list [3,7,9,10,11,12,16] 73352
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_17 : GoodRepresentative 73353 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,12,16] 73353
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_18 : GoodRepresentative 73356 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,12,16] 73356
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_19 : GoodRepresentative 73357 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,16] 73357
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_20 : GoodRepresentative 77313 := by
  apply goodRepresentative_of_list [0,9,10,11,13,16] 77313
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_21 : GoodRepresentative 77315 := by
  apply goodRepresentative_of_list [0,1,9,10,11,13,16] 77315
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_22 : GoodRepresentative 77320 := by
  apply goodRepresentative_of_list [3,9,10,11,13,16] 77320
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_23 : GoodRepresentative 77321 := by
  apply goodRepresentative_of_list [0,3,9,10,11,13,16] 77321
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_24 : GoodRepresentative 77322 := by
  apply goodRepresentative_of_list [1,3,9,10,11,13,16] 77322
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_25 : GoodRepresentative 77323 := by
  apply goodRepresentative_of_list [0,1,3,9,10,11,13,16] 77323
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_26 : GoodRepresentative 77329 := by
  apply goodRepresentative_of_list [0,4,9,10,11,13,16] 77329
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_27 : GoodRepresentative 77331 := by
  apply goodRepresentative_of_list [0,1,4,9,10,11,13,16] 77331
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_28 : GoodRepresentative 77336 := by
  apply goodRepresentative_of_list [3,4,9,10,11,13,16] 77336
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_29 : GoodRepresentative 77337 := by
  apply goodRepresentative_of_list [0,3,4,9,10,11,13,16] 77337
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_30 : GoodRepresentative 77338 := by
  apply goodRepresentative_of_list [1,3,4,9,10,11,13,16] 77338
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_17_31 : GoodRepresentative 77339 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,11,13,16] 77339
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks17 : List ℕ := [72333,72717,72840,72841,72844,72845,73217,73220,73221,73225,73228,73229,73344,73345,73348,73349,73352,73353,73356,73357,77313,77315,77320,77321,77322,77323,77329,77331,77336,77337,77338,77339]

theorem checkedMasks17_good : ∀ m ∈ checkedMasks17, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks17, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_17_0
  · exact good_17_1
  · exact good_17_2
  · exact good_17_3
  · exact good_17_4
  · exact good_17_5
  · exact good_17_6
  · exact good_17_7
  · exact good_17_8
  · exact good_17_9
  · exact good_17_10
  · exact good_17_11
  · exact good_17_12
  · exact good_17_13
  · exact good_17_14
  · exact good_17_15
  · exact good_17_16
  · exact good_17_17
  · exact good_17_18
  · exact good_17_19
  · exact good_17_20
  · exact good_17_21
  · exact good_17_22
  · exact good_17_23
  · exact good_17_24
  · exact good_17_25
  · exact good_17_26
  · exact good_17_27
  · exact good_17_28
  · exact good_17_29
  · exact good_17_30
  · exact good_17_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks17_good
