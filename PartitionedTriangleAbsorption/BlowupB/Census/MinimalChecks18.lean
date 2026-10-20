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

theorem good_18_0 : GoodRepresentative 77456 := by
  apply goodRepresentative_of_list [4,7,9,10,11,13,16] 77456
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_1 : GoodRepresentative 77488 := by
  apply goodRepresentative_of_list [4,5,7,9,10,11,13,16] 77488
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_2 : GoodRepresentative 77965 := by
  apply goodRepresentative_of_list [0,2,3,7,12,13,16] 77965
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_3 : GoodRepresentative 78341 := by
  apply goodRepresentative_of_list [0,2,9,12,13,16] 78341
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_4 : GoodRepresentative 78349 := by
  apply goodRepresentative_of_list [0,2,3,9,12,13,16] 78349
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_5 : GoodRepresentative 78469 := by
  apply goodRepresentative_of_list [0,2,7,9,12,13,16] 78469
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_6 : GoodRepresentative 78477 := by
  apply goodRepresentative_of_list [0,2,3,7,9,12,13,16] 78477
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_7 : GoodRepresentative 78985 := by
  apply goodRepresentative_of_list [0,3,7,10,12,13,16] 78985
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_8 : GoodRepresentative 78988 := by
  apply goodRepresentative_of_list [2,3,7,10,12,13,16] 78988
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_9 : GoodRepresentative 78989 := by
  apply goodRepresentative_of_list [0,2,3,7,10,12,13,16] 78989
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_10 : GoodRepresentative 79361 := by
  apply goodRepresentative_of_list [0,9,10,12,13,16] 79361
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_11 : GoodRepresentative 79365 := by
  apply goodRepresentative_of_list [0,2,9,10,12,13,16] 79365
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_12 : GoodRepresentative 79369 := by
  apply goodRepresentative_of_list [0,3,9,10,12,13,16] 79369
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_13 : GoodRepresentative 79372 := by
  apply goodRepresentative_of_list [2,3,9,10,12,13,16] 79372
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_14 : GoodRepresentative 79373 := by
  apply goodRepresentative_of_list [0,2,3,9,10,12,13,16] 79373
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_15 : GoodRepresentative 79489 := by
  apply goodRepresentative_of_list [0,7,9,10,12,13,16] 79489
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_16 : GoodRepresentative 79493 := by
  apply goodRepresentative_of_list [0,2,7,9,10,12,13,16] 79493
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_17 : GoodRepresentative 79497 := by
  apply goodRepresentative_of_list [0,3,7,9,10,12,13,16] 79497
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_18 : GoodRepresentative 79500 := by
  apply goodRepresentative_of_list [2,3,7,9,10,12,13,16] 79500
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_19 : GoodRepresentative 79501 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,12,13,16] 79501
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_20 : GoodRepresentative 80013 := by
  apply goodRepresentative_of_list [0,2,3,7,11,12,13,16] 80013
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_21 : GoodRepresentative 80385 := by
  apply goodRepresentative_of_list [0,9,11,12,13,16] 80385
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_22 : GoodRepresentative 80389 := by
  apply goodRepresentative_of_list [0,2,9,11,12,13,16] 80389
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_23 : GoodRepresentative 80393 := by
  apply goodRepresentative_of_list [0,3,9,11,12,13,16] 80393
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_24 : GoodRepresentative 80397 := by
  apply goodRepresentative_of_list [0,2,3,9,11,12,13,16] 80397
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_25 : GoodRepresentative 80513 := by
  apply goodRepresentative_of_list [0,7,9,11,12,13,16] 80513
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_26 : GoodRepresentative 80517 := by
  apply goodRepresentative_of_list [0,2,7,9,11,12,13,16] 80517
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_27 : GoodRepresentative 80521 := by
  apply goodRepresentative_of_list [0,3,7,9,11,12,13,16] 80521
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_28 : GoodRepresentative 80525 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,12,13,16] 80525
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_29 : GoodRepresentative 81037 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,12,13,16] 81037
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_30 : GoodRepresentative 81409 := by
  apply goodRepresentative_of_list [0,9,10,11,12,13,16] 81409
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_18_31 : GoodRepresentative 81413 := by
  apply goodRepresentative_of_list [0,2,9,10,11,12,13,16] 81413
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks18 : List ℕ := [77456,77488,77965,78341,78349,78469,78477,78985,78988,78989,79361,79365,79369,79372,79373,79489,79493,79497,79500,79501,80013,80385,80389,80393,80397,80513,80517,80521,80525,81037,81409,81413]

theorem checkedMasks18_good : ∀ m ∈ checkedMasks18, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks18, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_18_0
  · exact good_18_1
  · exact good_18_2
  · exact good_18_3
  · exact good_18_4
  · exact good_18_5
  · exact good_18_6
  · exact good_18_7
  · exact good_18_8
  · exact good_18_9
  · exact good_18_10
  · exact good_18_11
  · exact good_18_12
  · exact good_18_13
  · exact good_18_14
  · exact good_18_15
  · exact good_18_16
  · exact good_18_17
  · exact good_18_18
  · exact good_18_19
  · exact good_18_20
  · exact good_18_21
  · exact good_18_22
  · exact good_18_23
  · exact good_18_24
  · exact good_18_25
  · exact good_18_26
  · exact good_18_27
  · exact good_18_28
  · exact good_18_29
  · exact good_18_30
  · exact good_18_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks18_good
