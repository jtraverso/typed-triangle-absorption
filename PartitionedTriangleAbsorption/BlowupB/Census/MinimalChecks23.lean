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

theorem good_23_0 : GoodRepresentative 593413 := by
  apply goodRepresentative_of_list [0,2,9,10,11,16,19] 593413
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_1 : GoodRepresentative 593417 := by
  apply goodRepresentative_of_list [0,3,9,10,11,16,19] 593417
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_2 : GoodRepresentative 593419 := by
  apply goodRepresentative_of_list [0,1,3,9,10,11,16,19] 593419
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_3 : GoodRepresentative 593421 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,16,19] 593421
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_4 : GoodRepresentative 593433 := by
  apply goodRepresentative_of_list [0,3,4,9,10,11,16,19] 593433
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_5 : GoodRepresentative 593435 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,11,16,19] 593435
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_6 : GoodRepresentative 593541 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,16,19] 593541
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_7 : GoodRepresentative 593545 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,16,19] 593545
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_8 : GoodRepresentative 593549 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,16,19] 593549
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_9 : GoodRepresentative 597005 := by
  apply goodRepresentative_of_list [0,2,3,10,11,12,16,19] 597005
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_10 : GoodRepresentative 597129 := by
  apply goodRepresentative_of_list [0,3,7,10,11,12,16,19] 597129
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_11 : GoodRepresentative 597133 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,12,16,19] 597133
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_12 : GoodRepresentative 597633 := by
  apply goodRepresentative_of_list [0,7,9,10,11,12,16,19] 597633
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_13 : GoodRepresentative 597637 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,12,16,19] 597637
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_14 : GoodRepresentative 597645 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,16,19] 597645
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_15 : GoodRepresentative 601239 := by
  apply goodRepresentative_of_list [0,1,2,4,7,10,11,13,16,19] 601239
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_16 : GoodRepresentative 601271 := by
  apply goodRepresentative_of_list [0,1,2,4,5,7,10,11,13,16,19] 601271
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_17 : GoodRepresentative 601609 := by
  apply goodRepresentative_of_list [0,3,9,10,11,13,16,19] 601609
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_18 : GoodRepresentative 601611 := by
  apply goodRepresentative_of_list [0,1,3,9,10,11,13,16,19] 601611
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_19 : GoodRepresentative 601627 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,11,13,16,19] 601627
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_20 : GoodRepresentative 603277 := by
  apply goodRepresentative_of_list [0,2,3,7,10,12,13,16,19] 603277
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_21 : GoodRepresentative 603653 := by
  apply goodRepresentative_of_list [0,2,9,10,12,13,16,19] 603653
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_22 : GoodRepresentative 603661 := by
  apply goodRepresentative_of_list [0,2,3,9,10,12,13,16,19] 603661
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_23 : GoodRepresentative 603789 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,12,13,16,19] 603789
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_24 : GoodRepresentative 605325 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,12,13,16,19] 605325
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_25 : GoodRepresentative 605709 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,12,13,16,19] 605709
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_26 : GoodRepresentative 605833 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,12,13,16,19] 605833
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_27 : GoodRepresentative 605837 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,13,16,19] 605837
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_23_28 : GoodRepresentative 638605 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,13,15,16,19] 638605
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks23 : List ℕ := [593413,593417,593419,593421,593433,593435,593541,593545,593549,597005,597129,597133,597633,597637,597645,601239,601271,601609,601611,601627,603277,603653,603661,603789,605325,605709,605833,605837,638605]

theorem checkedMasks23_good : ∀ m ∈ checkedMasks23, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks23, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_23_0
  · exact good_23_1
  · exact good_23_2
  · exact good_23_3
  · exact good_23_4
  · exact good_23_5
  · exact good_23_6
  · exact good_23_7
  · exact good_23_8
  · exact good_23_9
  · exact good_23_10
  · exact good_23_11
  · exact good_23_12
  · exact good_23_13
  · exact good_23_14
  · exact good_23_15
  · exact good_23_16
  · exact good_23_17
  · exact good_23_18
  · exact good_23_19
  · exact good_23_20
  · exact good_23_21
  · exact good_23_22
  · exact good_23_23
  · exact good_23_24
  · exact good_23_25
  · exact good_23_26
  · exact good_23_27
  · exact good_23_28

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks23_good
