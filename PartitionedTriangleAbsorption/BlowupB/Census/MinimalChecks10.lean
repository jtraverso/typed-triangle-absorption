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

theorem good_10_0 : GoodRepresentative 42637 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,13,15] 42637
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_1 : GoodRepresentative 43653 := by
  apply goodRepresentative_of_list [0,2,7,9,11,13,15] 43653
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_2 : GoodRepresentative 43657 := by
  apply goodRepresentative_of_list [0,3,7,9,11,13,15] 43657
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_3 : GoodRepresentative 43661 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,13,15] 43661
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_4 : GoodRepresentative 44677 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,13,15] 44677
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_5 : GoodRepresentative 44681 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,13,15] 44681
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_6 : GoodRepresentative 44684 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,13,15] 44684
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_7 : GoodRepresentative 44685 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,13,15] 44685
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_8 : GoodRepresentative 47756 := by
  apply goodRepresentative_of_list [2,3,7,9,11,12,13,15] 47756
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_9 : GoodRepresentative 47757 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,12,13,15] 47757
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_10 : GoodRepresentative 48781 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,13,15] 48781
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_11 : GoodRepresentative 66568 := by
  apply goodRepresentative_of_list [3,10,16] 66568
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_12 : GoodRepresentative 66569 := by
  apply goodRepresentative_of_list [0,3,10,16] 66569
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_13 : GoodRepresentative 66570 := by
  apply goodRepresentative_of_list [1,3,10,16] 66570
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_14 : GoodRepresentative 66571 := by
  apply goodRepresentative_of_list [0,1,3,10,16] 66571
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_15 : GoodRepresentative 66584 := by
  apply goodRepresentative_of_list [3,4,10,16] 66584
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_16 : GoodRepresentative 66585 := by
  apply goodRepresentative_of_list [0,3,4,10,16] 66585
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_17 : GoodRepresentative 66586 := by
  apply goodRepresentative_of_list [1,3,4,10,16] 66586
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_18 : GoodRepresentative 66587 := by
  apply goodRepresentative_of_list [0,1,3,4,10,16] 66587
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_19 : GoodRepresentative 66625 := by
  apply goodRepresentative_of_list [0,6,10,16] 66625
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_20 : GoodRepresentative 66627 := by
  apply goodRepresentative_of_list [0,1,6,10,16] 66627
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_21 : GoodRepresentative 66632 := by
  apply goodRepresentative_of_list [3,6,10,16] 66632
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_22 : GoodRepresentative 66633 := by
  apply goodRepresentative_of_list [0,3,6,10,16] 66633
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_23 : GoodRepresentative 66634 := by
  apply goodRepresentative_of_list [1,3,6,10,16] 66634
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_24 : GoodRepresentative 66635 := by
  apply goodRepresentative_of_list [0,1,3,6,10,16] 66635
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_25 : GoodRepresentative 66643 := by
  apply goodRepresentative_of_list [0,1,4,6,10,16] 66643
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_26 : GoodRepresentative 66648 := by
  apply goodRepresentative_of_list [3,4,6,10,16] 66648
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_27 : GoodRepresentative 66649 := by
  apply goodRepresentative_of_list [0,3,4,6,10,16] 66649
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_28 : GoodRepresentative 66650 := by
  apply goodRepresentative_of_list [1,3,4,6,10,16] 66650
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_29 : GoodRepresentative 66651 := by
  apply goodRepresentative_of_list [0,1,3,4,6,10,16] 66651
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_30 : GoodRepresentative 67073 := by
  apply goodRepresentative_of_list [0,9,10,16] 67073
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_10_31 : GoodRepresentative 67074 := by
  apply goodRepresentative_of_list [1,9,10,16] 67074
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks10 : List ℕ := [42637,43653,43657,43661,44677,44681,44684,44685,47756,47757,48781,66568,66569,66570,66571,66584,66585,66586,66587,66625,66627,66632,66633,66634,66635,66643,66648,66649,66650,66651,67073,67074]

theorem checkedMasks10_good : ∀ m ∈ checkedMasks10, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks10, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_10_0
  · exact good_10_1
  · exact good_10_2
  · exact good_10_3
  · exact good_10_4
  · exact good_10_5
  · exact good_10_6
  · exact good_10_7
  · exact good_10_8
  · exact good_10_9
  · exact good_10_10
  · exact good_10_11
  · exact good_10_12
  · exact good_10_13
  · exact good_10_14
  · exact good_10_15
  · exact good_10_16
  · exact good_10_17
  · exact good_10_18
  · exact good_10_19
  · exact good_10_20
  · exact good_10_21
  · exact good_10_22
  · exact good_10_23
  · exact good_10_24
  · exact good_10_25
  · exact good_10_26
  · exact good_10_27
  · exact good_10_28
  · exact good_10_29
  · exact good_10_30
  · exact good_10_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks10_good
