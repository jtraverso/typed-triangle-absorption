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

theorem good_12_0 : GoodRepresentative 67264 := by
  apply goodRepresentative_of_list [6,7,9,10,16] 67264
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_1 : GoodRepresentative 67280 := by
  apply goodRepresentative_of_list [4,6,7,9,10,16] 67280
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_2 : GoodRepresentative 68616 := by
  apply goodRepresentative_of_list [3,10,11,16] 68616
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_3 : GoodRepresentative 68617 := by
  apply goodRepresentative_of_list [0,3,10,11,16] 68617
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_4 : GoodRepresentative 68618 := by
  apply goodRepresentative_of_list [1,3,10,11,16] 68618
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_5 : GoodRepresentative 68619 := by
  apply goodRepresentative_of_list [0,1,3,10,11,16] 68619
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_6 : GoodRepresentative 68620 := by
  apply goodRepresentative_of_list [2,3,10,11,16] 68620
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_7 : GoodRepresentative 68621 := by
  apply goodRepresentative_of_list [0,2,3,10,11,16] 68621
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_8 : GoodRepresentative 68632 := by
  apply goodRepresentative_of_list [3,4,10,11,16] 68632
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_9 : GoodRepresentative 68633 := by
  apply goodRepresentative_of_list [0,3,4,10,11,16] 68633
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_10 : GoodRepresentative 68634 := by
  apply goodRepresentative_of_list [1,3,4,10,11,16] 68634
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_11 : GoodRepresentative 68635 := by
  apply goodRepresentative_of_list [0,1,3,4,10,11,16] 68635
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_12 : GoodRepresentative 68744 := by
  apply goodRepresentative_of_list [3,7,10,11,16] 68744
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_13 : GoodRepresentative 68745 := by
  apply goodRepresentative_of_list [0,3,7,10,11,16] 68745
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_14 : GoodRepresentative 68748 := by
  apply goodRepresentative_of_list [2,3,7,10,11,16] 68748
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_15 : GoodRepresentative 68749 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,16] 68749
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_16 : GoodRepresentative 69121 := by
  apply goodRepresentative_of_list [0,9,10,11,16] 69121
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_17 : GoodRepresentative 69122 := by
  apply goodRepresentative_of_list [1,9,10,11,16] 69122
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_18 : GoodRepresentative 69123 := by
  apply goodRepresentative_of_list [0,1,9,10,11,16] 69123
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_19 : GoodRepresentative 69124 := by
  apply goodRepresentative_of_list [2,9,10,11,16] 69124
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_20 : GoodRepresentative 69125 := by
  apply goodRepresentative_of_list [0,2,9,10,11,16] 69125
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_21 : GoodRepresentative 69128 := by
  apply goodRepresentative_of_list [3,9,10,11,16] 69128
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_22 : GoodRepresentative 69129 := by
  apply goodRepresentative_of_list [0,3,9,10,11,16] 69129
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_23 : GoodRepresentative 69130 := by
  apply goodRepresentative_of_list [1,3,9,10,11,16] 69130
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_24 : GoodRepresentative 69131 := by
  apply goodRepresentative_of_list [0,1,3,9,10,11,16] 69131
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_25 : GoodRepresentative 69132 := by
  apply goodRepresentative_of_list [2,3,9,10,11,16] 69132
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_26 : GoodRepresentative 69133 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,16] 69133
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_27 : GoodRepresentative 69136 := by
  apply goodRepresentative_of_list [4,9,10,11,16] 69136
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_28 : GoodRepresentative 69137 := by
  apply goodRepresentative_of_list [0,4,9,10,11,16] 69137
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_29 : GoodRepresentative 69138 := by
  apply goodRepresentative_of_list [1,4,9,10,11,16] 69138
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_30 : GoodRepresentative 69139 := by
  apply goodRepresentative_of_list [0,1,4,9,10,11,16] 69139
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_12_31 : GoodRepresentative 69144 := by
  apply goodRepresentative_of_list [3,4,9,10,11,16] 69144
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks12 : List ℕ := [67264,67280,68616,68617,68618,68619,68620,68621,68632,68633,68634,68635,68744,68745,68748,68749,69121,69122,69123,69124,69125,69128,69129,69130,69131,69132,69133,69136,69137,69138,69139,69144]

theorem checkedMasks12_good : ∀ m ∈ checkedMasks12, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks12, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_12_0
  · exact good_12_1
  · exact good_12_2
  · exact good_12_3
  · exact good_12_4
  · exact good_12_5
  · exact good_12_6
  · exact good_12_7
  · exact good_12_8
  · exact good_12_9
  · exact good_12_10
  · exact good_12_11
  · exact good_12_12
  · exact good_12_13
  · exact good_12_14
  · exact good_12_15
  · exact good_12_16
  · exact good_12_17
  · exact good_12_18
  · exact good_12_19
  · exact good_12_20
  · exact good_12_21
  · exact good_12_22
  · exact good_12_23
  · exact good_12_24
  · exact good_12_25
  · exact good_12_26
  · exact good_12_27
  · exact good_12_28
  · exact good_12_29
  · exact good_12_30
  · exact good_12_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks12_good
