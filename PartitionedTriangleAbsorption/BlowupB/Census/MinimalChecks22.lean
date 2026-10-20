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

theorem good_22_0 : GoodRepresentative 590869 := by
  apply goodRepresentative_of_list [0,2,4,10,16,19] 590869
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_1 : GoodRepresentative 590871 := by
  apply goodRepresentative_of_list [0,1,2,4,10,16,19] 590871
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_2 : GoodRepresentative 590881 := by
  apply goodRepresentative_of_list [0,5,10,16,19] 590881
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_3 : GoodRepresentative 590883 := by
  apply goodRepresentative_of_list [0,1,5,10,16,19] 590883
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_4 : GoodRepresentative 590887 := by
  apply goodRepresentative_of_list [0,1,2,5,10,16,19] 590887
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_5 : GoodRepresentative 590899 := by
  apply goodRepresentative_of_list [0,1,4,5,10,16,19] 590899
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_6 : GoodRepresentative 590901 := by
  apply goodRepresentative_of_list [0,2,4,5,10,16,19] 590901
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_7 : GoodRepresentative 590903 := by
  apply goodRepresentative_of_list [0,1,2,4,5,10,16,19] 590903
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_8 : GoodRepresentative 590993 := by
  apply goodRepresentative_of_list [0,4,7,10,16,19] 590993
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_9 : GoodRepresentative 590995 := by
  apply goodRepresentative_of_list [0,1,4,7,10,16,19] 590995
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_10 : GoodRepresentative 590999 := by
  apply goodRepresentative_of_list [0,1,2,4,7,10,16,19] 590999
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_11 : GoodRepresentative 591025 := by
  apply goodRepresentative_of_list [0,4,5,7,10,16,19] 591025
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_12 : GoodRepresentative 591027 := by
  apply goodRepresentative_of_list [0,1,4,5,7,10,16,19] 591027
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_13 : GoodRepresentative 591031 := by
  apply goodRepresentative_of_list [0,1,2,4,5,7,10,16,19] 591031
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_14 : GoodRepresentative 592903 := by
  apply goodRepresentative_of_list [0,1,2,10,11,16,19] 592903
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_15 : GoodRepresentative 592905 := by
  apply goodRepresentative_of_list [0,3,10,11,16,19] 592905
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_16 : GoodRepresentative 592907 := by
  apply goodRepresentative_of_list [0,1,3,10,11,16,19] 592907
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_17 : GoodRepresentative 592909 := by
  apply goodRepresentative_of_list [0,2,3,10,11,16,19] 592909
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_18 : GoodRepresentative 592919 := by
  apply goodRepresentative_of_list [0,1,2,4,10,11,16,19] 592919
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_19 : GoodRepresentative 592923 := by
  apply goodRepresentative_of_list [0,1,3,4,10,11,16,19] 592923
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_20 : GoodRepresentative 592935 := by
  apply goodRepresentative_of_list [0,1,2,5,10,11,16,19] 592935
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_21 : GoodRepresentative 592951 := by
  apply goodRepresentative_of_list [0,1,2,4,5,10,11,16,19] 592951
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_22 : GoodRepresentative 593027 := by
  apply goodRepresentative_of_list [0,1,7,10,11,16,19] 593027
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_23 : GoodRepresentative 593031 := by
  apply goodRepresentative_of_list [0,1,2,7,10,11,16,19] 593031
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_24 : GoodRepresentative 593033 := by
  apply goodRepresentative_of_list [0,3,7,10,11,16,19] 593033
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_25 : GoodRepresentative 593037 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,16,19] 593037
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_26 : GoodRepresentative 593045 := by
  apply goodRepresentative_of_list [0,2,4,7,10,11,16,19] 593045
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_27 : GoodRepresentative 593047 := by
  apply goodRepresentative_of_list [0,1,2,4,7,10,11,16,19] 593047
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_28 : GoodRepresentative 593059 := by
  apply goodRepresentative_of_list [0,1,5,7,10,11,16,19] 593059
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_29 : GoodRepresentative 593063 := by
  apply goodRepresentative_of_list [0,1,2,5,7,10,11,16,19] 593063
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_30 : GoodRepresentative 593077 := by
  apply goodRepresentative_of_list [0,2,4,5,7,10,11,16,19] 593077
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_22_31 : GoodRepresentative 593079 := by
  apply goodRepresentative_of_list [0,1,2,4,5,7,10,11,16,19] 593079
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks22 : List ℕ := [590869,590871,590881,590883,590887,590899,590901,590903,590993,590995,590999,591025,591027,591031,592903,592905,592907,592909,592919,592923,592935,592951,593027,593031,593033,593037,593045,593047,593059,593063,593077,593079]

theorem checkedMasks22_good : ∀ m ∈ checkedMasks22, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks22, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_22_0
  · exact good_22_1
  · exact good_22_2
  · exact good_22_3
  · exact good_22_4
  · exact good_22_5
  · exact good_22_6
  · exact good_22_7
  · exact good_22_8
  · exact good_22_9
  · exact good_22_10
  · exact good_22_11
  · exact good_22_12
  · exact good_22_13
  · exact good_22_14
  · exact good_22_15
  · exact good_22_16
  · exact good_22_17
  · exact good_22_18
  · exact good_22_19
  · exact good_22_20
  · exact good_22_21
  · exact good_22_22
  · exact good_22_23
  · exact good_22_24
  · exact good_22_25
  · exact good_22_26
  · exact good_22_27
  · exact good_22_28
  · exact good_22_29
  · exact good_22_30
  · exact good_22_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks22_good
