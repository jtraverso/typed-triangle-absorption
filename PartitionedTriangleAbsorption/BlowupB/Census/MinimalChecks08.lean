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

theorem good_08_0 : GoodRepresentative 12428 := by
  apply goodRepresentative_of_list [2,3,7,12,13] 12428
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_1 : GoodRepresentative 12429 := by
  apply goodRepresentative_of_list [0,2,3,7,12,13] 12429
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_2 : GoodRepresentative 12804 := by
  apply goodRepresentative_of_list [2,9,12,13] 12804
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_3 : GoodRepresentative 12805 := by
  apply goodRepresentative_of_list [0,2,9,12,13] 12805
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_4 : GoodRepresentative 12812 := by
  apply goodRepresentative_of_list [2,3,9,12,13] 12812
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_5 : GoodRepresentative 12813 := by
  apply goodRepresentative_of_list [0,2,3,9,12,13] 12813
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_6 : GoodRepresentative 12929 := by
  apply goodRepresentative_of_list [0,7,9,12,13] 12929
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_7 : GoodRepresentative 12933 := by
  apply goodRepresentative_of_list [0,2,7,9,12,13] 12933
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_8 : GoodRepresentative 12937 := by
  apply goodRepresentative_of_list [0,3,7,9,12,13] 12937
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_9 : GoodRepresentative 12940 := by
  apply goodRepresentative_of_list [2,3,7,9,12,13] 12940
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_10 : GoodRepresentative 12941 := by
  apply goodRepresentative_of_list [0,2,3,7,9,12,13] 12941
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_11 : GoodRepresentative 13449 := by
  apply goodRepresentative_of_list [0,3,7,10,12,13] 13449
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_12 : GoodRepresentative 13452 := by
  apply goodRepresentative_of_list [2,3,7,10,12,13] 13452
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_13 : GoodRepresentative 13453 := by
  apply goodRepresentative_of_list [0,2,3,7,10,12,13] 13453
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_14 : GoodRepresentative 13829 := by
  apply goodRepresentative_of_list [0,2,9,10,12,13] 13829
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_15 : GoodRepresentative 13836 := by
  apply goodRepresentative_of_list [2,3,9,10,12,13] 13836
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_16 : GoodRepresentative 13837 := by
  apply goodRepresentative_of_list [0,2,3,9,10,12,13] 13837
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_17 : GoodRepresentative 13952 := by
  apply goodRepresentative_of_list [7,9,10,12,13] 13952
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_18 : GoodRepresentative 13953 := by
  apply goodRepresentative_of_list [0,7,9,10,12,13] 13953
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_19 : GoodRepresentative 13956 := by
  apply goodRepresentative_of_list [2,7,9,10,12,13] 13956
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_20 : GoodRepresentative 13957 := by
  apply goodRepresentative_of_list [0,2,7,9,10,12,13] 13957
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_21 : GoodRepresentative 13960 := by
  apply goodRepresentative_of_list [3,7,9,10,12,13] 13960
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_22 : GoodRepresentative 13961 := by
  apply goodRepresentative_of_list [0,3,7,9,10,12,13] 13961
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_23 : GoodRepresentative 13964 := by
  apply goodRepresentative_of_list [2,3,7,9,10,12,13] 13964
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_24 : GoodRepresentative 13965 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,12,13] 13965
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_25 : GoodRepresentative 14476 := by
  apply goodRepresentative_of_list [2,3,7,11,12,13] 14476
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_26 : GoodRepresentative 14477 := by
  apply goodRepresentative_of_list [0,2,3,7,11,12,13] 14477
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_27 : GoodRepresentative 14860 := by
  apply goodRepresentative_of_list [2,3,9,11,12,13] 14860
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_28 : GoodRepresentative 14861 := by
  apply goodRepresentative_of_list [0,2,3,9,11,12,13] 14861
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_29 : GoodRepresentative 14977 := by
  apply goodRepresentative_of_list [0,7,9,11,12,13] 14977
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_30 : GoodRepresentative 14981 := by
  apply goodRepresentative_of_list [0,2,7,9,11,12,13] 14981
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_08_31 : GoodRepresentative 14984 := by
  apply goodRepresentative_of_list [3,7,9,11,12,13] 14984
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks08 : List ℕ := [12428,12429,12804,12805,12812,12813,12929,12933,12937,12940,12941,13449,13452,13453,13829,13836,13837,13952,13953,13956,13957,13960,13961,13964,13965,14476,14477,14860,14861,14977,14981,14984]

theorem checkedMasks08_good : ∀ m ∈ checkedMasks08, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks08, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_08_0
  · exact good_08_1
  · exact good_08_2
  · exact good_08_3
  · exact good_08_4
  · exact good_08_5
  · exact good_08_6
  · exact good_08_7
  · exact good_08_8
  · exact good_08_9
  · exact good_08_10
  · exact good_08_11
  · exact good_08_12
  · exact good_08_13
  · exact good_08_14
  · exact good_08_15
  · exact good_08_16
  · exact good_08_17
  · exact good_08_18
  · exact good_08_19
  · exact good_08_20
  · exact good_08_21
  · exact good_08_22
  · exact good_08_23
  · exact good_08_24
  · exact good_08_25
  · exact good_08_26
  · exact good_08_27
  · exact good_08_28
  · exact good_08_29
  · exact good_08_30
  · exact good_08_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks08_good
