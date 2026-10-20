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

theorem good_09_0 : GoodRepresentative 14985 := by
  apply goodRepresentative_of_list [0,3,7,9,11,12,13] 14985
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_1 : GoodRepresentative 14988 := by
  apply goodRepresentative_of_list [2,3,7,9,11,12,13] 14988
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_2 : GoodRepresentative 14989 := by
  apply goodRepresentative_of_list [0,2,3,7,9,11,12,13] 14989
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_3 : GoodRepresentative 15501 := by
  apply goodRepresentative_of_list [0,2,3,7,10,11,12,13] 15501
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_4 : GoodRepresentative 15885 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,12,13] 15885
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_5 : GoodRepresentative 16000 := by
  apply goodRepresentative_of_list [7,9,10,11,12,13] 16000
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_6 : GoodRepresentative 16001 := by
  apply goodRepresentative_of_list [0,7,9,10,11,12,13] 16001
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_7 : GoodRepresentative 16004 := by
  apply goodRepresentative_of_list [2,7,9,10,11,12,13] 16004
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_8 : GoodRepresentative 16005 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,12,13] 16005
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_9 : GoodRepresentative 16008 := by
  apply goodRepresentative_of_list [3,7,9,10,11,12,13] 16008
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_10 : GoodRepresentative 16009 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,12,13] 16009
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_11 : GoodRepresentative 16012 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,12,13] 16012
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_12 : GoodRepresentative 16013 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,13] 16013
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_13 : GoodRepresentative 16736 := by
  apply goodRepresentative_of_list [5,6,8,14] 16736
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_14 : GoodRepresentative 17665 := by
  apply goodRepresentative_of_list [0,8,10,14] 17665
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_15 : GoodRepresentative 17669 := by
  apply goodRepresentative_of_list [0,2,8,10,14] 17669
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_16 : GoodRepresentative 17676 := by
  apply goodRepresentative_of_list [2,3,8,10,14] 17676
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_17 : GoodRepresentative 17677 := by
  apply goodRepresentative_of_list [0,2,3,8,10,14] 17677
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_18 : GoodRepresentative 19717 := by
  apply goodRepresentative_of_list [0,2,8,10,11,14] 19717
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_19 : GoodRepresentative 19721 := by
  apply goodRepresentative_of_list [0,3,8,10,11,14] 19721
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_20 : GoodRepresentative 19724 := by
  apply goodRepresentative_of_list [2,3,8,10,11,14] 19724
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_21 : GoodRepresentative 19725 := by
  apply goodRepresentative_of_list [0,2,3,8,10,11,14] 19725
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_22 : GoodRepresentative 22796 := by
  apply goodRepresentative_of_list [2,3,8,11,12,14] 22796
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_23 : GoodRepresentative 22797 := by
  apply goodRepresentative_of_list [0,2,3,8,11,12,14] 22797
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_24 : GoodRepresentative 23821 := by
  apply goodRepresentative_of_list [0,2,3,8,10,11,12,14] 23821
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_25 : GoodRepresentative 41601 := by
  apply goodRepresentative_of_list [0,7,9,13,15] 41601
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_26 : GoodRepresentative 41605 := by
  apply goodRepresentative_of_list [0,2,7,9,13,15] 41605
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_27 : GoodRepresentative 41613 := by
  apply goodRepresentative_of_list [0,2,3,7,9,13,15] 41613
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_28 : GoodRepresentative 42625 := by
  apply goodRepresentative_of_list [0,7,9,10,13,15] 42625
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_29 : GoodRepresentative 42628 := by
  apply goodRepresentative_of_list [2,7,9,10,13,15] 42628
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_30 : GoodRepresentative 42629 := by
  apply goodRepresentative_of_list [0,2,7,9,10,13,15] 42629
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_09_31 : GoodRepresentative 42636 := by
  apply goodRepresentative_of_list [2,3,7,9,10,13,15] 42636
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks09 : List ℕ := [14985,14988,14989,15501,15885,16000,16001,16004,16005,16008,16009,16012,16013,16736,17665,17669,17676,17677,19717,19721,19724,19725,22796,22797,23821,41601,41605,41613,42625,42628,42629,42636]

theorem checkedMasks09_good : ∀ m ∈ checkedMasks09, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks09, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_09_0
  · exact good_09_1
  · exact good_09_2
  · exact good_09_3
  · exact good_09_4
  · exact good_09_5
  · exact good_09_6
  · exact good_09_7
  · exact good_09_8
  · exact good_09_9
  · exact good_09_10
  · exact good_09_11
  · exact good_09_12
  · exact good_09_13
  · exact good_09_14
  · exact good_09_15
  · exact good_09_16
  · exact good_09_17
  · exact good_09_18
  · exact good_09_19
  · exact good_09_20
  · exact good_09_21
  · exact good_09_22
  · exact good_09_23
  · exact good_09_24
  · exact good_09_25
  · exact good_09_26
  · exact good_09_27
  · exact good_09_28
  · exact good_09_29
  · exact good_09_30
  · exact good_09_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks09_good
