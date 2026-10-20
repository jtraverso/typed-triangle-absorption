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

theorem good_19_0 : GoodRepresentative 81417 := by
  apply goodRepresentative_of_list [0,3,9,10,11,12,13,16] 81417
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_1 : GoodRepresentative 81420 := by
  apply goodRepresentative_of_list [2,3,9,10,11,12,13,16] 81420
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_2 : GoodRepresentative 81421 := by
  apply goodRepresentative_of_list [0,2,3,9,10,11,12,13,16] 81421
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_3 : GoodRepresentative 81537 := by
  apply goodRepresentative_of_list [0,7,9,10,11,12,13,16] 81537
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_4 : GoodRepresentative 81541 := by
  apply goodRepresentative_of_list [0,2,7,9,10,11,12,13,16] 81541
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_5 : GoodRepresentative 81544 := by
  apply goodRepresentative_of_list [3,7,9,10,11,12,13,16] 81544
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_6 : GoodRepresentative 81545 := by
  apply goodRepresentative_of_list [0,3,7,9,10,11,12,13,16] 81545
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_7 : GoodRepresentative 81548 := by
  apply goodRepresentative_of_list [2,3,7,9,10,11,12,13,16] 81548
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_8 : GoodRepresentative 81549 := by
  apply goodRepresentative_of_list [0,2,3,7,9,10,11,12,13,16] 81549
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_9 : GoodRepresentative 99841 := by
  apply goodRepresentative_of_list [0,9,10,15,16] 99841
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_10 : GoodRepresentative 99843 := by
  apply goodRepresentative_of_list [0,1,9,10,15,16] 99843
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_11 : GoodRepresentative 99845 := by
  apply goodRepresentative_of_list [0,2,9,10,15,16] 99845
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_12 : GoodRepresentative 99849 := by
  apply goodRepresentative_of_list [0,3,9,10,15,16] 99849
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_13 : GoodRepresentative 99850 := by
  apply goodRepresentative_of_list [1,3,9,10,15,16] 99850
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_14 : GoodRepresentative 99851 := by
  apply goodRepresentative_of_list [0,1,3,9,10,15,16] 99851
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_15 : GoodRepresentative 99852 := by
  apply goodRepresentative_of_list [2,3,9,10,15,16] 99852
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_16 : GoodRepresentative 99853 := by
  apply goodRepresentative_of_list [0,2,3,9,10,15,16] 99853
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_17 : GoodRepresentative 99859 := by
  apply goodRepresentative_of_list [0,1,4,9,10,15,16] 99859
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_18 : GoodRepresentative 99865 := by
  apply goodRepresentative_of_list [0,3,4,9,10,15,16] 99865
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_19 : GoodRepresentative 99866 := by
  apply goodRepresentative_of_list [1,3,4,9,10,15,16] 99866
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_20 : GoodRepresentative 99867 := by
  apply goodRepresentative_of_list [0,1,3,4,9,10,15,16] 99867
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_21 : GoodRepresentative 99905 := by
  apply goodRepresentative_of_list [0,6,9,10,15,16] 99905
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_22 : GoodRepresentative 99907 := by
  apply goodRepresentative_of_list [0,1,6,9,10,15,16] 99907
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_23 : GoodRepresentative 99913 := by
  apply goodRepresentative_of_list [0,3,6,9,10,15,16] 99913
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_24 : GoodRepresentative 99914 := by
  apply goodRepresentative_of_list [1,3,6,9,10,15,16] 99914
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_25 : GoodRepresentative 99915 := by
  apply goodRepresentative_of_list [0,1,3,6,9,10,15,16] 99915
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_26 : GoodRepresentative 99923 := by
  apply goodRepresentative_of_list [0,1,4,6,9,10,15,16] 99923
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_27 : GoodRepresentative 99929 := by
  apply goodRepresentative_of_list [0,3,4,6,9,10,15,16] 99929
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_28 : GoodRepresentative 99930 := by
  apply goodRepresentative_of_list [1,3,4,6,9,10,15,16] 99930
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_29 : GoodRepresentative 99931 := by
  apply goodRepresentative_of_list [0,1,3,4,6,9,10,15,16] 99931
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_30 : GoodRepresentative 99969 := by
  apply goodRepresentative_of_list [0,7,9,10,15,16] 99969
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem good_19_31 : GoodRepresentative 99973 := by
  apply goodRepresentative_of_list [0,2,7,9,10,15,16] 99973
  · decide +kernel
  · decide +kernel
  · decide +kernel

def checkedMasks19 : List ℕ := [81417,81420,81421,81537,81541,81544,81545,81548,81549,99841,99843,99845,99849,99850,99851,99852,99853,99859,99865,99866,99867,99905,99907,99913,99914,99915,99923,99929,99930,99931,99969,99973]

theorem checkedMasks19_good : ∀ m ∈ checkedMasks19, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks19, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_19_0
  · exact good_19_1
  · exact good_19_2
  · exact good_19_3
  · exact good_19_4
  · exact good_19_5
  · exact good_19_6
  · exact good_19_7
  · exact good_19_8
  · exact good_19_9
  · exact good_19_10
  · exact good_19_11
  · exact good_19_12
  · exact good_19_13
  · exact good_19_14
  · exact good_19_15
  · exact good_19_16
  · exact good_19_17
  · exact good_19_18
  · exact good_19_19
  · exact good_19_20
  · exact good_19_21
  · exact good_19_22
  · exact good_19_23
  · exact good_19_24
  · exact good_19_25
  · exact good_19_26
  · exact good_19_27
  · exact good_19_28
  · exact good_19_29
  · exact good_19_30
  · exact good_19_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks19_good
