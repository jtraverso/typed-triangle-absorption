/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.Uniqueness

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem good_07_0 : GoodRepresentative 10760 := by decide +kernel

theorem good_07_1 : GoodRepresentative 10761 := by decide +kernel

theorem good_07_2 : GoodRepresentative 10762 := by decide +kernel

theorem good_07_3 : GoodRepresentative 10763 := by decide +kernel

theorem good_07_4 : GoodRepresentative 10777 := by decide +kernel

theorem good_07_5 : GoodRepresentative 10778 := by decide +kernel

theorem good_07_6 : GoodRepresentative 10779 := by decide +kernel

theorem good_07_7 : GoodRepresentative 10896 := by decide +kernel

theorem good_07_8 : GoodRepresentative 10928 := by decide +kernel

theorem good_07_9 : GoodRepresentative 11400 := by decide +kernel

theorem good_07_10 : GoodRepresentative 11401 := by decide +kernel

theorem good_07_11 : GoodRepresentative 11404 := by decide +kernel

theorem good_07_12 : GoodRepresentative 11405 := by decide +kernel

theorem good_07_13 : GoodRepresentative 11780 := by decide +kernel

theorem good_07_14 : GoodRepresentative 11781 := by decide +kernel

theorem good_07_15 : GoodRepresentative 11785 := by decide +kernel

theorem good_07_16 : GoodRepresentative 11787 := by decide +kernel

theorem good_07_17 : GoodRepresentative 11788 := by decide +kernel

theorem good_07_18 : GoodRepresentative 11789 := by decide +kernel

theorem good_07_19 : GoodRepresentative 11803 := by decide +kernel

theorem good_07_20 : GoodRepresentative 11904 := by decide +kernel

theorem good_07_21 : GoodRepresentative 11905 := by decide +kernel

theorem good_07_22 : GoodRepresentative 11908 := by decide +kernel

theorem good_07_23 : GoodRepresentative 11909 := by decide +kernel

theorem good_07_24 : GoodRepresentative 11912 := by decide +kernel

theorem good_07_25 : GoodRepresentative 11913 := by decide +kernel

theorem good_07_26 : GoodRepresentative 11916 := by decide +kernel

theorem good_07_27 : GoodRepresentative 11917 := by decide +kernel

theorem good_07_28 : GoodRepresentative 11920 := by decide +kernel

theorem good_07_29 : GoodRepresentative 11936 := by decide +kernel

theorem good_07_30 : GoodRepresentative 11952 := by decide +kernel

theorem good_07_31 : GoodRepresentative 12425 := by decide +kernel

def checkedMasks07 : List ℕ := [10760,10761,10762,10763,10777,10778,10779,10896,10928,11400,11401,11404,11405,11780,11781,11785,11787,11788,11789,11803,11904,11905,11908,11909,11912,11913,11916,11917,11920,11936,11952,12425]

theorem checkedMasks07_good : ∀ m ∈ checkedMasks07, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks07, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_07_0
  · exact good_07_1
  · exact good_07_2
  · exact good_07_3
  · exact good_07_4
  · exact good_07_5
  · exact good_07_6
  · exact good_07_7
  · exact good_07_8
  · exact good_07_9
  · exact good_07_10
  · exact good_07_11
  · exact good_07_12
  · exact good_07_13
  · exact good_07_14
  · exact good_07_15
  · exact good_07_16
  · exact good_07_17
  · exact good_07_18
  · exact good_07_19
  · exact good_07_20
  · exact good_07_21
  · exact good_07_22
  · exact good_07_23
  · exact good_07_24
  · exact good_07_25
  · exact good_07_26
  · exact good_07_27
  · exact good_07_28
  · exact good_07_29
  · exact good_07_30
  · exact good_07_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks07_good
