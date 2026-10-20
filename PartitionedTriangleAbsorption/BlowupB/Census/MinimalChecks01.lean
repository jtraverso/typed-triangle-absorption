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

theorem good_01_0 : GoodRepresentative 1424 := by decide +kernel

theorem good_01_1 : GoodRepresentative 1472 := by decide +kernel

theorem good_01_2 : GoodRepresentative 1488 := by decide +kernel

theorem good_01_3 : GoodRepresentative 1664 := by decide +kernel

theorem good_01_4 : GoodRepresentative 1665 := by decide +kernel

theorem good_01_5 : GoodRepresentative 1668 := by decide +kernel

theorem good_01_6 : GoodRepresentative 1669 := by decide +kernel

theorem good_01_7 : GoodRepresentative 1676 := by decide +kernel

theorem good_01_8 : GoodRepresentative 1677 := by decide +kernel

theorem good_01_9 : GoodRepresentative 1680 := by decide +kernel

theorem good_01_10 : GoodRepresentative 1696 := by decide +kernel

theorem good_01_11 : GoodRepresentative 1712 := by decide +kernel

theorem good_01_12 : GoodRepresentative 1920 := by decide +kernel

theorem good_01_13 : GoodRepresentative 1921 := by decide +kernel

theorem good_01_14 : GoodRepresentative 1924 := by decide +kernel

theorem good_01_15 : GoodRepresentative 1925 := by decide +kernel

theorem good_01_16 : GoodRepresentative 1932 := by decide +kernel

theorem good_01_17 : GoodRepresentative 1933 := by decide +kernel

theorem good_01_18 : GoodRepresentative 1936 := by decide +kernel

theorem good_01_19 : GoodRepresentative 2056 := by decide +kernel

theorem good_01_20 : GoodRepresentative 2057 := by decide +kernel

theorem good_01_21 : GoodRepresentative 2058 := by decide +kernel

theorem good_01_22 : GoodRepresentative 2059 := by decide +kernel

theorem good_01_23 : GoodRepresentative 2060 := by decide +kernel

theorem good_01_24 : GoodRepresentative 2061 := by decide +kernel

theorem good_01_25 : GoodRepresentative 2073 := by decide +kernel

theorem good_01_26 : GoodRepresentative 2074 := by decide +kernel

theorem good_01_27 : GoodRepresentative 2075 := by decide +kernel

theorem good_01_28 : GoodRepresentative 2184 := by decide +kernel

theorem good_01_29 : GoodRepresentative 2185 := by decide +kernel

theorem good_01_30 : GoodRepresentative 2188 := by decide +kernel

theorem good_01_31 : GoodRepresentative 2189 := by decide +kernel

def checkedMasks01 : List ℕ := [1424,1472,1488,1664,1665,1668,1669,1676,1677,1680,1696,1712,1920,1921,1924,1925,1932,1933,1936,2056,2057,2058,2059,2060,2061,2073,2074,2075,2184,2185,2188,2189]

theorem checkedMasks01_good : ∀ m ∈ checkedMasks01, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks01, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_01_0
  · exact good_01_1
  · exact good_01_2
  · exact good_01_3
  · exact good_01_4
  · exact good_01_5
  · exact good_01_6
  · exact good_01_7
  · exact good_01_8
  · exact good_01_9
  · exact good_01_10
  · exact good_01_11
  · exact good_01_12
  · exact good_01_13
  · exact good_01_14
  · exact good_01_15
  · exact good_01_16
  · exact good_01_17
  · exact good_01_18
  · exact good_01_19
  · exact good_01_20
  · exact good_01_21
  · exact good_01_22
  · exact good_01_23
  · exact good_01_24
  · exact good_01_25
  · exact good_01_26
  · exact good_01_27
  · exact good_01_28
  · exact good_01_29
  · exact good_01_30
  · exact good_01_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks01_good
