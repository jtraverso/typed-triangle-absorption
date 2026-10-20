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

theorem good_00_0 : GoodRepresentative 96 := by decide +kernel

theorem good_00_1 : GoodRepresentative 192 := by decide +kernel

theorem good_00_2 : GoodRepresentative 208 := by decide +kernel

theorem good_00_3 : GoodRepresentative 224 := by decide +kernel

theorem good_00_4 : GoodRepresentative 352 := by decide +kernel

theorem good_00_5 : GoodRepresentative 464 := by decide +kernel

theorem good_00_6 : GoodRepresentative 656 := by decide +kernel

theorem good_00_7 : GoodRepresentative 688 := by decide +kernel

theorem good_00_8 : GoodRepresentative 1036 := by decide +kernel

theorem good_00_9 : GoodRepresentative 1037 := by decide +kernel

theorem good_00_10 : GoodRepresentative 1160 := by decide +kernel

theorem good_00_11 : GoodRepresentative 1161 := by decide +kernel

theorem good_00_12 : GoodRepresentative 1164 := by decide +kernel

theorem good_00_13 : GoodRepresentative 1165 := by decide +kernel

theorem good_00_14 : GoodRepresentative 1216 := by decide +kernel

theorem good_00_15 : GoodRepresentative 1232 := by decide +kernel

theorem good_00_16 : GoodRepresentative 1280 := by decide +kernel

theorem good_00_17 : GoodRepresentative 1281 := by decide +kernel

theorem good_00_18 : GoodRepresentative 1284 := by decide +kernel

theorem good_00_19 : GoodRepresentative 1285 := by decide +kernel

theorem good_00_20 : GoodRepresentative 1292 := by decide +kernel

theorem good_00_21 : GoodRepresentative 1293 := by decide +kernel

theorem good_00_22 : GoodRepresentative 1296 := by decide +kernel

theorem good_00_23 : GoodRepresentative 1312 := by decide +kernel

theorem good_00_24 : GoodRepresentative 1328 := by decide +kernel

theorem good_00_25 : GoodRepresentative 1409 := by decide +kernel

theorem good_00_26 : GoodRepresentative 1412 := by decide +kernel

theorem good_00_27 : GoodRepresentative 1413 := by decide +kernel

theorem good_00_28 : GoodRepresentative 1416 := by decide +kernel

theorem good_00_29 : GoodRepresentative 1417 := by decide +kernel

theorem good_00_30 : GoodRepresentative 1420 := by decide +kernel

theorem good_00_31 : GoodRepresentative 1421 := by decide +kernel

def checkedMasks00 : List ℕ := [96,192,208,224,352,464,656,688,1036,1037,1160,1161,1164,1165,1216,1232,1280,1281,1284,1285,1292,1293,1296,1312,1328,1409,1412,1413,1416,1417,1420,1421]

theorem checkedMasks00_good : ∀ m ∈ checkedMasks00, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks00, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_00_0
  · exact good_00_1
  · exact good_00_2
  · exact good_00_3
  · exact good_00_4
  · exact good_00_5
  · exact good_00_6
  · exact good_00_7
  · exact good_00_8
  · exact good_00_9
  · exact good_00_10
  · exact good_00_11
  · exact good_00_12
  · exact good_00_13
  · exact good_00_14
  · exact good_00_15
  · exact good_00_16
  · exact good_00_17
  · exact good_00_18
  · exact good_00_19
  · exact good_00_20
  · exact good_00_21
  · exact good_00_22
  · exact good_00_23
  · exact good_00_24
  · exact good_00_25
  · exact good_00_26
  · exact good_00_27
  · exact good_00_28
  · exact good_00_29
  · exact good_00_30
  · exact good_00_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks00_good
