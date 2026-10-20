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

theorem good_02_0 : GoodRepresentative 2312 := by decide +kernel

theorem good_02_1 : GoodRepresentative 2313 := by decide +kernel

theorem good_02_2 : GoodRepresentative 2316 := by decide +kernel

theorem good_02_3 : GoodRepresentative 2317 := by decide +kernel

theorem good_02_4 : GoodRepresentative 2320 := by decide +kernel

theorem good_02_5 : GoodRepresentative 2352 := by decide +kernel

theorem good_02_6 : GoodRepresentative 2561 := by decide +kernel

theorem good_02_7 : GoodRepresentative 2563 := by decide +kernel

theorem good_02_8 : GoodRepresentative 2564 := by decide +kernel

theorem good_02_9 : GoodRepresentative 2565 := by decide +kernel

theorem good_02_10 : GoodRepresentative 2568 := by decide +kernel

theorem good_02_11 : GoodRepresentative 2569 := by decide +kernel

theorem good_02_12 : GoodRepresentative 2570 := by decide +kernel

theorem good_02_13 : GoodRepresentative 2571 := by decide +kernel

theorem good_02_14 : GoodRepresentative 2572 := by decide +kernel

theorem good_02_15 : GoodRepresentative 2573 := by decide +kernel

theorem good_02_16 : GoodRepresentative 2577 := by decide +kernel

theorem good_02_17 : GoodRepresentative 2579 := by decide +kernel

theorem good_02_18 : GoodRepresentative 2584 := by decide +kernel

theorem good_02_19 : GoodRepresentative 2585 := by decide +kernel

theorem good_02_20 : GoodRepresentative 2586 := by decide +kernel

theorem good_02_21 : GoodRepresentative 2587 := by decide +kernel

theorem good_02_22 : GoodRepresentative 2689 := by decide +kernel

theorem good_02_23 : GoodRepresentative 2692 := by decide +kernel

theorem good_02_24 : GoodRepresentative 2693 := by decide +kernel

theorem good_02_25 : GoodRepresentative 2696 := by decide +kernel

theorem good_02_26 : GoodRepresentative 2697 := by decide +kernel

theorem good_02_27 : GoodRepresentative 2700 := by decide +kernel

theorem good_02_28 : GoodRepresentative 2701 := by decide +kernel

theorem good_02_29 : GoodRepresentative 2704 := by decide +kernel

theorem good_02_30 : GoodRepresentative 2720 := by decide +kernel

theorem good_02_31 : GoodRepresentative 2736 := by decide +kernel

def checkedMasks02 : List ℕ := [2312,2313,2316,2317,2320,2352,2561,2563,2564,2565,2568,2569,2570,2571,2572,2573,2577,2579,2584,2585,2586,2587,2689,2692,2693,2696,2697,2700,2701,2704,2720,2736]

theorem checkedMasks02_good : ∀ m ∈ checkedMasks02, GoodRepresentative m := by
  intro m hm
  simp only [checkedMasks02, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_02_0
  · exact good_02_1
  · exact good_02_2
  · exact good_02_3
  · exact good_02_4
  · exact good_02_5
  · exact good_02_6
  · exact good_02_7
  · exact good_02_8
  · exact good_02_9
  · exact good_02_10
  · exact good_02_11
  · exact good_02_12
  · exact good_02_13
  · exact good_02_14
  · exact good_02_15
  · exact good_02_16
  · exact good_02_17
  · exact good_02_18
  · exact good_02_19
  · exact good_02_20
  · exact good_02_21
  · exact good_02_22
  · exact good_02_23
  · exact good_02_24
  · exact good_02_25
  · exact good_02_26
  · exact good_02_27
  · exact good_02_28
  · exact good_02_29
  · exact good_02_30
  · exact good_02_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks02_good
