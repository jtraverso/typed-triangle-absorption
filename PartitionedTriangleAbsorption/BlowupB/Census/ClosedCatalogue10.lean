/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Census.ClosedBasic
public import PartitionedTriangleAbsorption.BlowupB.Census.MinimalChecks10

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PartitionedTriangleAbsorption.BlowupB.FiniteCensus

theorem closed_10_0 :
    Closed765 (decode (actCode 4 (decodeMask 42637))) := by
  have he : decode (actCode 4 (decodeMask 42637)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR506 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR506)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_10_1 :
    Closed765 (decode (actCode 4 (decodeMask 43653))) := by
  have he : decode (actCode 4 (decodeMask 43653)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL275 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨275, by decide +kernel⟩)))

theorem closed_10_2 :
    Closed765 (decode (actCode 5 (decodeMask 43657))) := by
  have he : decode (actCode 5 (decodeMask 43657)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR048 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR048)⟩))))))))))))))))

theorem closed_10_3 :
    Closed765 (decode (actCode 4 (decodeMask 43661))) := by
  have he : decode (actCode 4 (decodeMask 43661)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR507 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR507)))⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_10_4 :
    Closed765 (decode (actCode 4 (decodeMask 44677))) := by
  have he : decode (actCode 4 (decodeMask 44677)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL298 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨298, by decide +kernel⟩)))

theorem closed_10_5 :
    Closed765 (decode (actCode 5 (decodeMask 44681))) := by
  have he : decode (actCode 5 (decodeMask 44681)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR049 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR049))⟩))))))))))))))))

theorem closed_10_6 :
    Closed765 (decode (actCode 18 (decodeMask 44684))) := by
  have he : decode (actCode 18 (decodeMask 44684)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR508 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR508)⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_10_7 :
    Closed765 (decode (actCode 4 (decodeMask 44685))) := by
  have he : decode (actCode 4 (decodeMask 44685)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR509 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR509))⟩))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem closed_10_8 :
    Closed765 (decode (actCode 0 (decodeMask 47756))) := by
  have he : decode (actCode 0 (decodeMask 47756)) =
      PartitionedTriangleAbsorption.TypedApplicationLinks.F1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.TypedApplicationLinks.F1)⟩))))))))))))))))))))

theorem closed_10_9 :
    Closed765 (decode (actCode 4 (decodeMask 47757))) := by
  have he : decode (actCode 4 (decodeMask 47757)) =
      PaddedFbit.Fbit := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedFbit.Fbit)⟩)))))))))))))))))))

theorem closed_10_10 :
    Closed765 (decode (actCode 4 (decodeMask 48781))) := by
  have he : decode (actCode 4 (decodeMask 48781)) =
      PaddedFbit.Fbit333 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedFbit.Fbit333))⟩)))))))))))))))))))

theorem closed_10_11 :
    Closed765 (decode (actCode 12 (decodeMask 66568))) := by
  have he : decode (actCode 12 (decodeMask 66568)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL003 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨3, by decide +kernel⟩)))

theorem closed_10_12 :
    Closed765 (decode (actCode 3 (decodeMask 66569))) := by
  have he : decode (actCode 3 (decodeMask 66569)) =
      PaddedComponents.KE2 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inr (Or.inl (identity_perm_family PaddedComponents.KE2))⟩))))))

theorem closed_10_13 :
    Closed765 (decode (actCode 7 (decodeMask 66570))) := by
  have he : decode (actCode 7 (decodeMask 66570)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL047 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨47, by decide +kernel⟩)))

theorem closed_10_14 :
    Closed765 (decode (actCode 1 (decodeMask 66571))) := by
  have he : decode (actCode 1 (decodeMask 66571)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR050 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR050)))⟩))))))))))))))))

theorem closed_10_15 :
    Closed765 (decode (actCode 7 (decodeMask 66584))) := by
  have he : decode (actCode 7 (decodeMask 66584)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL032 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨32, by decide +kernel⟩)))

theorem closed_10_16 :
    Closed765 (decode (actCode 3 (decodeMask 66585))) := by
  have he : decode (actCode 3 (decodeMask 66585)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR051 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inr (Or.inr (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR051)))⟩))))))))))))))))

theorem closed_10_17 :
    Closed765 (decode (actCode 7 (decodeMask 66586))) := by
  have he : decode (actCode 7 (decodeMask 66586)) =
      PaddedComponents.KM1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KM1)⟩))))))))))))

theorem closed_10_18 :
    Closed765 (decode (actCode 1 (decodeMask 66587))) := by
  have he : decode (actCode 1 (decodeMask 66587)) =
      PaddedComponents.FM06 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM06, (by exact List.get_mem PaddedComponents.monoList ⟨5, by decide +kernel⟩), identity_perm_family PaddedComponents.FM06⟩)))))))))))))))

theorem closed_10_19 :
    Closed765 (decode (actCode 1 (decodeMask 66625))) := by
  have he : decode (actCode 1 (decodeMask 66625)) =
      PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.case13.F := by decide +kernel
  rw [he]
  exact Or.inr ⟨13, rfl⟩

theorem closed_10_20 :
    Closed765 (decode (actCode 1 (decodeMask 66627))) := by
  have he : decode (actCode 1 (decodeMask 66627)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL099 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨99, by decide +kernel⟩)))

theorem closed_10_21 :
    Closed765 (decode (actCode 7 (decodeMask 66632))) := by
  have he : decode (actCode 7 (decodeMask 66632)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL054 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨54, by decide +kernel⟩)))

theorem closed_10_22 :
    Closed765 (decode (actCode 3 (decodeMask 66633))) := by
  have he : decode (actCode 3 (decodeMask 66633)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL107 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨107, by decide +kernel⟩)))

theorem closed_10_23 :
    Closed765 (decode (actCode 7 (decodeMask 66634))) := by
  have he : decode (actCode 7 (decodeMask 66634)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR052 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR052)⟩)))))))))))))))))

theorem closed_10_24 :
    Closed765 (decode (actCode 1 (decodeMask 66635))) := by
  have he : decode (actCode 1 (decodeMask 66635)) =
      PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR053 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨1, Or.inr (Or.inl (identity_perm_family PartitionedTriangleAbsorption.BlowupB.Flex.Par.F_PAR053))⟩)))))))))))))))))

theorem closed_10_25 :
    Closed765 (decode (actCode 1 (decodeMask 66643))) := by
  have he : decode (actCode 1 (decodeMask 66643)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL183 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨183, by decide +kernel⟩)))

theorem closed_10_26 :
    Closed765 (decode (actCode 7 (decodeMask 66648))) := by
  have he : decode (actCode 7 (decodeMask 66648)) =
      PaddedComponents.KCX1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KCX1)⟩)))))))))

theorem closed_10_27 :
    Closed765 (decode (actCode 3 (decodeMask 66649))) := by
  have he : decode (actCode 3 (decodeMask 66649)) =
      PaddedComponents.KCT1 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, Or.inl (identity_perm_family PaddedComponents.KCT1)⟩))))))))))

theorem closed_10_28 :
    Closed765 (decode (actCode 7 (decodeMask 66650))) := by
  have he : decode (actCode 7 (decodeMask 66650)) =
      PaddedComponents.FM07 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM07, (by exact List.get_mem PaddedComponents.monoList ⟨6, by decide +kernel⟩), identity_perm_family PaddedComponents.FM07⟩)))))))))))))))

theorem closed_10_29 :
    Closed765 (decode (actCode 1 (decodeMask 66651))) := by
  have he : decode (actCode 1 (decodeMask 66651)) =
      PaddedComponents.FM11 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨1, PaddedComponents.FM11, (by exact List.get_mem PaddedComponents.monoList ⟨10, by decide +kernel⟩), identity_perm_family PaddedComponents.FM11⟩)))))))))))))))

theorem closed_10_30 :
    Closed765 (decode (actCode 3 (decodeMask 67073))) := by
  have he : decode (actCode 3 (decodeMask 67073)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL052 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨52, by decide +kernel⟩)))

theorem closed_10_31 :
    Closed765 (decode (actCode 7 (decodeMask 67074))) := by
  have he : decode (actCode 7 (decodeMask 67074)) =
      PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.F_BAL050 := by decide +kernel
  rw [he]
  exact Or.inl (Or.inr ((by exact List.get_mem PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.balClosed ⟨50, by decide +kernel⟩)))

theorem checkedMasks10_closed (m : ℕ) (hm : m ∈ checkedMasks10) :
    ∃ s : Equiv.Perm (Fin 4),
      Closed765 ((decode (decodeMask m)).image (Multiset.map s)) := by
  simp only [checkedMasks10, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_0
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_1
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_10_2
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_3
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_4
  · refine ⟨sigma 5, ?_⟩
    rw [← decode_actCode]
    exact closed_10_5
  · refine ⟨sigma 18, ?_⟩
    rw [← decode_actCode]
    exact closed_10_6
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_7
  · refine ⟨sigma 0, ?_⟩
    rw [← decode_actCode]
    exact closed_10_8
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_9
  · refine ⟨sigma 4, ?_⟩
    rw [← decode_actCode]
    exact closed_10_10
  · refine ⟨sigma 12, ?_⟩
    rw [← decode_actCode]
    exact closed_10_11
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_10_12
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_13
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_14
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_15
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_10_16
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_17
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_18
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_19
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_20
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_21
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_10_22
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_23
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_24
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_25
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_26
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_10_27
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_28
  · refine ⟨sigma 1, ?_⟩
    rw [← decode_actCode]
    exact closed_10_29
  · refine ⟨sigma 3, ?_⟩
    rw [← decode_actCode]
    exact closed_10_30
  · refine ⟨sigma 7, ?_⟩
    rw [← decode_actCode]
    exact closed_10_31

end PartitionedTriangleAbsorption.BlowupB.FiniteCensus

#print axioms PartitionedTriangleAbsorption.BlowupB.FiniteCensus.checkedMasks10_closed
