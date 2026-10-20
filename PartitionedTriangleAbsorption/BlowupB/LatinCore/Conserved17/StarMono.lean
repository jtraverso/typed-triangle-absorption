/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarCertificate
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Batch0

@[expose] public section

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17
open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General VertexSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Star03_0

noncomputable def K : Finset (Multiset (Fin 4)) := {{0, 0, 0}}

def c : Fin 4 → Fin 4 := ![0, 1, 1, 1]

def σ : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
def B : Finset (Fin 4) := ∅

private theorem sum_fin (f : Fin 4 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, (d 0 - (0)) / 2)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 1
    have z0 : d 0 = 0 := by
      by_contra h
      exact absurd (hsupp 0 h) (by unfold Link K; decide)
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 2
    have z0 : d 0 = 0 := by
      by_contra h
      exact absurd (hsupp 0 h) (by unfold Link K; decide)
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 3
    have z0 : d 0 = 0 := by
      by_contra h
      exact absurd (hsupp 0 h) (by unfold Link K; decide)
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 4 → Fin 4 → ℤ) : Multiset (Fin 4) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  refine ⟨canon u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [K, canon, FinT.coeffList, typeEdgeVec, Finset.sum_insert] <;>
    omega

def data : StarCertificateData K c 0 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by unfold FinT.LocalWalk Link K; decide +kernel
  σ := σ
  balanced := B
  local_sol := localSol
  scalar := scalar
  kill := by decide +kernel
  odd := by unfold Link K; decide +kernel
  bound := by decide +kernel
  m := 0
  g := 0
  plus := fun r => ⟨∅, fun _ => r, by simp, by simp [AntiEdgeSelection.incidentLoad], by simp⟩
  minus := fun r => ⟨∅, fun _ => r, by simp, by simp [AntiEdgeSelection.incidentLoad], by simp⟩
  modulus := 3
  modulus_three := dvd_refl _
  plus_ok := by simp [B]
  minus_ok := by simp [B]
  three := fun _ _ _ _ _ _ _ h => h
  small := by norm_num

theorem exists_certificate : ∃ L, BalFixer.ComponentCertFlexTL
    (componentFamily case03 (0 : Fin 4)) c (0 : Fin 4) L := by
  have hK : componentFamily case03 (0 : Fin 4) = K := by
    simp [componentFamily, case03, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star03_0

#print axioms Star03_0.exists_certificate

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

