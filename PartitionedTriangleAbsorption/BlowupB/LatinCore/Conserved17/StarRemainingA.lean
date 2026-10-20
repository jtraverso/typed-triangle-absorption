/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarCertificate
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.All

@[expose] public section

/-! Checked non-Latin component witnesses, compilation batch A. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17
open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General VertexSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Star02_0

def K : Finset (Multiset (Fin 6)) := {{0, 0, 0}}

def c : Fin 6 → Fin 6 := ![0, 1, 1, 3, 1, 3]

def σ : Fin 6 → Fin 6 → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 6) := ∅

private theorem sum_fin (f : Fin 6 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 5
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  have s50 := hs 5 0
  have s51 := hs 5 1
  have s52 := hs 5 2
  have s53 := hs 5 3
  have s54 := hs 5 4
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
    (componentFamily case02 (0 : Fin 6)) c (0 : Fin 6) L := by
  have hK : componentFamily case02 (0 : Fin 6) = K := by
    simp [componentFamily, case02, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star02_0

#print axioms Star02_0.exists_certificate

namespace Star02_3

def K : Finset (Multiset (Fin 6)) := {{3, 5, 5}}

def c : Fin 6 → Fin 6 := ![0, 1, 1, 3, 1, 3]

def σ : Fin 6 → Fin 6 → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 1]]
def B : Finset (Fin 6) := {5}

private theorem sum_fin (f : Fin 6 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 5, 5}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 5, 5}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 5, 5}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 5, 5}, d 5 / 2)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 5, 5}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 5
    have z0 : d 0 = 0 := by
      by_contra h
      exact absurd (hsupp 0 h) (by unfold Link K; decide)
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    have hb := hbal (by decide : (5 : Fin 6) ∈ B)
    simp [σ, sum_fin] at hb
    refine ⟨FinT.coeffList [({3, 5, 5}, d 3)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({3, 5, 5}, u 5 3 / 2)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 3 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z00 : u 0 0 = 0 := hf 0 0 (by unfold Link K; decide)
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have hb := hbal 5 (by decide)
  simp [σ, sum_fin] at hb
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  have s50 := hs 5 0
  have s51 := hs 5 1
  have s52 := hs 5 2
  have s53 := hs 5 3
  have s54 := hs 5 4
  refine ⟨canon u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [K, canon, FinT.coeffList, typeEdgeVec, Finset.sum_insert] <;>
    omega

def TP (_ : Fin 6) : BalFixer.RootedTemplate 6 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 0)}, ![5, 5, 3, 5, 5],
    by decide +kernel, by decide +kernel, by decide +kernel⟩
def TM (_ : Fin 6) : BalFixer.RootedTemplate 6 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}, ![5, 3, 5, 5, 3],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def β : Fin 6 → Fin 6 → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 2]]

theorem vertex_three : ∀ r (d : Fin 6 → ℤ),
    (∀ j, d j ≠ 0 → ∃ l, Link K r j l) → (2 : ℤ) ∣ ∑ j, d j →
    (r ∈ B → ∑ j, σ r j * d j = 0) → (3 : ℤ) ∣ ∑ j, β r j * d j := by
  intro r d hsupp hpar hbal
  fin_cases r
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · have hb := hbal (by decide)
    simp [σ, β, sum_fin] at hb ⊢
    omega

def data : StarCertificateData K c 3 where
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
  m := 4
  g := 5
  plus := TP
  minus := TM
  modulus := 1
  modulus_three := by norm_num
  plus_ok := by
    intro r hr _
    have hr' : r = 5 := by simpa [B] using hr
    subst r
    exact ⟨by decide +kernel, by unfold Link; decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  minus_ok := by
    intro r hr _
    have hr' : r = 5 := by simpa [B] using hr
    subst r
    exact ⟨by decide +kernel, by unfold Link; decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  three := fun q E hl ha _ he hb _ =>
    BalFixer.three_dvd_of_pot σ B β (by unfold Link K; decide +kernel)
      vertex_three hl ha he hb
  small := by norm_num

theorem exists_certificate : ∃ L, BalFixer.ComponentCertFlexTL
    (componentFamily case02 (3 : Fin 6)) c (3 : Fin 6) L := by
  have hK : componentFamily case02 (3 : Fin 6) = K := by
    simp [componentFamily, case02, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star02_3

#print axioms Star02_3.exists_certificate

namespace Star04_0

def K : Finset (Multiset (Fin 5)) := {{0, 0, 0}}

def c : Fin 5 → Fin 5 := ![0, 1, 1, 1, 4]

def σ : Fin 5 → Fin 5 → ℤ := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
def B : Finset (Fin 5) := ∅

private theorem sum_fin (f : Fin 5 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 5 → Fin 5 → ℤ) : Multiset (Fin 5) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
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
    (componentFamily case04 (0 : Fin 5)) c (0 : Fin 5) L := by
  have hK : componentFamily case04 (0 : Fin 5) = K := by
    simp [componentFamily, case04, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star04_0

#print axioms Star04_0.exists_certificate

namespace Star04_4

def K : Finset (Multiset (Fin 5)) := {{4, 4, 4}}

def c : Fin 5 → Fin 5 := ![0, 1, 1, 1, 4]

def σ : Fin 5 → Fin 5 → ℤ := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
def B : Finset (Fin 5) := ∅

private theorem sum_fin (f : Fin 5 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({4, 4, 4}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({4, 4, 4}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({4, 4, 4}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({4, 4, 4}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    refine ⟨FinT.coeffList [({4, 4, 4}, (d 4 - (0)) / 2)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 5 → Fin 5 → ℤ) : Multiset (Fin 5) → ℤ :=
  FinT.coeffList [({4, 4, 4}, (u 4 4 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 4 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z00 : u 0 0 = 0 := hf 0 0 (by unfold Link K; decide)
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  refine ⟨canon u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [K, canon, FinT.coeffList, typeEdgeVec, Finset.sum_insert] <;>
    omega

def data : StarCertificateData K c 4 where
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
    (componentFamily case04 (4 : Fin 5)) c (4 : Fin 5) L := by
  have hK : componentFamily case04 (4 : Fin 5) = K := by
    simp [componentFamily, case04, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star04_4

#print axioms Star04_4.exists_certificate

namespace Star05_0

def K : Finset (Multiset (Fin 5)) := {{0, 0, 0}, {0, 0, 1}}

def c : Fin 5 → Fin 5 := ![0, 0, 2, 2, 2]

def σ : Fin 5 → Fin 5 → ℤ := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
def B : Finset (Fin 5) := ∅

private theorem sum_fin (f : Fin 5 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, (d 0 - (d 1)) / 2), ({0, 0, 1}, d 1)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 1
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, d 0 / 2)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 5 → Fin 5 → ℤ) : Multiset (Fin 5) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (u 0 1 / 2)) / 3), ({0, 0, 1}, u 0 1 / 2)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
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
    (componentFamily case05 (0 : Fin 5)) c (0 : Fin 5) L := by
  have hK : componentFamily case05 (0 : Fin 5) = K := by
    simp [componentFamily, case05, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star05_0

#print axioms Star05_0.exists_certificate

namespace Star06_0

def K : Finset (Multiset (Fin 5)) := {{0, 0, 0}}

def c : Fin 5 → Fin 5 := ![0, 1, 1, 1, 1]

def σ : Fin 5 → Fin 5 → ℤ := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
def B : Finset (Fin 5) := ∅

private theorem sum_fin (f : Fin 5 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 5 → Fin 5 → ℤ) : Multiset (Fin 5) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
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
    (componentFamily case06 (0 : Fin 5)) c (0 : Fin 5) L := by
  have hK : componentFamily case06 (0 : Fin 5) = K := by
    simp [componentFamily, case06, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star06_0

#print axioms Star06_0.exists_certificate

namespace Star07_0

def K : Finset (Multiset (Fin 6)) := {{0, 0, 1}, {0, 0, 3}}

def c : Fin 6 → Fin 6 := ![0, 0, 2, 0, 2, 2]

def σ : Fin 6 → Fin 6 → ℤ := ![![1, -1, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 6) := {0}

private theorem sum_fin (f : Fin 6 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    have hb := hbal (by decide : (0 : Fin 6) ∈ B)
    simp [σ, sum_fin] at hb
    refine ⟨FinT.coeffList [({0, 0, 1}, d 1), ({0, 0, 3}, d 3)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 1
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, d 0 / 2), ({0, 0, 3}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 3
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0), ({0, 0, 3}, d 0 / 2)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 5
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({0, 0, 1}, u 0 1 / 2), ({0, 0, 3}, u 0 3 / 2)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have hb := hbal 0 (by decide)
  simp [σ, sum_fin] at hb
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  have s50 := hs 5 0
  have s51 := hs 5 1
  have s52 := hs 5 2
  have s53 := hs 5 3
  have s54 := hs 5 4
  refine ⟨canon u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [K, canon, FinT.coeffList, typeEdgeVec, Finset.sum_insert] <;>
    omega

def TP (_ : Fin 6) : BalFixer.RootedTemplate 6 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 0)}, ![0, 0, 1, 0, 0],
    by decide +kernel, by decide +kernel, by decide +kernel⟩
def TM (_ : Fin 6) : BalFixer.RootedTemplate 6 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}, ![0, 1, 0, 0, 1],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def β : Fin 6 → Fin 6 → ℤ := ![![2, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

theorem vertex_three : ∀ r (d : Fin 6 → ℤ),
    (∀ j, d j ≠ 0 → ∃ l, Link K r j l) → (2 : ℤ) ∣ ∑ j, d j →
    (r ∈ B → ∑ j, σ r j * d j = 0) → (3 : ℤ) ∣ ∑ j, β r j * d j := by
  intro r d hsupp hpar hbal
  fin_cases r
  · have hb := hbal (by decide)
    simp [σ, β, sum_fin] at hb ⊢
    omega
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · simp [β, sum_fin]
  · simp [β, sum_fin]

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
  m := 4
  g := 5
  plus := TP
  minus := TM
  modulus := 1
  modulus_three := by norm_num
  plus_ok := by
    intro r hr _
    have hr' : r = 0 := by simpa [B] using hr
    subst r
    exact ⟨by decide +kernel, by unfold Link; decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  minus_ok := by
    intro r hr _
    have hr' : r = 0 := by simpa [B] using hr
    subst r
    exact ⟨by decide +kernel, by unfold Link; decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  three := fun q E hl ha _ he hb _ =>
    BalFixer.three_dvd_of_pot σ B β (by unfold Link K; decide +kernel)
      vertex_three hl ha he hb
  small := by norm_num

theorem exists_certificate : ∃ L, BalFixer.ComponentCertFlexTL
    (componentFamily case07 (0 : Fin 6)) c (0 : Fin 6) L := by
  have hK : componentFamily case07 (0 : Fin 6) = K := by
    simp [componentFamily, case07, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star07_0

#print axioms Star07_0.exists_certificate

namespace Star08_0

def K : Finset (Multiset (Fin 6)) := {{0, 0, 0}, {0, 0, 1}}

def c : Fin 6 → Fin 6 := ![0, 0, 2, 3, 2, 2]

def σ : Fin 6 → Fin 6 → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 6) := ∅

private theorem sum_fin (f : Fin 6 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, (d 0 - (d 1)) / 2), ({0, 0, 1}, d 1)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 1
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, d 0 / 2)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 5
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (u 0 1 / 2)) / 3), ({0, 0, 1}, u 0 1 / 2)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  have s50 := hs 5 0
  have s51 := hs 5 1
  have s52 := hs 5 2
  have s53 := hs 5 3
  have s54 := hs 5 4
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
    (componentFamily case08 (0 : Fin 6)) c (0 : Fin 6) L := by
  have hK : componentFamily case08 (0 : Fin 6) = K := by
    simp [componentFamily, case08, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star08_0

#print axioms Star08_0.exists_certificate

namespace Star08_3

def K : Finset (Multiset (Fin 6)) := {{3, 3, 3}}

def c : Fin 6 → Fin 6 := ![0, 0, 2, 3, 2, 2]

def σ : Fin 6 → Fin 6 → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 6) := ∅

private theorem sum_fin (f : Fin 6 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 3, 3}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 3, 3}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 3, 3}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 3, 3}, (d 3 - (0)) / 2)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 3, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 5
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 3, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({3, 3, 3}, (u 3 3 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 3 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z00 : u 0 0 = 0 := hf 0 0 (by unfold Link K; decide)
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  have s50 := hs 5 0
  have s51 := hs 5 1
  have s52 := hs 5 2
  have s53 := hs 5 3
  have s54 := hs 5 4
  refine ⟨canon u, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [K, canon, FinT.coeffList, typeEdgeVec, Finset.sum_insert] <;>
    omega

def data : StarCertificateData K c 3 where
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
    (componentFamily case08 (3 : Fin 6)) c (3 : Fin 6) L := by
  have hK : componentFamily case08 (3 : Fin 6) = K := by
    simp [componentFamily, case08, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star08_3

#print axioms Star08_3.exists_certificate

namespace Star09_0

def K : Finset (Multiset (Fin 6)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 3}}

def c : Fin 6 → Fin 6 := ![0, 0, 2, 0, 2, 2]

def σ : Fin 6 → Fin 6 → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 6) := ∅

private theorem sum_fin (f : Fin 6 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, Fin.succ, add_assoc]

theorem localSol : BalFixer.LocalSol K σ B := by
  intro r d hsupp hpar hbal
  fin_cases r
  · -- root 0
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, (d 0 - (d 1 + d 3)) / 2), ({0, 0, 1}, d 1), ({0, 0, 3}, d 3)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 1
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, d 0 / 2), ({0, 0, 3}, 0)], ?_⟩
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 3
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
    have z2 : d 2 = 0 := by
      by_contra h
      exact absurd (hsupp 2 h) (by unfold Link K; decide)
    have z3 : d 3 = 0 := by
      by_contra h
      exact absurd (hsupp 3 h) (by unfold Link K; decide)
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, d 0 / 2)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 4
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega
  · -- root 5
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
    have z4 : d 4 = 0 := by
      by_contra h
      exact absurd (hsupp 4 h) (by unfold Link K; decide)
    have z5 : d 5 = 0 := by
      by_contra h
      exact absurd (hsupp 5 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    fin_cases j <;>
      simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (u 0 1 / 2 + u 0 3 / 2)) / 3), ({0, 0, 1}, u 0 1 / 2), ({0, 0, 3}, u 0 3 / 2)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s21 := hs 2 1
  have s30 := hs 3 0
  have s31 := hs 3 1
  have s32 := hs 3 2
  have s40 := hs 4 0
  have s41 := hs 4 1
  have s42 := hs 4 2
  have s43 := hs 4 3
  have s50 := hs 5 0
  have s51 := hs 5 1
  have s52 := hs 5 2
  have s53 := hs 5 3
  have s54 := hs 5 4
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
    (componentFamily case09 (0 : Fin 6)) c (0 : Fin 6) L := by
  have hK : componentFamily case09 (0 : Fin 6) = K := by
    simp [componentFamily, case09, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star09_0

#print axioms Star09_0.exists_certificate

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

