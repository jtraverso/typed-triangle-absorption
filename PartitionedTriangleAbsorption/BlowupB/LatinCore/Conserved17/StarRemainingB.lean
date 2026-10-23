/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarCertificate
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.All

@[expose] public section

/-! Checked non-Latin component witnesses, compilation batch B. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17
open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General VertexSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Star10_0

def K : Finset (Multiset (Fin 7)) := {{0, 0, 0}}

def c : Fin 7 → Fin 7 := ![0, 1, 1, 3, 1, 3, 3]

def σ : Fin 7 → Fin 7 → ℤ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 7) := ∅

private theorem sum_fin (f : Fin 7 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, (d 0 - (0)) / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
  · -- root 6
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 7 → Fin 7 → ℤ) : Multiset (Fin 7) → ℤ :=
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
  have z06 : u 0 6 = 0 := hf 0 6 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z16 : u 1 6 = 0 := hf 1 6 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z26 : u 2 6 = 0 := hf 2 6 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z36 : u 3 6 = 0 := hf 3 6 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z46 : u 4 6 = 0 := hf 4 6 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have z56 : u 5 6 = 0 := hf 5 6 (by unfold Link K; decide)
  have z66 : u 6 6 = 0 := hf 6 6 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  have p6 := hp 6
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5 p6
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
  have s60 := hs 6 0
  have s61 := hs 6 1
  have s62 := hs 6 2
  have s63 := hs 6 3
  have s64 := hs 6 4
  have s65 := hs 6 5
  refine ⟨canon u, ?_⟩
  intro i j
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 0 0 - (0)) / 3 * 3 = u 0 0 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 0 0 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 p6 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 0 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 7, c b = 0 → ∃ l, Link K b 0 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨0, 0, 0, h i hi, h 0 (by decide +kernel),
      h 0 (by decide +kernel), h j hj⟩
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
    (componentFamily case10 (0 : Fin 7)) c (0 : Fin 7) L := by
  have hK : componentFamily case10 (0 : Fin 7) = K := by
    simp [componentFamily, case10, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star10_0

#print axioms Star10_0.exists_certificate

namespace Star10_3

def K : Finset (Multiset (Fin 7)) := {{3, 6, 6}, {5, 6, 6}}

def c : Fin 7 → Fin 7 := ![0, 1, 1, 3, 1, 3, 3]

def σ : Fin 7 → Fin 7 → ℤ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, -1, 1]]
def B : Finset (Fin 7) := {6}

private theorem sum_fin (f : Fin 7 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 6, 6}, 0), ({5, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 6, 6}, 0), ({5, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 6, 6}, 0), ({5, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({3, 6, 6}, d 6 / 2), ({5, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({3, 6, 6}, 0), ({5, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({3, 6, 6}, 0), ({5, 6, 6}, d 6 / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
  · -- root 6
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
    have hb := hbal (by decide : (6 : Fin 7) ∈ B)
    simp [σ, sum_fin] at hb
    refine ⟨FinT.coeffList [({3, 6, 6}, d 3), ({5, 6, 6}, d 5)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 7 → Fin 7 → ℤ) : Multiset (Fin 7) → ℤ :=
  FinT.coeffList [({3, 6, 6}, u 6 3 / 2), ({5, 6, 6}, u 6 5 / 2)]

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
  have z06 : u 0 6 = 0 := hf 0 6 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z16 : u 1 6 = 0 := hf 1 6 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z26 : u 2 6 = 0 := hf 2 6 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z46 : u 4 6 = 0 := hf 4 6 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  have p6 := hp 6
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5 p6
  unfold FinT.totalU at h3
  simp only [sum_fin, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have hb := hbal 6 (by decide)
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
  have s60 := hs 6 0
  have s61 := hs 6 1
  have s62 := hs 6 2
  have s63 := hs 6 3
  have s64 := hs 6 4
  have s65 := hs 6 5
  refine ⟨canon u, ?_⟩
  intro i j
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def TP (_ : Fin 7) : BalFixer.RootedTemplate 7 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 0)}, ![6, 6, 3, 6, 6],
    by decide +kernel, by decide +kernel, by decide +kernel⟩
def TM (_ : Fin 7) : BalFixer.RootedTemplate 7 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}, ![6, 3, 6, 6, 3],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def β : Fin 7 → Fin 7 → ℤ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 2]]

theorem vertex_three : ∀ r (d : Fin 7 → ℤ),
    (∀ j, d j ≠ 0 → ∃ l, Link K r j l) → (2 : ℤ) ∣ ∑ j, d j →
    (r ∈ B → ∑ j, σ r j * d j = 0) → (3 : ℤ) ∣ ∑ j, β r j * d j := by
  intro r d hsupp hpar hbal
  fin_cases r
  · simp [β, sum_fin]
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
  walk := by
    have h : ∀ b : Fin 7, c b = 3 → ∃ l, Link K b 6 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨6, 6, 6, h i hi, h 6 (by decide +kernel),
      h 6 (by decide +kernel), h j hj⟩
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
    have hr' : r = 6 := by simpa [B] using hr
    subst r
    exact ⟨by decide +kernel, by unfold Link; decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  minus_ok := by
    intro r hr _
    have hr' : r = 6 := by simpa [B] using hr
    subst r
    exact ⟨by decide +kernel, by unfold Link; decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
  three := fun q E hl ha _ he hb _ =>
    BalFixer.three_dvd_of_pot σ B β (by unfold Link K; decide +kernel)
      vertex_three hl ha he hb
  small := by norm_num

theorem exists_certificate : ∃ L, BalFixer.ComponentCertFlexTL
    (componentFamily case10 (3 : Fin 7)) c (3 : Fin 7) L := by
  have hK : componentFamily case10 (3 : Fin 7) = K := by
    simp [componentFamily, case10, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star10_3

#print axioms Star10_3.exists_certificate

namespace Star11_0

def K : Finset (Multiset (Fin 7)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 3}}

def c : Fin 7 → Fin 7 := ![0, 0, 2, 0, 2, 2, 6]

def σ : Fin 7 → Fin 7 → ℤ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 7) := ∅

private theorem sum_fin (f : Fin 7 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, (d 0 - (d 1 + d 3)) / 2), ({0, 0, 1}, d 1), ({0, 0, 3}, d 3)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, d 0 / 2), ({0, 0, 3}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, d 0 / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
  · -- root 6
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 0}, 0), ({0, 0, 1}, 0), ({0, 0, 3}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 7 → Fin 7 → ℤ) : Multiset (Fin 7) → ℤ :=
  FinT.coeffList [({0, 0, 0}, (u 0 0 - (u 0 1 / 2 + u 0 3 / 2)) / 3), ({0, 0, 1}, u 0 1 / 2), ({0, 0, 3}, u 0 3 / 2)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 0 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z06 : u 0 6 = 0 := hf 0 6 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z16 : u 1 6 = 0 := hf 1 6 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z26 : u 2 6 = 0 := hf 2 6 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z36 : u 3 6 = 0 := hf 3 6 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z46 : u 4 6 = 0 := hf 4 6 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have z56 : u 5 6 = 0 := hf 5 6 (by unfold Link K; decide)
  have z66 : u 6 6 = 0 := hf 6 6 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  have p6 := hp 6
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5 p6
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
  have s60 := hs 6 0
  have s61 := hs 6 1
  have s62 := hs 6 2
  have s63 := hs 6 3
  have s64 := hs 6 4
  have s65 := hs 6 5
  refine ⟨canon u, ?_⟩
  intro i j
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 0 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 7, c b = 0 → ∃ l, Link K b 0 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨0, 0, 0, h i hi, h 0 (by decide +kernel),
      h 0 (by decide +kernel), h j hj⟩
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
    (componentFamily case11 (0 : Fin 7)) c (0 : Fin 7) L := by
  have hK : componentFamily case11 (0 : Fin 7) = K := by
    simp [componentFamily, case11, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star11_0

#print axioms Star11_0.exists_certificate

namespace Star11_6

def K : Finset (Multiset (Fin 7)) := {{6, 6, 6}}

def c : Fin 7 → Fin 7 := ![0, 0, 2, 0, 2, 2, 6]

def σ : Fin 7 → Fin 7 → ℤ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]]
def B : Finset (Fin 7) := ∅

private theorem sum_fin (f : Fin 7 → ℤ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({6, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({6, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({6, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({6, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({6, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    have z6 : d 6 = 0 := by
      by_contra h
      exact absurd (hsupp 6 h) (by unfold Link K; decide)
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({6, 6, 6}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
  · -- root 6
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
    refine ⟨FinT.coeffList [({6, 6, 6}, (d 6 - (0)) / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 7 → Fin 7 → ℤ) : Multiset (Fin 7) → ℤ :=
  FinT.coeffList [({6, 6, 6}, (u 6 6 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 6 u → ∃ w, FinT.LatEq K u w := by
  intro u hu _
  obtain ⟨⟨hs, _, hf, hp, h3⟩, hbal, -⟩ := hu
  have z00 : u 0 0 = 0 := hf 0 0 (by unfold Link K; decide)
  have z01 : u 0 1 = 0 := hf 0 1 (by unfold Link K; decide)
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link K; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link K; decide)
  have z04 : u 0 4 = 0 := hf 0 4 (by unfold Link K; decide)
  have z05 : u 0 5 = 0 := hf 0 5 (by unfold Link K; decide)
  have z06 : u 0 6 = 0 := hf 0 6 (by unfold Link K; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link K; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link K; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link K; decide)
  have z14 : u 1 4 = 0 := hf 1 4 (by unfold Link K; decide)
  have z15 : u 1 5 = 0 := hf 1 5 (by unfold Link K; decide)
  have z16 : u 1 6 = 0 := hf 1 6 (by unfold Link K; decide)
  have z22 : u 2 2 = 0 := hf 2 2 (by unfold Link K; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link K; decide)
  have z24 : u 2 4 = 0 := hf 2 4 (by unfold Link K; decide)
  have z25 : u 2 5 = 0 := hf 2 5 (by unfold Link K; decide)
  have z26 : u 2 6 = 0 := hf 2 6 (by unfold Link K; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link K; decide)
  have z34 : u 3 4 = 0 := hf 3 4 (by unfold Link K; decide)
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
  have z36 : u 3 6 = 0 := hf 3 6 (by unfold Link K; decide)
  have z44 : u 4 4 = 0 := hf 4 4 (by unfold Link K; decide)
  have z45 : u 4 5 = 0 := hf 4 5 (by unfold Link K; decide)
  have z46 : u 4 6 = 0 := hf 4 6 (by unfold Link K; decide)
  have z55 : u 5 5 = 0 := hf 5 5 (by unfold Link K; decide)
  have z56 : u 5 6 = 0 := hf 5 6 (by unfold Link K; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  have p4 := hp 4
  have p5 := hp 5
  have p6 := hp 6
  simp only [sum_fin, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3 p4 p5 p6
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
  have s60 := hs 6 0
  have s61 := hs 6 1
  have s62 := hs 6 2
  have s63 := hs 6 3
  have s64 := hs 6 4
  have s65 := hs 6 5
  refine ⟨canon u, ?_⟩
  intro i j
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 6 6 - (0)) / 3 * 3 = u 6 6 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 6 6 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 p6 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 6 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 7, c b = 6 → ∃ l, Link K b 6 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨6, 6, 6, h i hi, h 6 (by decide +kernel),
      h 6 (by decide +kernel), h j hj⟩
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
    (componentFamily case11 (6 : Fin 7)) c (6 : Fin 7) L := by
  have hK : componentFamily case11 (6 : Fin 7) = K := by
    simp [componentFamily, case11, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star11_6

#print axioms Star11_6.exists_certificate

namespace Star12_0

def K : Finset (Multiset (Fin 6)) := {{0, 0, 0}}

def c : Fin 6 → Fin 6 := ![0, 1, 1, 1, 1, 5]

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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

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
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 0 0 - (0)) / 3 * 3 = u 0 0 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 0 0 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 0 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 6, c b = 0 → ∃ l, Link K b 0 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨0, 0, 0, h i hi, h 0 (by decide +kernel),
      h 0 (by decide +kernel), h j hj⟩
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
    (componentFamily case12 (0 : Fin 6)) c (0 : Fin 6) L := by
  have hK : componentFamily case12 (0 : Fin 6) = K := by
    simp [componentFamily, case12, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star12_0

#print axioms Star12_0.exists_certificate

namespace Star12_5

def K : Finset (Multiset (Fin 6)) := {{5, 5, 5}}

def c : Fin 6 → Fin 6 := ![0, 1, 1, 1, 1, 5]

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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({5, 5, 5}, (d 5 - (0)) / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({5, 5, 5}, (u 5 5 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 5 u → ∃ w, FinT.LatEq K u w := by
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
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
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
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 5 5 - (0)) / 3 * 3 = u 5 5 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 5 5 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 5 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 6, c b = 5 → ∃ l, Link K b 5 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨5, 5, 5, h i hi, h 5 (by decide +kernel),
      h 5 (by decide +kernel), h j hj⟩
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
    (componentFamily case12 (5 : Fin 6)) c (5 : Fin 6) L := by
  have hK : componentFamily case12 (5 : Fin 6) = K := by
    simp [componentFamily, case12, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star12_5

#print axioms Star12_5.exists_certificate

namespace Star13_0

def K : Finset (Multiset (Fin 6)) := {{0, 0, 0}}

def c : Fin 6 → Fin 6 := ![0, 1, 2, 1, 1, 5]

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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

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
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 0 0 - (0)) / 3 * 3 = u 0 0 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 0 0 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 0 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 6, c b = 0 → ∃ l, Link K b 0 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨0, 0, 0, h i hi, h 0 (by decide +kernel),
      h 0 (by decide +kernel), h j hj⟩
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
    (componentFamily case13 (0 : Fin 6)) c (0 : Fin 6) L := by
  have hK : componentFamily case13 (0 : Fin 6) = K := by
    simp [componentFamily, case13, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star13_0

#print axioms Star13_0.exists_certificate

namespace Star13_2

def K : Finset (Multiset (Fin 6)) := {{2, 2, 2}}

def c : Fin 6 → Fin 6 := ![0, 1, 2, 1, 1, 5]

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
    refine ⟨FinT.coeffList [({2, 2, 2}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({2, 2, 2}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
  · -- root 2
    have z0 : d 0 = 0 := by
      by_contra h
      exact absurd (hsupp 0 h) (by unfold Link K; decide)
    have z1 : d 1 = 0 := by
      by_contra h
      exact absurd (hsupp 1 h) (by unfold Link K; decide)
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
    refine ⟨FinT.coeffList [({2, 2, 2}, (d 2 - (0)) / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({2, 2, 2}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({2, 2, 2}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({2, 2, 2}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({2, 2, 2}, (u 2 2 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 2 u → ∃ w, FinT.LatEq K u w := by
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
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 2 2 - (0)) / 3 * 3 = u 2 2 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 2 2 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 2 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 6, c b = 2 → ∃ l, Link K b 2 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨2, 2, 2, h i hi, h 2 (by decide +kernel),
      h 2 (by decide +kernel), h j hj⟩
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
    (componentFamily case13 (2 : Fin 6)) c (2 : Fin 6) L := by
  have hK : componentFamily case13 (2 : Fin 6) = K := by
    simp [componentFamily, case13, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star13_2

#print axioms Star13_2.exists_certificate

namespace Star13_5

def K : Finset (Multiset (Fin 6)) := {{5, 5, 5}}

def c : Fin 6 → Fin 6 := ![0, 1, 2, 1, 1, 5]

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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    refine ⟨FinT.coeffList [({5, 5, 5}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega
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
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({5, 5, 5}, (d 5 - (0)) / 2)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 6 → Fin 6 → ℤ) : Multiset (Fin 6) → ℤ :=
  FinT.coeffList [({5, 5, 5}, (u 5 5 - (0)) / 3)]

theorem scalar : ∀ u, BalFixer.BalScalarHyp K σ B (fun _ _ => 0) u →
    FinT.CountsInside c 5 u → ∃ w, FinT.LatEq K u w := by
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
  have z35 : u 3 5 = 0 := hf 3 5 (by unfold Link K; decide)
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
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  have hqv0 : (u 5 5 - (0)) / 3 * 3 = u 5 5 - (0) := Int.ediv_mul_cancel (by omega)
  generalize (u 5 5 - (0)) / 3 = qv0 at *
  clear p0 p1 p2 p3 p4 p5 h3
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def data : StarCertificateData K c 5 where
  comp := by unfold CompT.CompLabel Link K; decide +kernel
  card := by decide +kernel
  walk := by
    have h : ∀ b : Fin 6, c b = 5 → ∃ l, Link K b 5 l := by
      unfold Link K
      decide +kernel
    intro i j hi hj
    exact ⟨5, 5, 5, h i hi, h 5 (by decide +kernel),
      h 5 (by decide +kernel), h j hj⟩
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
    (componentFamily case13 (5 : Fin 6)) c (5 : Fin 6) L := by
  have hK : componentFamily case13 (5 : Fin 6) = K := by
    simp [componentFamily, case13, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star13_5

#print axioms Star13_5.exists_certificate

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

