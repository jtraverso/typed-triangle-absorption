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

namespace Star01_0

def K : Finset (Multiset (Fin 5)) := {{0, 0, 1}}

def c : Fin 5 → Fin 5 := ![0, 0, 2, 2, 2]

def σ : Fin 5 → Fin 5 → ℤ := ![![1, -1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
def B : Finset (Fin 5) := {0}

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
    have hb := hbal (by decide : (0 : Fin 5) ∈ B)
    simp [σ, sum_fin] at hb
    refine ⟨FinT.coeffList [({0, 0, 1}, d 1)], ?_⟩
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
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, d 0 / 2)], ?_⟩
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
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0)], ?_⟩
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
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0)], ?_⟩
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
    simp only [sum_fin] at hpar
    refine ⟨FinT.coeffList [({0, 0, 1}, 0)], ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_filter, K]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp (config := {decide := true}) only [FinT.coeffList, Pi.smul_apply, smul_eq_mul, ite_true, ite_false]
    fin_cases j <;>
      simp (config := {decide := true}) only [typeDegVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega

def canon (u : Fin 5 → Fin 5 → ℤ) : Multiset (Fin 5) → ℤ :=
  FinT.coeffList [({0, 0, 1}, u 0 1 / 2)]

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
  refine ⟨canon u, ?_⟩
  intro i j
  rw [K]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp (config := {decide := true}) only [canon, FinT.coeffList, ite_true, ite_false]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;>
    omega

def TP (_ : Fin 5) : BalFixer.RootedTemplate 5 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 0)}, ![0, 0, 1, 0, 0],
    by decide +kernel, by decide +kernel, by decide +kernel⟩
def TM (_ : Fin 5) : BalFixer.RootedTemplate 5 4 5 :=
  ⟨{s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}, ![0, 1, 0, 0, 1],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def β : Fin 5 → Fin 5 → ℤ := ![![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]

theorem vertex_three : ∀ r (d : Fin 5 → ℤ),
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
    (componentFamily case01 (0 : Fin 5)) c (0 : Fin 5) L := by
  have hK : componentFamily case01 (0 : Fin 5) = K := by
    simp [componentFamily, case01, K] <;> decide +kernel
  rw [hK]
  exact data.exists_certificate

end Star01_0

#print axioms Star01_0.exists_certificate

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

