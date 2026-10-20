/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Lattice
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Collapse
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Links
public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.Evaluation

@[expose] public section

/-!
# The family `KZ3 = F* ∖ {233}` and its `ℤ/3` lattice

`KZ3 = {000, 001, 002, 012, 123, 133, 333}` has the allowed pairs of F*, no `ThreeStepLinks`, but
`KappaLinks` and `FiveStepLinks`. Its lattice has index 3 in `Λ_ord`; the torsion value is

  `kz3Val E = (x13 + 2 x23 + d3) mod 3`

(additive on all edge sets, no division). The unique witness is `a123 = x23`, `a012 = x12 - x23`,
`a133 = (x13 - x23)/2`, `a333 = (d3 - a133)/3`, `a001 = (x01 - a012)/2`, `a002 = (x02 - a012)/2`,
`a000 = (d0 - a001 - a002)/3`.
-/

namespace TorsionQ.KZ3

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PaddedF12 PaddedFstar

noncomputable def KZ3 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}, {3, 3, 3}}

theorem KZ3_card : ∀ τ ∈ KZ3, Multiset.card τ = 3 := by decide

theorem not_threeStep_KZ3 : ¬ ThreeStepLinks KZ3 := by
  unfold ThreeStepLinks Link KZ3; decide

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000000 in
set_option maxHeartbeats 4000000 in
theorem fiveStep_KZ3 : FiveStepLinks KZ3 := by
  unfold FiveStepLinks Link KZ3; decide

theorem KZ3_subset_Fstar : KZ3 ⊆ Fstar := by decide

theorem active_Fstar_of_KZ3 {V : Type*} [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : ActiveEdges KZ3 p E) : ActiveEdges Fstar p E := by
  intro a b hab
  obtain ⟨k, hk⟩ := h a b hab
  exact ⟨k, KZ3_subset_Fstar hk⟩

noncomputable def kz3Coeff (a000 a001 a002 a012 a123 a133 a333 : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 0} then a000 else if τ = {0, 0, 1} then a001 else
  if τ = {0, 0, 2} then a002 else if τ = {0, 1, 2} then a012 else
  if τ = {1, 2, 3} then a123 else if τ = {1, 3, 3} then a133 else
  if τ = {3, 3, 3} then a333 else 0

theorem sum_KZ3 {β : Type*} [AddCommMonoid β] (f : Multiset (Fin 4) → β) :
    ∑ τ ∈ KZ3, f τ = f {0, 0, 0} + f {0, 0, 1} + f {0, 0, 2} + f {0, 1, 2} +
      f {1, 2, 3} + f {1, 3, 3} + f {3, 3, 3} := by
  unfold KZ3
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  abel

theorem kz3_edge_lattice_matrix (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ KZ3, c τ • typeEdgeVec τ) =
      fstarMatrix (3 * c {0, 0, 0} + c {0, 0, 1} + c {0, 0, 2}) (2 * c {0, 0, 1} + c {0, 1, 2})
        (2 * c {0, 0, 2} + c {0, 1, 2}) (c {0, 1, 2} + c {1, 2, 3})
        (c {1, 2, 3} + 2 * c {1, 3, 3}) (c {1, 2, 3})
        (c {1, 3, 3} + 3 * c {3, 3, 3}) := by
  rw [sum_KZ3]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fstarMatrix, typeEdgeVec] <;> ring

theorem zc0 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {0, 0, 0} = a := by
  unfold kz3Coeff; rw [if_pos rfl]
theorem zc1 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {0, 0, 1} = b := by
  unfold kz3Coeff; rw [if_neg (by decide), if_pos rfl]
theorem zc2 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {0, 0, 2} = c := by
  unfold kz3Coeff; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem zc3 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {0, 1, 2} = d := by
  unfold kz3Coeff; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem zc4 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {1, 2, 3} = e := by
  unfold kz3Coeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem zc5 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {1, 3, 3} = f := by
  unfold kz3Coeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]
theorem zc6 (a b c d e f g : ℤ) : kz3Coeff a b c d e f g {3, 3, 3} = g := by
  unfold kz3Coeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem kz3_scalar_witness (d0 x01 x02 x12 x13 x23 d3 : ℤ)
    (hn : 0 ≤ d0 ∧ 0 ≤ x01 ∧ 0 ≤ x02 ∧ 0 ≤ x12 ∧ 0 ≤ x13 ∧ 0 ≤ x23 ∧ 0 ≤ d3)
    (hp1 : (2 : ℤ) ∣ x01 + x12 + x13) (hp2 : (2 : ℤ) ∣ x02 + x12 + x23)
    (hp3 : (2 : ℤ) ∣ x13 + x23)
    (hval : (3 : ℤ) ∣ x13 + 2 * x23 + d3)
    (h3 : (3 : ℤ) ∣ d0 + x01 + x02 + x12 + x13 + x23 + d3) :
    ∃ a000 a001 a002 a012 a123 a133 a333 : ℤ,
      d0 = 3 * a000 + a001 + a002 ∧ x01 = 2 * a001 + a012 ∧ x02 = 2 * a002 + a012 ∧
      x12 = a012 + a123 ∧ x13 = a123 + 2 * a133 ∧ x23 = a123 ∧
      d3 = a133 + 3 * a333 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a000 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a001 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a002 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a012 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a123 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a133 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a333 := by
  obtain ⟨hd0, h01, h02, h12, h13, h23, hd3⟩ := hn
  obtain ⟨k1, hk1⟩ := hp1
  obtain ⟨k2, hk2⟩ := hp2
  obtain ⟨k3, hk3⟩ := hp3
  obtain ⟨v, hv⟩ := hval
  obtain ⟨t, ht⟩ := h3
  obtain ⟨u5, hu5⟩ : ∃ u, x13 - x23 = 2 * u := ⟨k3 - x23, by omega⟩
  obtain ⟨u6, hu6⟩ : ∃ u, d3 - u5 = 3 * u := ⟨v - x23 - u5, by omega⟩
  obtain ⟨u1, hu1⟩ : ∃ u, x01 - (x12 - x23) = 2 * u := ⟨k1 - x12 - u5 - x23 + x23, by omega⟩
  obtain ⟨u2, hu2⟩ : ∃ u, x02 - (x12 - x23) = 2 * u := ⟨k2 - x12, by omega⟩
  obtain ⟨u0, hu0⟩ : ∃ u, d0 - u1 - u2 = 3 * u :=
    ⟨t - u1 - u2 - (x12 - x23) - x23 - u5 - u6, by omega⟩
  refine ⟨u0, u1, u2, x12 - x23, x23, u5, u6, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear hk1 hk2 hk3 hv ht
  all_goals omega

variable {V : Type*} [DecidableEq V]

def kz3Num (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  unorderedCount p E 1 3 + 2 * unorderedCount p E 2 3 + unorderedCount p E 3 3

def kz3Val (p : V → Fin 4) (E : Finset (Sym2 V)) : ℕ := (kz3Num p E % 3).toNat

def KZ3Good (p : V → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ ActiveEdges KZ3 p E ∧
    (∀ v, Even (incidentLoad E v)) ∧ 3 ∣ E.card

theorem kz3Num_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    kz3Num p (A ∪ B) = kz3Num p A + kz3Num p B := by
  simp only [kz3Num, unorderedCount_union p h]
  ring

theorem KZ3Good_empty (p : V → Fin 4) : KZ3Good p ∅ := by
  simp [KZ3Good, ActiveEdges, OnePart.incidentLoad_empty]

theorem KZ3Good_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : KZ3Good p A) (hB : KZ3Good p B) : KZ3Good p (A ∪ B) := by
  refine ⟨?_, ?_, OnePart.even_incidentLoad_union h hA.2.2.1 hB.2.2.1, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hA.1 e he
    · exact hB.1 e he
  · intro a b hab
    rcases mem_union.mp hab with hab | hab
    · exact hA.2.1 a b hab
    · exact hB.2.1 a b hab
  · rw [card_union_of_disjoint h]
    exact dvd_add hA.2.2.2 hB.2.2.2

theorem kz3Val_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    kz3Val p (A ∪ B) = (kz3Val p A + kz3Val p B) % 3 := by
  unfold kz3Val
  rw [kz3Num_union p h]
  omega

theorem kz3Val_eq_zero_iff (p : V → Fin 4) (E : Finset (Sym2 V)) :
    kz3Val p E = 0 ↔ (3 : ℤ) ∣ kz3Num p E := by
  unfold kz3Val; omega

/-- The `ℤ/3` evaluation of KZ3. -/
def kz3Eval (p : V → Fin 4) : QEvaluation 3 (KZ3Good p) where
  empty_good := KZ3Good_empty p
  union_good := KZ3Good_union p
  value := kz3Val p
  value_lt := fun E _ => by unfold kz3Val; omega
  empty_value := by simp [kz3Val, kz3Num, unorderedCount_empty]
  union_value := fun h _ _ => kz3Val_union p h

/-- **The `ℤ/3` lattice of KZ3.** -/
theorem isIntDiv_KZ3_iff_good_val [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p KZ3 E ↔ KZ3Good p E ∧ kz3Val p E = 0 := by
  rw [isIntDiv_iff_five fiveStep_KZ3 KZ3_card hloop]
  constructor
  · rintro ⟨hact, heven, c, hc⟩
    have hact' := active_Fstar_of_KZ3 p E hact
    have htot := fstar_total_count p E hact'
    rw [edgeVec_fstarMatrix p E hact', kz3_edge_lattice_matrix] at hc
    set A0 := c {0, 0, 0} with hA0
    set A1 := c {0, 0, 1} with hA1
    set A2 := c {0, 0, 2} with hA2
    set A3 := c {0, 1, 2} with hA3
    set A4 := c {1, 2, 3} with hA4
    set A5 := c {1, 3, 3} with hA5
    set A6 := c {3, 3, 3} with hA6
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e02 := congrFun (congrFun hc 0) 2
    have e12 := congrFun (congrFun hc 1) 2
    have e13 := congrFun (congrFun hc 1) 3
    have e23 := congrFun (congrFun hc 2) 3
    have e33 := congrFun (congrFun hc 3) 3
    simp only [fstarMatrix] at e00 e01 e02 e12 e13 e23 e33
    norm_num at e00 e01 e02 e12 e13 e23 e33
    have h3 : (3 : ℤ) ∣ (E.card : ℤ) := ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6, by omega⟩
    refine ⟨⟨hloop, hact, heven, by exact_mod_cast h3⟩, ?_⟩
    rw [kz3Val_eq_zero_iff]
    exact ⟨A4 + A5 + A6, by unfold kz3Num; omega⟩
  · rintro ⟨⟨-, hact, heven, h3⟩, hval⟩
    refine ⟨hact, heven, ?_⟩
    have hact' := active_Fstar_of_KZ3 p E hact
    obtain ⟨-, hp1, hp2, hp3⟩ := fstar_class_parities p E hact' hloop heven
    have htot := fstar_total_count p E hact'
    have h3' : (3 : ℤ) ∣ unorderedCount p E 0 0 + unorderedCount p E 0 1 +
        unorderedCount p E 0 2 + unorderedCount p E 1 2 + unorderedCount p E 1 3 +
        unorderedCount p E 2 3 + unorderedCount p E 3 3 := by
      rw [← htot]; exact_mod_cast h3
    rw [kz3Val_eq_zero_iff] at hval
    obtain ⟨a000, a001, a002, a012, a123, a133, a333, q0, q1, q2, q3, q4, q5, q6,
      -, -, -, -, -, -, -⟩ :=
      kz3_scalar_witness _ _ _ _ _ _ _ ⟨unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _⟩ hp1 hp2 hp3 hval h3'
    refine ⟨kz3Coeff a000 a001 a002 a012 a123 a133 a333, ?_⟩
    rw [edgeVec_fstarMatrix p E hact', kz3_edge_lattice_matrix]
    rw [zc0, zc1, zc2, zc3, zc4, zc5, zc6, q0, q1, q2, q3, q4, q5, q6]

theorem kz3_bounded_coefficients (K : ℕ) {W : Type*} [DecidableEq W]
    (p : W → Fin 4) (P : Finset (Sym2 W)) (hK : P.card ≤ K) (hdiv : IsIntDiv p KZ3 P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ KZ3, c τ • typeEdgeVec τ ∧
      negativeMass KZ3 c ≤ 7 * K := by
  have hact := active_of_isIntDiv KZ3_card hdiv
  have hact' := active_Fstar_of_KZ3 p P hact
  obtain ⟨c, hc⟩ := hdiv.1
  have htot := fstar_total_count p P hact'
  rw [edgeVec_fstarMatrix p P hact', kz3_edge_lattice_matrix] at hc
  set A0 := c {0, 0, 0} with hA0
  set A1 := c {0, 0, 1} with hA1
  set A2 := c {0, 0, 2} with hA2
  set A3 := c {0, 1, 2} with hA3
  set A4 := c {1, 2, 3} with hA4
  set A5 := c {1, 3, 3} with hA5
  set A6 := c {3, 3, 3} with hA6
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e02 := congrFun (congrFun hc 0) 2
  have e12 := congrFun (congrFun hc 1) 2
  have e13 := congrFun (congrFun hc 1) 3
  have e23 := congrFun (congrFun hc 2) 3
  have e33 := congrFun (congrFun hc 3) 3
  simp only [fstarMatrix] at e00 e01 e02 e12 e13 e23 e33
  norm_num at e00 e01 e02 e12 e13 e23 e33
  obtain ⟨a000, a001, a002, a012, a123, a133, a333, q0, q1, q2, q3, q4, q5, q6,
    b0, b1, b2, b3, b4, b5, b6⟩ :=
    kz3_scalar_witness (unorderedCount p P 0 0) (unorderedCount p P 0 1)
      (unorderedCount p P 0 2) (unorderedCount p P 1 2) (unorderedCount p P 1 3)
      (unorderedCount p P 2 3) (unorderedCount p P 3 3)
      ⟨unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _⟩
      ⟨A1 + A3 + A4 + A5, by omega⟩ ⟨A2 + A3 + A4, by omega⟩
      ⟨A4 + A5, by omega⟩ ⟨A4 + A5 + A6, by omega⟩
      ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6, by omega⟩
  refine ⟨kz3Coeff a000 a001 a002 a012 a123 a133 a333, ?_, ?_⟩
  · rw [edgeVec_fstarMatrix p P hact', kz3_edge_lattice_matrix]
    rw [zc0, zc1, zc2, zc3, zc4, zc5, zc6, q0, q1, q2, q3, q4, q5, q6]
  · unfold negativeMass
    rw [sum_KZ3, zc0, zc1, zc2, zc3, zc4, zc5, zc6]
    have hKZ : (P.card : ℤ) ≤ K := by exact_mod_cast hK
    rw [← htot] at b0 b1 b2 b3 b4 b5 b6
    clear * - b0 b1 b2 b3 b4 b5 b6 hKZ
    omega

end TorsionQ.KZ3

#print axioms TorsionQ.KZ3.isIntDiv_KZ3_iff_good_val
#print axioms TorsionQ.KZ3.kz3_bounded_coefficients
