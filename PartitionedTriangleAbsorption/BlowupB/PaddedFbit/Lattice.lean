/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Lattice
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalParity

@[expose] public section

/-!
# The family Fbit (= G9) and its one-bit lattice

`Fbit = {000, 001, 002, 011, 022, 113, 133, 223, 233}`. Allowed pairs: 00, 01, 02, 11, 13, 22, 23,
33 (forbidden 03 and 12). It has `ThreeStepLinks` and common neighbour classes. The local census
found `Λ_ord / L_Fbit = ℤ/2`, and the same for the four other bit-only families of the census
(`Fbit ∪ {333}`, `Fbit ∪ {111}`, `Fbit ∪ {111, 222}`, `Fbit ∪ {111, 222, 333}`), all with the same
allowed pairs. Every type has even cross counts, so the bit is simply

  `fbitBit E = x01 mod 2`

(the class parities force `x01 ≡ x02 ≡ x13 ≡ x23 (mod 2)`); no division by two is needed. The
6-cycle `0,0,1,3,2,0` has bit 1.

Lean content:
* `isIntDiv_Fbit_iff_good_bit`: on loopless sets, `IsIntDiv p Fbit E ↔ FbitGood p E ∧ bit = 0`;
* `fbitParity`: the parity evaluation;
* `fbit_bounded_coefficients`: an integral witness with negative mass `≤ 8 K` (free parameter of
  the one-dimensional kernel set to `a001 = 0`).
-/

namespace PaddedFbit

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PaddedF12

/-- The family Fbit (G9 of the census). -/
noncomputable def Fbit : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}, {2, 2, 3},
    {2, 3, 3}}

theorem Fbit_card : ∀ τ ∈ Fbit, Multiset.card τ = 3 := by decide

theorem Fbit_three_step : ThreeStepLinks Fbit := by
  unfold ThreeStepLinks Link Fbit
  decide

/-- The explicit coefficients, indexed by type. -/
noncomputable def fbitCoeff (a000 a001 a002 a011 a022 a113 a133 a223 a233 : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 0} then a000 else if τ = {0, 0, 1} then a001 else
  if τ = {0, 0, 2} then a002 else if τ = {0, 1, 1} then a011 else
  if τ = {0, 2, 2} then a022 else if τ = {1, 1, 3} then a113 else
  if τ = {1, 3, 3} then a133 else if τ = {2, 2, 3} then a223 else
  if τ = {2, 3, 3} then a233 else 0

/-- The ordered edge matrix of Fbit-supported counts. -/
def fbitMatrix (d0 x01 x02 d1 x13 d2 x23 d3 : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![2 * d0, x01, x02, 0], ![x01, 2 * d1, 0, x13],
    ![x02, 0, 2 * d2, x23], ![0, x13, x23, 2 * d3]]

theorem sum_Fbit {β : Type*} [AddCommMonoid β] (f : Multiset (Fin 4) → β) :
    ∑ τ ∈ Fbit, f τ = f {0, 0, 0} + f {0, 0, 1} + f {0, 0, 2} + f {0, 1, 1} +
      f {0, 2, 2} + f {1, 1, 3} + f {1, 3, 3} + f {2, 2, 3} + f {2, 3, 3} := by
  unfold Fbit
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  abel

theorem fbit_edge_lattice_matrix (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ Fbit, c τ • typeEdgeVec τ) =
      fbitMatrix (3 * c {0, 0, 0} + c {0, 0, 1} + c {0, 0, 2})
        (2 * c {0, 0, 1} + 2 * c {0, 1, 1}) (2 * c {0, 0, 2} + 2 * c {0, 2, 2})
        (c {0, 1, 1} + c {1, 1, 3}) (2 * c {1, 1, 3} + 2 * c {1, 3, 3})
        (c {0, 2, 2} + c {2, 2, 3}) (2 * c {2, 2, 3} + 2 * c {2, 3, 3})
        (c {1, 3, 3} + c {2, 3, 3}) := by
  rw [sum_Fbit]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fbitMatrix, typeEdgeVec] <;> ring

section Eval
variable (a b c d e f g h k : ℤ)
theorem bc0 : fbitCoeff a b c d e f g h k {0, 0, 0} = a := by
  unfold fbitCoeff; rw [if_pos rfl]
theorem bc1 : fbitCoeff a b c d e f g h k {0, 0, 1} = b := by
  unfold fbitCoeff; rw [if_neg (by decide), if_pos rfl]
theorem bc2 : fbitCoeff a b c d e f g h k {0, 0, 2} = c := by
  unfold fbitCoeff; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem bc3 : fbitCoeff a b c d e f g h k {0, 1, 1} = d := by
  unfold fbitCoeff; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem bc4 : fbitCoeff a b c d e f g h k {0, 2, 2} = e := by
  unfold fbitCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem bc5 : fbitCoeff a b c d e f g h k {1, 1, 3} = f := by
  unfold fbitCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]
theorem bc6 : fbitCoeff a b c d e f g h k {1, 3, 3} = g := by
  unfold fbitCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem bc7 : fbitCoeff a b c d e f g h k {2, 2, 3} = h := by
  unfold fbitCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem bc8 : fbitCoeff a b c d e f g h k {2, 3, 3} = k := by
  unfold fbitCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
end Eval

variable {V : Type*} [DecidableEq V]

theorem fbit_inactive_counts (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : ActiveEdges Fbit p E) :
    unorderedCount p E 0 3 = 0 ∧ unorderedCount p E 1 2 = 0 := by
  have hf : ∀ a b k : Fin 4, Link Fbit a b k → s(a, b) ≠ s(0, 3) ∧ s(a, b) ≠ s(1, 2) := by
    unfold Link Fbit; decide
  refine ⟨?_, ?_⟩ <;> apply unorderedCount_zero_of_forbidden <;> intro e he <;>
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨k, hk⟩ := h a b he
      have := hf (p a) (p b) k hk
      first | exact this.1 | exact this.2

theorem edgeVec_fbitMatrix (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges Fbit p E) :
    edgeVec p E = fbitMatrix (unorderedCount p E 0 0) (unorderedCount p E 0 1)
      (unorderedCount p E 0 2) (unorderedCount p E 1 1) (unorderedCount p E 1 3)
      (unorderedCount p E 2 2) (unorderedCount p E 2 3) (unorderedCount p E 3 3) := by
  obtain ⟨h03, h12⟩ := fbit_inactive_counts p E h
  funext i j
  rw [edgeVec_unorderedCount]
  fin_cases i <;> fin_cases j <;>
    simp [fbitMatrix, unorderedCount_swap p E 1 0, unorderedCount_swap p E 2 0,
      unorderedCount_swap p E 2 1, unorderedCount_swap p E 3 0,
      unorderedCount_swap p E 3 1, unorderedCount_swap p E 3 2, h03, h12]

theorem fbit_total_count (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges Fbit p E) :
    (E.card : ℤ) = unorderedCount p E 0 0 + unorderedCount p E 0 1 + unorderedCount p E 0 2 +
      unorderedCount p E 1 1 + unorderedCount p E 1 3 + unorderedCount p E 2 2 +
      unorderedCount p E 2 3 + unorderedCount p E 3 3 := by
  have htotal := total_edgeVec p E
  rw [edgeVec_fbitMatrix p E h] at htotal
  norm_num [fbitMatrix, Fin.sum_univ_succ] at htotal
  omega

theorem fbit_class_parities [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges Fbit p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) :
    (2 : ℤ) ∣ unorderedCount p E 0 1 + unorderedCount p E 0 2 ∧
    (2 : ℤ) ∣ unorderedCount p E 0 1 + unorderedCount p E 1 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 0 2 + unorderedCount p E 2 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 1 3 + unorderedCount p E 2 3 := by
  obtain ⟨k0, hk0⟩ := class_row_two_dvd p E hloop heven 0
  obtain ⟨k1, hk1⟩ := class_row_two_dvd p E hloop heven 1
  obtain ⟨k2, hk2⟩ := class_row_two_dvd p E hloop heven 2
  obtain ⟨k3, hk3⟩ := class_row_two_dvd p E hloop heven 3
  rw [edgeVec_fbitMatrix p E hact] at hk0 hk1 hk2 hk3
  norm_num [fbitMatrix, Fin.sum_univ_succ] at hk0 hk1 hk2 hk3
  exact ⟨⟨k0 - unorderedCount p E 0 0, by omega⟩, ⟨k1 - unorderedCount p E 1 1, by omega⟩,
    ⟨k2 - unorderedCount p E 2 2, by omega⟩, ⟨k3 - unorderedCount p E 3 3, by omega⟩⟩

/-- An explicit witness for scalar counts (kernel parameter `a001 = 0`). -/
theorem fbit_scalar_witness (d0 x01 x02 d1 x13 d2 x23 d3 : ℤ)
    (hn : 0 ≤ d0 ∧ 0 ≤ x01 ∧ 0 ≤ x02 ∧ 0 ≤ d1 ∧ 0 ≤ x13 ∧ 0 ≤ d2 ∧ 0 ≤ x23 ∧ 0 ≤ d3)
    (hp0 : (2 : ℤ) ∣ x01 + x02) (hp1 : (2 : ℤ) ∣ x01 + x13)
    (hp3 : (2 : ℤ) ∣ x13 + x23) (hbit : (2 : ℤ) ∣ x01)
    (h3 : (3 : ℤ) ∣ d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) :
    ∃ a000 a001 a002 a011 a022 a113 a133 a223 a233 : ℤ,
      d0 = 3 * a000 + a001 + a002 ∧ x01 = 2 * a001 + 2 * a011 ∧
      x02 = 2 * a002 + 2 * a022 ∧ d1 = a011 + a113 ∧ x13 = 2 * a113 + 2 * a133 ∧
      d2 = a022 + a223 ∧ x23 = 2 * a223 + 2 * a233 ∧ d3 = a133 + a233 ∧
      a001 = 0 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a000 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a002 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a011 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a022 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a113 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a133 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a223 ∧
      -(d0 + x01 + x02 + d1 + x13 + d2 + x23 + d3) ≤ a233 := by
  obtain ⟨hd0, h01, h02, hd1, h13, hd2, h23, hd3⟩ := hn
  obtain ⟨u01, hu01⟩ := hbit
  obtain ⟨u02, hu02⟩ : ∃ u, x02 = 2 * u := by
    obtain ⟨k, hk⟩ := hp0; exact ⟨k - u01, by omega⟩
  obtain ⟨u13, hu13⟩ : ∃ u, x13 = 2 * u := by
    obtain ⟨k, hk⟩ := hp1; exact ⟨k - u01, by omega⟩
  obtain ⟨u23, hu23⟩ : ∃ u, x23 = 2 * u := by
    obtain ⟨k, hk⟩ := hp3; exact ⟨k - u13, by omega⟩
  obtain ⟨t, ht⟩ := h3
  obtain ⟨u0, hu0⟩ : ∃ u, d0 - u02 + (d2 - u23 + d3 - u13 + d1 - u01) = 3 * u :=
    ⟨t - (u01 + u02 + u13 + u23), by omega⟩
  refine ⟨u0, 0, u02 - (d2 - u23 + d3 - u13 + d1 - u01), u01, d2 - u23 + d3 - u13 + d1 - u01,
    d1 - u01, u13 - d1 + u01, u23 - d3 + u13 - d1 + u01, d3 - u13 + d1 - u01,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear ht
  all_goals omega

/-- The bit: the parity of the number of 01-edges. -/
def fbitBit (p : V → Fin 4) (E : Finset (Sym2 V)) : ℕ :=
  intParity (unorderedCount p E 0 1)

def FbitGood (p : V → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ ActiveEdges Fbit p E ∧
    (∀ v, Even (incidentLoad E v)) ∧ 3 ∣ E.card

theorem FbitGood_empty (p : V → Fin 4) : FbitGood p ∅ := by
  simp [FbitGood, ActiveEdges, OnePart.incidentLoad_empty]

theorem FbitGood_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : FbitGood p A) (hB : FbitGood p B) : FbitGood p (A ∪ B) := by
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

theorem fbitBit_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    fbitBit p (A ∪ B) = (fbitBit p A + fbitBit p B) % 2 := by
  simp only [fbitBit, unorderedCount_union p h, intParity_add]

/-- The parity evaluation of Fbit. -/
def fbitParity (p : V → Fin 4) : ParityEvaluation (FbitGood p) where
  empty_good := FbitGood_empty p
  union_good := FbitGood_union p
  value := fbitBit p
  value_lt := fun E _ => intParity_lt _
  empty_value := by simp [fbitBit, unorderedCount_empty, intParity_zero]
  union_value := fun h _ _ => fbitBit_union p h

/-- **The one-bit lattice of Fbit.** -/
theorem isIntDiv_Fbit_iff_good_bit [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p Fbit E ↔ FbitGood p E ∧ fbitBit p E = 0 := by
  rw [TypedDivisibilityCollapse.isIntDiv_iff Fbit_three_step Fbit_card hloop]
  constructor
  · rintro ⟨hact, heven, c, hc⟩
    have htot := fbit_total_count p E hact
    rw [edgeVec_fbitMatrix p E hact, fbit_edge_lattice_matrix] at hc
    set A0 := c {0, 0, 0} with hA0
    set A1 := c {0, 0, 1} with hA1
    set A2 := c {0, 0, 2} with hA2
    set A3 := c {0, 1, 1} with hA3
    set A4 := c {0, 2, 2} with hA4
    set A5 := c {1, 1, 3} with hA5
    set A6 := c {1, 3, 3} with hA6
    set A7 := c {2, 2, 3} with hA7
    set A8 := c {2, 3, 3} with hA8
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e02 := congrFun (congrFun hc 0) 2
    have e11 := congrFun (congrFun hc 1) 1
    have e13 := congrFun (congrFun hc 1) 3
    have e22 := congrFun (congrFun hc 2) 2
    have e23 := congrFun (congrFun hc 2) 3
    have e33 := congrFun (congrFun hc 3) 3
    simp only [fbitMatrix] at e00 e01 e02 e11 e13 e22 e23 e33
    norm_num at e00 e01 e02 e11 e13 e22 e23 e33
    have h3 : (3 : ℤ) ∣ (E.card : ℤ) := ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6 + A7 + A8, by omega⟩
    refine ⟨⟨hloop, hact, heven, by exact_mod_cast h3⟩, ?_⟩
    unfold fbitBit
    rw [intParity_eq_zero_iff]
    exact ⟨A1 + A3, by omega⟩
  · rintro ⟨⟨-, hact, heven, h3⟩, hbit⟩
    refine ⟨hact, heven, ?_⟩
    obtain ⟨hp0, hp1, -, hp3⟩ := fbit_class_parities p E hact hloop heven
    have htot := fbit_total_count p E hact
    have h3' : (3 : ℤ) ∣ unorderedCount p E 0 0 + unorderedCount p E 0 1 +
        unorderedCount p E 0 2 + unorderedCount p E 1 1 + unorderedCount p E 1 3 +
        unorderedCount p E 2 2 + unorderedCount p E 2 3 + unorderedCount p E 3 3 := by
      rw [← htot]; exact_mod_cast h3
    unfold fbitBit at hbit
    rw [intParity_eq_zero_iff] at hbit
    obtain ⟨a000, a001, a002, a011, a022, a113, a133, a223, a233, q0, q1, q2, q3, q4, q5, q6,
      q7, -, -, -, -, -, -, -, -, -⟩ :=
      fbit_scalar_witness _ _ _ _ _ _ _ _ ⟨unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _⟩ hp0 hp1 hp3 hbit h3'
    refine ⟨fbitCoeff a000 a001 a002 a011 a022 a113 a133 a223 a233, ?_⟩
    rw [edgeVec_fbitMatrix p E hact, fbit_edge_lattice_matrix]
    rw [bc0, bc1, bc2, bc3, bc4, bc5, bc6, bc7, bc8, q0, q1, q2, q3, q4, q5, q6, q7]

/-- **Bounded integral witnesses** for pieces with at most `K` edges. -/
theorem fbit_bounded_coefficients (K : ℕ) {W : Type*} [DecidableEq W]
    (p : W → Fin 4) (P : Finset (Sym2 W)) (hK : P.card ≤ K) (hdiv : IsIntDiv p Fbit P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ Fbit, c τ • typeEdgeVec τ ∧
      negativeMass Fbit c ≤ 8 * K := by
  have hact := active_of_isIntDiv Fbit_card hdiv
  obtain ⟨c, hc⟩ := hdiv.1
  have htot := fbit_total_count p P hact
  rw [edgeVec_fbitMatrix p P hact, fbit_edge_lattice_matrix] at hc
  set A0 := c {0, 0, 0} with hA0
  set A1 := c {0, 0, 1} with hA1
  set A2 := c {0, 0, 2} with hA2
  set A3 := c {0, 1, 1} with hA3
  set A4 := c {0, 2, 2} with hA4
  set A5 := c {1, 1, 3} with hA5
  set A6 := c {1, 3, 3} with hA6
  set A7 := c {2, 2, 3} with hA7
  set A8 := c {2, 3, 3} with hA8
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e02 := congrFun (congrFun hc 0) 2
  have e11 := congrFun (congrFun hc 1) 1
  have e13 := congrFun (congrFun hc 1) 3
  have e22 := congrFun (congrFun hc 2) 2
  have e23 := congrFun (congrFun hc 2) 3
  have e33 := congrFun (congrFun hc 3) 3
  simp only [fbitMatrix] at e00 e01 e02 e11 e13 e22 e23 e33
  norm_num at e00 e01 e02 e11 e13 e22 e23 e33
  obtain ⟨a000, a001, a002, a011, a022, a113, a133, a223, a233, q0, q1, q2, q3, q4, q5, q6, q7,
    z1, b0, b2, b3, b4, b5, b6, b7, b8⟩ :=
    fbit_scalar_witness (unorderedCount p P 0 0) (unorderedCount p P 0 1)
      (unorderedCount p P 0 2) (unorderedCount p P 1 1) (unorderedCount p P 1 3)
      (unorderedCount p P 2 2) (unorderedCount p P 2 3) (unorderedCount p P 3 3)
      ⟨unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _⟩
      ⟨A1 + A2 + A3 + A4, by omega⟩ ⟨A1 + A3 + A5 + A6, by omega⟩
      ⟨A5 + A6 + A7 + A8, by omega⟩ ⟨A1 + A3, by omega⟩
      ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6 + A7 + A8, by omega⟩
  refine ⟨fbitCoeff a000 a001 a002 a011 a022 a113 a133 a223 a233, ?_, ?_⟩
  · rw [edgeVec_fbitMatrix p P hact, fbit_edge_lattice_matrix]
    rw [bc0, bc1, bc2, bc3, bc4, bc5, bc6, bc7, bc8, q0, q1, q2, q3, q4, q5, q6, q7]
  · unfold negativeMass
    rw [sum_Fbit, bc0, bc1, bc2, bc3, bc4, bc5, bc6, bc7, bc8]
    have hKZ : (P.card : ℤ) ≤ K := by exact_mod_cast hK
    rw [← htot] at b0 b2 b3 b4 b5 b6 b7 b8
    clear * - z1 b0 b2 b3 b4 b5 b6 b7 b8 hKZ
    omega

#print axioms fbitParity
#print axioms isIntDiv_Fbit_iff_good_bit
#print axioms fbit_bounded_coefficients

end PaddedFbit
