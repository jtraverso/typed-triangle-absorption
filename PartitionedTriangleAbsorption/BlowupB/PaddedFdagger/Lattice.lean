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
# The family F† and its one-bit lattice

`Fdag = {000, 001, 002, 012, 123, 133, 233}` is `Fstar` without `333`. It has the same allowed
pairs as F* (00, 01, 02, 12, 13, 23, 33), `ThreeStepLinks` and common neighbour classes. The local
census found its quotient `Λ_ord / L_F† = ℤ/2` (Hermite forms: `det Λ_ord = 24`, `det L_F† = 48`).
The bit is

  `fdagBit E = ((x13 + x23)/2 + x01 + x12 + d3) mod 2`,

which needs the division by two, so (as for F2) it is a `ParityEvaluation` on the domain
`FdagGood` (loopless, allowed, even degrees, `3 ∣ |E|`). Every type of F† has bit 0; the
monochromatic triangle `333` has bit 1.

Lean content:
* `isIntDiv_Fdag_iff_good_bit`: on loopless sets, `IsIntDiv p Fdag E ↔ FdagGood p E ∧ bit = 0`;
* `fdagParity`: the parity evaluation;
* `fdag_bounded_coefficients`: the (unique) integral witness has negative mass `≤ 7 K`.
-/

namespace PaddedFdagger

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PaddedF12 PaddedFstar

/-- The family F†. -/
noncomputable def Fdag : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}, {2, 3, 3}}

theorem Fdag_card : ∀ τ ∈ Fdag, Multiset.card τ = 3 := by decide

theorem Fdag_three_step : ThreeStepLinks Fdag := by
  unfold ThreeStepLinks Link Fdag
  decide

theorem Fdag_subset_Fstar : Fdag ⊆ Fstar := by decide

theorem active_Fstar_of_Fdag {V : Type*} [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : ActiveEdges Fdag p E) : ActiveEdges Fstar p E := by
  intro a b hab
  obtain ⟨k, hk⟩ := h a b hab
  exact ⟨k, Fdag_subset_Fstar hk⟩

/-- The explicit coefficients, indexed by type. -/
noncomputable def fdagCoeff (a000 a001 a002 a012 a123 a133 a233 : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 0} then a000 else if τ = {0, 0, 1} then a001 else
  if τ = {0, 0, 2} then a002 else if τ = {0, 1, 2} then a012 else
  if τ = {1, 2, 3} then a123 else if τ = {1, 3, 3} then a133 else
  if τ = {2, 3, 3} then a233 else 0

theorem sum_Fdag {β : Type*} [AddCommMonoid β] (f : Multiset (Fin 4) → β) :
    ∑ τ ∈ Fdag, f τ = f {0, 0, 0} + f {0, 0, 1} + f {0, 0, 2} + f {0, 1, 2} +
      f {1, 2, 3} + f {1, 3, 3} + f {2, 3, 3} := by
  unfold Fdag
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  abel

theorem fdag_edge_lattice_matrix (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ Fdag, c τ • typeEdgeVec τ) =
      fstarMatrix (3 * c {0, 0, 0} + c {0, 0, 1} + c {0, 0, 2}) (2 * c {0, 0, 1} + c {0, 1, 2})
        (2 * c {0, 0, 2} + c {0, 1, 2}) (c {0, 1, 2} + c {1, 2, 3})
        (c {1, 2, 3} + 2 * c {1, 3, 3}) (c {1, 2, 3} + 2 * c {2, 3, 3})
        (c {1, 3, 3} + c {2, 3, 3}) := by
  rw [sum_Fdag]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fstarMatrix, typeEdgeVec] <;> ring

theorem dc0 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {0, 0, 0} = a := by
  unfold fdagCoeff; rw [if_pos rfl]
theorem dc1 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {0, 0, 1} = b := by
  unfold fdagCoeff; rw [if_neg (by decide), if_pos rfl]
theorem dc2 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {0, 0, 2} = c := by
  unfold fdagCoeff; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem dc3 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {0, 1, 2} = d := by
  unfold fdagCoeff; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem dc4 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {1, 2, 3} = e := by
  unfold fdagCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem dc5 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {1, 3, 3} = f := by
  unfold fdagCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]
theorem dc6 (a b c d e f g : ℤ) : fdagCoeff a b c d e f g {2, 3, 3} = g := by
  unfold fdagCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The unique witness for scalar counts: `a123 = (x13 + x23)/2 - d3`, `a012 = x12 - a123`,
the rest by halving and thirding. -/
theorem fdag_scalar_witness (d0 x01 x02 x12 x13 x23 d3 : ℤ)
    (hn : 0 ≤ d0 ∧ 0 ≤ x01 ∧ 0 ≤ x02 ∧ 0 ≤ x12 ∧ 0 ≤ x13 ∧ 0 ≤ x23 ∧ 0 ≤ d3)
    (hp0 : (2 : ℤ) ∣ x01 + x02) (hp1 : (2 : ℤ) ∣ x01 + x12 + x13)
    (hp3 : (2 : ℤ) ∣ x13 + x23)
    (hbit : (2 : ℤ) ∣ (x13 + x23 + 2 * (x01 + x12 + d3)) / 2)
    (h3 : (3 : ℤ) ∣ d0 + x01 + x02 + x12 + x13 + x23 + d3) :
    ∃ a000 a001 a002 a012 a123 a133 a233 : ℤ,
      d0 = 3 * a000 + a001 + a002 ∧ x01 = 2 * a001 + a012 ∧ x02 = 2 * a002 + a012 ∧
      x12 = a012 + a123 ∧ x13 = a123 + 2 * a133 ∧ x23 = a123 + 2 * a233 ∧
      d3 = a133 + a233 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a000 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a001 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a002 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a012 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a123 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a133 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3) ≤ a233 := by
  obtain ⟨hd0, h01, h02, h12, h13, h23, hd3⟩ := hn
  obtain ⟨k3, hk3⟩ := hp3
  have hhalf : (x13 + x23 + 2 * (x01 + x12 + d3)) / 2 = k3 + x01 + x12 + d3 := by omega
  rw [hhalf] at hbit
  obtain ⟨b, hb⟩ := hbit
  obtain ⟨k0, hk0⟩ := hp0
  obtain ⟨k1, hk1⟩ := hp1
  obtain ⟨t, ht⟩ := h3
  obtain ⟨u1, hu1⟩ : ∃ u, x01 - x12 + k3 - d3 = 2 * u := ⟨b - x12 - d3, by omega⟩
  obtain ⟨u2, hu2⟩ : ∃ u, x02 - x12 + k3 - d3 = 2 * u := ⟨k0 - x01 + u1, by omega⟩
  obtain ⟨u5, hu5⟩ : ∃ u, x13 - k3 + d3 = 2 * u := ⟨k1 - b + d3, by omega⟩
  obtain ⟨u6, hu6⟩ : ∃ u, x23 - k3 + d3 = 2 * u := ⟨u5 + k3 - x13, by omega⟩
  obtain ⟨u0, hu0⟩ : ∃ u, d0 - u1 - u2 = 3 * u :=
    ⟨t - u1 - u2 - (x12 - k3 + d3) - (k3 - d3) - u5 - u6, by omega⟩
  refine ⟨u0, u1, u2, x12 - k3 + d3, k3 - d3, u5, u6, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear hk0 hk1 hb ht
  all_goals omega

variable {V : Type*} [DecidableEq V]

/-- The numerator of the bit (even on the good domain). -/
def fdagNum (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  unorderedCount p E 1 3 + unorderedCount p E 2 3 +
    2 * (unorderedCount p E 0 1 + unorderedCount p E 1 2 + unorderedCount p E 3 3)

def fdagBit (p : V → Fin 4) (E : Finset (Sym2 V)) : ℕ :=
  intParity (fdagNum p E / 2)

def FdagGood (p : V → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ ActiveEdges Fdag p E ∧
    (∀ v, Even (incidentLoad E v)) ∧ 3 ∣ E.card

theorem fdagNum_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    fdagNum p (A ∪ B) = fdagNum p A + fdagNum p B := by
  simp only [fdagNum, unorderedCount_union p h]
  ring

theorem fdagNum_even [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges Fdag p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) : (2 : ℤ) ∣ fdagNum p E := by
  obtain ⟨-, -, -, ⟨k, hk⟩⟩ :=
    fstar_class_parities p E (active_Fstar_of_Fdag p E hact) hloop heven
  exact ⟨k + (unorderedCount p E 0 1 + unorderedCount p E 1 2 + unorderedCount p E 3 3),
    by unfold fdagNum; omega⟩

theorem FdagGood_empty (p : V → Fin 4) : FdagGood p ∅ := by
  simp [FdagGood, ActiveEdges, OnePart.incidentLoad_empty]

theorem FdagGood_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : FdagGood p A) (hB : FdagGood p B) : FdagGood p (A ∪ B) := by
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

theorem fdagBit_union [Fintype V] (p : V → Fin 4) {A B : Finset (Sym2 V)}
    (h : Disjoint A B) (hA : FdagGood p A) (hB : FdagGood p B) :
    fdagBit p (A ∪ B) = (fdagBit p A + fdagBit p B) % 2 := by
  obtain ⟨a, ha⟩ := fdagNum_even p A hA.2.1 hA.1 hA.2.2.1
  obtain ⟨b, hb⟩ := fdagNum_even p B hB.2.1 hB.1 hB.2.2.1
  have hsum : fdagNum p (A ∪ B) / 2 = fdagNum p A / 2 + fdagNum p B / 2 := by
    rw [fdagNum_union p h]
    omega
  simp only [fdagBit, hsum, intParity_add]

/-- The parity evaluation of F†. -/
def fdagParity [Fintype V] (p : V → Fin 4) : ParityEvaluation (FdagGood p) where
  empty_good := FdagGood_empty p
  union_good := FdagGood_union p
  value := fdagBit p
  value_lt := fun E _ => intParity_lt _
  empty_value := by simp [fdagBit, fdagNum, unorderedCount_empty, intParity_zero]
  union_value := fdagBit_union p

/-- **The one-bit lattice of F†.** -/
theorem isIntDiv_Fdag_iff_good_bit [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p Fdag E ↔ FdagGood p E ∧ fdagBit p E = 0 := by
  rw [TypedDivisibilityCollapse.isIntDiv_iff Fdag_three_step Fdag_card hloop]
  constructor
  · rintro ⟨hact, heven, c, hc⟩
    have hact' := active_Fstar_of_Fdag p E hact
    have htot := fstar_total_count p E hact'
    rw [edgeVec_fstarMatrix p E hact', fdag_edge_lattice_matrix] at hc
    set A0 := c {0, 0, 0} with hA0
    set A1 := c {0, 0, 1} with hA1
    set A2 := c {0, 0, 2} with hA2
    set A3 := c {0, 1, 2} with hA3
    set A4 := c {1, 2, 3} with hA4
    set A5 := c {1, 3, 3} with hA5
    set A6 := c {2, 3, 3} with hA6
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
    unfold fdagBit
    rw [intParity_eq_zero_iff]
    have hnum : fdagNum p E / 2 = 2 * (A1 + A3 + A4 + A5 + A6) := by
      unfold fdagNum
      omega
    rw [hnum]
    exact dvd_mul_right 2 _
  · rintro ⟨⟨-, hact, heven, h3⟩, hbit⟩
    refine ⟨hact, heven, ?_⟩
    have hact' := active_Fstar_of_Fdag p E hact
    obtain ⟨hp0, hp1, -, hp3⟩ := fstar_class_parities p E hact' hloop heven
    have htot := fstar_total_count p E hact'
    have h3' : (3 : ℤ) ∣ unorderedCount p E 0 0 + unorderedCount p E 0 1 +
        unorderedCount p E 0 2 + unorderedCount p E 1 2 + unorderedCount p E 1 3 +
        unorderedCount p E 2 3 + unorderedCount p E 3 3 := by
      rw [← htot]; exact_mod_cast h3
    unfold fdagBit at hbit
    rw [intParity_eq_zero_iff] at hbit
    obtain ⟨a000, a001, a002, a012, a123, a133, a233, q0, q1, q2, q3, q4, q5, q6,
      -, -, -, -, -, -, -⟩ :=
      fdag_scalar_witness _ _ _ _ _ _ _ ⟨unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _⟩ hp0 hp1 hp3 hbit h3'
    refine ⟨fdagCoeff a000 a001 a002 a012 a123 a133 a233, ?_⟩
    rw [edgeVec_fstarMatrix p E hact', fdag_edge_lattice_matrix]
    rw [dc0, dc1, dc2, dc3, dc4, dc5, dc6, q0, q1, q2, q3, q4, q5, q6]

/-- **Bounded integral witnesses** for pieces with at most `K` edges. -/
theorem fdag_bounded_coefficients (K : ℕ) {W : Type*} [DecidableEq W]
    (p : W → Fin 4) (P : Finset (Sym2 W)) (hK : P.card ≤ K) (hdiv : IsIntDiv p Fdag P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ Fdag, c τ • typeEdgeVec τ ∧
      negativeMass Fdag c ≤ 7 * K := by
  have hact := active_of_isIntDiv Fdag_card hdiv
  have hact' := active_Fstar_of_Fdag p P hact
  obtain ⟨c, hc⟩ := hdiv.1
  have htot := fstar_total_count p P hact'
  rw [edgeVec_fstarMatrix p P hact', fdag_edge_lattice_matrix] at hc
  set A0 := c {0, 0, 0} with hA0
  set A1 := c {0, 0, 1} with hA1
  set A2 := c {0, 0, 2} with hA2
  set A3 := c {0, 1, 2} with hA3
  set A4 := c {1, 2, 3} with hA4
  set A5 := c {1, 3, 3} with hA5
  set A6 := c {2, 3, 3} with hA6
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e02 := congrFun (congrFun hc 0) 2
  have e12 := congrFun (congrFun hc 1) 2
  have e13 := congrFun (congrFun hc 1) 3
  have e23 := congrFun (congrFun hc 2) 3
  have e33 := congrFun (congrFun hc 3) 3
  simp only [fstarMatrix] at e00 e01 e02 e12 e13 e23 e33
  norm_num at e00 e01 e02 e12 e13 e23 e33
  have hhalf : (unorderedCount p P 1 3 + unorderedCount p P 2 3 +
      2 * (unorderedCount p P 0 1 + unorderedCount p P 1 2 + unorderedCount p P 3 3)) / 2 =
      2 * (A1 + A3 + A4 + A5 + A6) := by omega
  obtain ⟨a000, a001, a002, a012, a123, a133, a233, q0, q1, q2, q3, q4, q5, q6,
    b0, b1, b2, b3, b4, b5, b6⟩ :=
    fdag_scalar_witness (unorderedCount p P 0 0) (unorderedCount p P 0 1)
      (unorderedCount p P 0 2) (unorderedCount p P 1 2) (unorderedCount p P 1 3)
      (unorderedCount p P 2 3) (unorderedCount p P 3 3)
      ⟨unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _⟩
      ⟨A1 + A2 + A3, by omega⟩ ⟨A1 + A3 + A4 + A5, by omega⟩
      ⟨A4 + A5 + A6, by omega⟩ (by rw [hhalf]; exact dvd_mul_right 2 _)
      ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6, by omega⟩
  refine ⟨fdagCoeff a000 a001 a002 a012 a123 a133 a233, ?_, ?_⟩
  · rw [edgeVec_fstarMatrix p P hact', fdag_edge_lattice_matrix]
    rw [dc0, dc1, dc2, dc3, dc4, dc5, dc6, q0, q1, q2, q3, q4, q5, q6]
  · unfold negativeMass
    rw [sum_Fdag, dc0, dc1, dc2, dc3, dc4, dc5, dc6]
    have hKZ : (P.card : ℤ) ≤ K := by exact_mod_cast hK
    rw [← htot] at b0 b1 b2 b3 b4 b5 b6
    clear * - b0 b1 b2 b3 b4 b5 b6 hKZ
    omega

#print axioms fdagParity
#print axioms isIntDiv_Fdag_iff_good_bit
#print axioms fdag_bounded_coefficients

end PaddedFdagger
