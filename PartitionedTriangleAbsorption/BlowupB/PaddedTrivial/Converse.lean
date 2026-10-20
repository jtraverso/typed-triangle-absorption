/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Lattice

@[expose] public section

/-!
# Ordinary divisibility implies `Ftriv`-divisibility

For a loopless edge set with allowed support, `3 ∣ |E|` and even degrees give explicit
integral witnesses for the edge lattice and for every degree lattice of `Ftriv`.
-/

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PaddedF12

/-! ### Ordinary divisibility implies `Ftriv`-divisibility -/

/-- A coefficient vector on the eight types of `Ftriv`. -/
noncomputable def mkCoeff (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 0} then a0 else if τ = {0, 0, 1} then a1 else if τ = {0, 0, 2} then a2 else
  if τ = {0, 1, 2} then a3 else if τ = {1, 2, 3} then a4 else if τ = {1, 3, 3} then a5 else
  if τ = {2, 3, 3} then a6 else if τ = {3, 3, 3} then a7 else 0

theorem mkCoeff_values (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) :
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {0, 0, 0} = a0 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {0, 0, 1} = a1 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {0, 0, 2} = a2 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {0, 1, 2} = a3 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {1, 2, 3} = a4 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {1, 3, 3} = a5 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {2, 3, 3} = a6 ∧
    mkCoeff a0 a1 a2 a3 a4 a5 a6 a7 {3, 3, 3} = a7 := by
  unfold mkCoeff
  simp (config := {decide := true})

section Converse

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem unordered_forbidden (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges Ftriv p E) :
    unorderedCount p E 0 3 = 0 ∧ unorderedCount p E 1 1 = 0 ∧ unorderedCount p E 2 2 = 0 := by
  have hf : ∀ a b k : Fin 4, Link Ftriv a b k →
      s(a, b) ≠ s(0, 3) ∧ s(a, b) ≠ s(1, 1) ∧ s(a, b) ≠ s(2, 2) := by
    unfold Link Ftriv; decide
  refine ⟨?_, ?_, ?_⟩ <;> apply unorderedCount_zero_of_forbidden <;> intro e he <;>
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨k, hk⟩ := hact a b he
      have := hf (p a) (p b) k hk
      simp only [Sym2.map_mk]
      tauto

theorem class_degree_even (p : V → Fin 4) (E : Finset (Sym2 V)) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) (i : Fin 4) :
    Even (∑ j, edgeVec p E i j) := by
  have h : ∑ j, edgeVec p E i j = ∑ v ∈ univ.filter (fun v => p v = i), (incidentLoad E v : ℤ) := by
    simp only [StructuralF3General.LatticeBasics.edgeVec_eq_sum_degVec]
    rw [sum_comm]
    exact sum_congr rfl fun v _ => sum_degVec p E hloop v
  rw [h]
  exact Finset.even_sum _ fun v _ => (Int.even_coe_nat _).mpr (heven v)

omit [Fintype V] in
theorem degVec_forbidden (p : V → Fin 4) (E : Finset (Sym2 V)) (hact : ActiveEdges Ftriv p E)
    (v : V) (j : Fin 4) (hj : ¬ trivAllowed (p v) j) : degVec p E v j = 0 := by
  by_contra h
  obtain ⟨b, hb, rfl⟩ := exists_of_degVec_ne_zero h
  exact hj ((Ftriv_allowed_iff _ _).mp (hact v b hb))

/-- The ordered edge vector of an allowed-support edge set, in unordered counts. -/
def uMatrix (x00 x01 x02 x12 x13 x23 x33 : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![2 * x00, x01, x02, 0], ![x01, 0, x12, x13], ![x02, x12, 0, x23], ![0, x13, x23, 2 * x33]]

theorem edge_witness (x00 x01 x02 x12 x13 x23 x33 N : ℤ) (h3 : 3 ∣ N)
    (htot : 2 * x00 + 2 * x33 + 2 * (x01 + x02 + x12 + x13 + x23) = 2 * N)
    (e0 : Even (2 * x00 + x01 + x02)) (e1 : Even (x01 + x12 + x13))
    (e3 : Even (x13 + x23 + 2 * x33)) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ℤ, trivEdgeMatrix a0 a1 a2 a3 a4 a5 a6 a7 =
      uMatrix x00 x01 x02 x12 x13 x23 x33 := by
  obtain ⟨a, ha2, ha3, ha0, ha5⟩ : ∃ a : ℤ, (x01 - a) % 2 = 0 ∧
      (2 * x00 - x01 - x02 + 2 * a) % 6 = 0 ∧ 0 ≤ a ∧ a < 6 := by
    refine ⟨(3 * (x01 % 2) + 4 * ((2 * (x01 + x02 - 2 * x00)) % 3)) % 6, ?_, ?_, ?_, ?_⟩
    all_goals rcases e0 with ⟨r, hr⟩; omega
  rcases e0 with ⟨r0, hr0⟩
  rcases e1 with ⟨r1, hr1⟩
  rcases e3 with ⟨r3, hr3⟩
  obtain ⟨q, hq⟩ := h3
  refine ⟨(2 * x00 - x01 - x02 + 2 * a) / 6, (x01 - a) / 2, (x02 - a) / 2, a, x12 - a,
    (x13 - (x12 - a)) / 2, (x23 - (x12 - a)) / 2,
    (2 * x33 - x13 - x23 + 2 * (x12 - a)) / 6, ?_⟩
  funext i j
  fin_cases i <;> fin_cases j <;> simp [trivEdgeMatrix, uMatrix] <;> omega

omit [Fintype V] in
theorem edgeVec_eq_uMatrix (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges Ftriv p E) :
    edgeVec p E = uMatrix (unorderedCount p E 0 0) (unorderedCount p E 0 1)
      (unorderedCount p E 0 2) (unorderedCount p E 1 2) (unorderedCount p E 1 3)
      (unorderedCount p E 2 3) (unorderedCount p E 3 3) := by
  obtain ⟨z03, z11, z22⟩ := unordered_forbidden p E hact
  have hsw := unorderedCount_swap p E
  funext i j
  rw [edgeVec_unorderedCount]
  fin_cases i <;> fin_cases j <;>
    simp [uMatrix, hsw 1 0, hsw 2 0, hsw 2 1, hsw 3 0, hsw 3 1, hsw 3 2, z03, z11, z22]

theorem deg_witness0 (e0 e1 e2 e3 : ℤ) (z3 : e3 = 0) (hev : Even (e0 + e1 + e2 + e3)) :
    ∃ c : Multiset (Fin 4) → ℤ,
      ![e0, e1, e2, e3] = ∑ τ ∈ Ftriv with (0 : Fin 4) ∈ τ, c τ • typeDegVec τ 0 := by
  rcases hev with ⟨r, hr⟩
  refine ⟨mkCoeff 0 ((e0 + e1 - e2) / 2) ((e0 - e1 + e2) / 2) ((-e0 + e1 + e2) / 2)
    0 0 0 0, ?_⟩
  rw [(deg_lattice_eval _).1]
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩ := mkCoeff_values 0 ((e0 + e1 - e2) / 2)
    ((e0 - e1 + e2) / 2) ((-e0 + e1 + e2) / 2) 0 0 0 0
  rw [m0, m1, m2, m3]
  funext j
  fin_cases j <;> simp <;> omega

theorem deg_witness1 (e0 e1 e2 e3 : ℤ) (z1 : e1 = 0) (hev : Even (e0 + e1 + e2 + e3)) :
    ∃ c : Multiset (Fin 4) → ℤ,
      ![e0, e1, e2, e3] = ∑ τ ∈ Ftriv with (1 : Fin 4) ∈ τ, c τ • typeDegVec τ 1 := by
  rcases hev with ⟨r, hr⟩
  refine ⟨mkCoeff 0 ((e0 - (e2 - e3 % 2)) / 2) 0 (e2 - e3 % 2) (e3 % 2)
    ((e3 - e3 % 2) / 2) 0 0, ?_⟩
  rw [(deg_lattice_eval _).2.1]
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩ := mkCoeff_values 0 ((e0 - (e2 - e3 % 2)) / 2) 0
    (e2 - e3 % 2) (e3 % 2) ((e3 - e3 % 2) / 2) 0 0
  rw [m1, m3, m4, m5]
  funext j
  fin_cases j <;> simp <;> omega

theorem deg_witness2 (e0 e1 e2 e3 : ℤ) (z2 : e2 = 0) (hev : Even (e0 + e1 + e2 + e3)) :
    ∃ c : Multiset (Fin 4) → ℤ,
      ![e0, e1, e2, e3] = ∑ τ ∈ Ftriv with (2 : Fin 4) ∈ τ, c τ • typeDegVec τ 2 := by
  rcases hev with ⟨r, hr⟩
  refine ⟨mkCoeff 0 0 ((e0 - (e1 - e3 % 2)) / 2) (e1 - e3 % 2) (e3 % 2)
    0 ((e3 - e3 % 2) / 2) 0, ?_⟩
  rw [(deg_lattice_eval _).2.2.1]
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩ := mkCoeff_values 0 0 ((e0 - (e1 - e3 % 2)) / 2)
    (e1 - e3 % 2) (e3 % 2) 0 ((e3 - e3 % 2) / 2) 0
  rw [m2, m3, m4, m6]
  funext j
  fin_cases j <;> simp <;> omega

theorem deg_witness3 (e0 e1 e2 e3 : ℤ) (z0 : e0 = 0) (hev : Even (e0 + e1 + e2 + e3)) :
    ∃ c : Multiset (Fin 4) → ℤ,
      ![e0, e1, e2, e3] = ∑ τ ∈ Ftriv with (3 : Fin 4) ∈ τ, c τ • typeDegVec τ 3 := by
  rcases hev with ⟨r, hr⟩
  refine ⟨mkCoeff 0 0 0 0 ((e1 + e2 - e3) / 2) ((e1 - e2 + e3) / 2) ((-e1 + e2 + e3) / 2)
    0, ?_⟩
  rw [(deg_lattice_eval _).2.2.2]
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩ := mkCoeff_values 0 0 0 0 ((e1 + e2 - e3) / 2)
    ((e1 - e2 + e3) / 2) ((-e1 + e2 + e3) / 2) 0
  rw [m4, m5, m6, m7]
  funext j
  fin_cases j <;> simp <;> omega

/-- **Ordinary divisibility on allowed support gives `Ftriv`-divisibility.** -/
theorem isIntDiv_Ftriv_of_even3 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges Ftriv p E) (h : OnePart.Even3 E) :
    IsIntDiv p Ftriv E := by
  obtain ⟨h3, heven⟩ := h
  refine ⟨?_, fun v => ?_⟩
  · have hU := edgeVec_eq_uMatrix p E hact
    have c0 := class_degree_even p E hloop heven 0
    have c1 := class_degree_even p E hloop heven 1
    have c3 := class_degree_even p E hloop heven 3
    have htot := edgeVec_total p E
    rw [hU] at htot c0 c1 c3
    simp only [sum_fin4, uMatrix] at htot c0 c1 c3
    norm_num at htot c0 c1 c3
    have h3z : (3 : ℤ) ∣ E.card := by exact_mod_cast h3
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, ha⟩ := edge_witness (unorderedCount p E 0 0)
      (unorderedCount p E 0 1) (unorderedCount p E 0 2) (unorderedCount p E 1 2)
      (unorderedCount p E 1 3) (unorderedCount p E 2 3) (unorderedCount p E 3 3) _ h3z
      (by linarith) (by simpa [add_assoc] using c0) (by simpa [add_assoc] using c1)
      (by simpa [add_assoc] using c3)
    refine ⟨mkCoeff a0 a1 a2 a3 a4 a5 a6 a7, ?_⟩
    rw [edge_lattice_eval, hU, ← ha]
    obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩ := mkCoeff_values a0 a1 a2 a3 a4 a5 a6 a7
    rw [m0, m1, m2, m3, m4, m5, m6, m7]
  · have hsum := sum_degVec p E hloop v
    have hev := (Int.even_coe_nat _).mpr (heven v)
    rw [← hsum, sum_fin4] at hev
    have hz := degVec_forbidden p E hact v
    have hdv : degVec p E v = ![degVec p E v 0, degVec p E v 1, degVec p E v 2,
        degVec p E v 3] := by
      funext j; fin_cases j <;> rfl
    rw [hdv]
    have hcases : p v = 0 ∨ p v = 1 ∨ p v = 2 ∨ p v = 3 := by
      generalize p v = a; fin_cases a <;> simp
    rcases hcases with h | h | h | h <;> rw [h] at hz ⊢
    · exact deg_witness0 _ _ _ _ (hz 3 (by decide)) hev
    · exact deg_witness1 _ _ _ _ (hz 1 (by decide)) hev
    · exact deg_witness2 _ _ _ _ (hz 2 (by decide)) hev
    · exact deg_witness3 _ _ _ _ (hz 0 (by decide)) hev

/-- **The `Ftriv` lattice is trivial**: on loopless edge sets with allowed support, integral
`Ftriv`-divisibility is ordinary divisibility. -/
theorem isIntDiv_Ftriv_iff_even3 (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges Ftriv p E) :
    IsIntDiv p Ftriv E ↔ OnePart.Even3 E :=
  ⟨even3_of_isIntDiv Ftriv_card_three p hloop, isIntDiv_Ftriv_of_even3 p E hloop hact⟩

end Converse

#print axioms isIntDiv_Ftriv_iff_even3

end PaddedTrivial
