/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Cert
public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Lattice

@[expose] public section

/-!
# Scalar form of the lattice conditions

For a family `F` on four classes, an edge set is described by its unordered class-pair counts
`u i j`. `ScalarHyp F u` collects what ordinary divisibility on allowed support says about `u`
(symmetry, nonnegativity, zeros on forbidden pairs, even class rows, `3 ∣` total), and
`LatEq F u c` says that `c` is an integral `F`-witness for `u`. A scalar solution of
`ScalarHyp → ∃ c, LatEq` with an explicit linear bound on the negative mass gives both
`TrivialLattice F` and `WitnessBoundK F K B` (`trivialLattice_of_scalar`,
`witnessBound_of_scalar`).
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedF12 PaddedGeneral

/-- The number of edges, from the class-pair counts. -/
noncomputable def totalU (u : Fin 4 → Fin 4 → ℤ) : ℤ := ∑ i, ∑ j, if i ≤ j then u i j else 0

/-- Ordinary divisibility on allowed support, in terms of class-pair counts. -/
structure ScalarHyp (F : Finset (Multiset (Fin 4))) (u : Fin 4 → Fin 4 → ℤ) : Prop where
  symm : ∀ i j, u i j = u j i
  nonneg : ∀ i j, 0 ≤ u i j
  forbid : ∀ i j, (¬ ∃ k, Link F i j k) → u i j = 0
  parity : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j
  three : (3 : ℤ) ∣ totalU u

/-- `c` is an integral `F`-witness for the counts `u`. -/
def LatEq (F : Finset (Multiset (Fin 4))) (u : Fin 4 → Fin 4 → ℤ)
    (c : Multiset (Fin 4) → ℤ) : Prop :=
  ∀ i j, (if i = j then 2 else 1) * u i j = ∑ τ ∈ F, c τ * typeEdgeVec τ i j

/-- Coefficients given by a list of (type, value) pairs. -/
noncomputable def coeffList : List (Multiset (Fin 4) × ℤ) → Multiset (Fin 4) → ℤ
  | [], _ => 0
  | (t, a) :: l, τ => if τ = t then a else coeffList l τ

theorem typeEdgeVec_row {τ : Multiset (Fin 4)} (hτ : Multiset.card τ = 3) (i : Fin 4) :
    ∑ j, typeEdgeVec τ i j = 2 * (τ.count i : ℤ) := by
  have h : ∑ j : Fin 4, (τ.count j : ℤ) = 3 := by
    exact_mod_cast (Multiset.sum_count_eq_card (by simp)).trans hτ
  simp only [typeEdgeVec, sum_sub_distrib, ← mul_sum, h]
  simp only [sum_ite_eq, mem_univ, if_true]
  ring

theorem row_split (u : Fin 4 → Fin 4 → ℤ) (i : Fin 4) :
    ∑ j, (if i = j then (2 : ℤ) else 1) * u i j = 2 * u i i + ∑ j, if i = j then 0 else u i j := by
  have h : ∀ j, (if i = j then (2 : ℤ) else 1) * u i j =
      (if i = j then 2 * u i i else 0) + (if i = j then 0 else u i j) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [sum_congr rfl fun j _ => h j, sum_add_distrib, sum_ite_eq]
  simp

theorem weighted_total (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i) :
    ∑ i, ∑ j, (if i = j then (2 : ℤ) else 1) * u i j = 2 * totalU u := by
  simp only [totalU, Fin.sum_univ_four]
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false, Fin.reduceLE, le_refl]
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]
  norm_num
  ring

theorem scalarHyp_of_latEq {F : Finset (Multiset (Fin 4))}
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) {u : Fin 4 → Fin 4 → ℤ}
    {c : Multiset (Fin 4) → ℤ} (hs : ∀ i j, u i j = u j i) (hn : ∀ i j, 0 ≤ u i j)
    (hf : ∀ i j, (¬ ∃ k, Link F i j k) → u i j = 0) (h : LatEq F u c) : ScalarHyp F u := by
  refine ⟨hs, hn, hf, fun i => ?_, ?_⟩
  · have hrow : ∑ j, (if i = j then (2 : ℤ) else 1) * u i j =
        2 * ∑ τ ∈ F, c τ * (τ.count i : ℤ) := by
      rw [sum_congr rfl fun j _ => h i j, sum_comm, mul_sum]
      refine sum_congr rfl fun τ hτ => ?_
      rw [← mul_sum, typeEdgeVec_row (hcard τ hτ)]
      ring
    rw [row_split] at hrow
    exact ⟨∑ τ ∈ F, c τ * (τ.count i : ℤ) - u i i, by linarith⟩
  · have htot : ∑ i, ∑ j, (if i = j then (2 : ℤ) else 1) * u i j = 6 * ∑ τ ∈ F, c τ := by
      rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => h i j]
      rw [sum_congr rfl fun i _ => sum_comm, sum_comm, mul_sum]
      refine sum_congr rfl fun τ hτ => ?_
      simp only [← mul_sum]
      rw [PaddedTrivial.typeEdgeVec_total (hcard τ hτ)]
      ring
    rw [weighted_total u hs] at htot
    exact ⟨∑ τ ∈ F, c τ, by linarith⟩

section Counts

variable {V : Type*} [DecidableEq V]

theorem link_swap12 (F : Finset (Multiset (Fin 4))) (i j k : Fin 4) :
    Link F i j k ↔ Link F j i k := by
  unfold Link
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.insert_eq_cons,
    Multiset.insert_eq_cons, Multiset.cons_swap]

theorem latEq_counts_iff (F : Finset (Multiset (Fin 4))) (p : V → Fin 4) (E : Finset (Sym2 V))
    (c : Multiset (Fin 4) → ℤ) :
    LatEq F (unorderedCount p E) c ↔ edgeVec p E = ∑ τ ∈ F, c τ • typeEdgeVec τ := by
  constructor
  · intro h
    funext i j
    rw [edgeVec_unorderedCount, h i j]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [edgeVec_unorderedCount] at this
    rw [this]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem counts_forbid {F : Finset (Multiset (Fin 4))} {p : V → Fin 4} {E : Finset (Sym2 V)}
    (hact : ActiveEdges F p E) (i j : Fin 4) (hij : ¬ ∃ k, Link F i j k) :
    unorderedCount p E i j = 0 := by
  apply unorderedCount_zero_of_forbidden
  intro e he hmap
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨k, hk⟩ := hact a b he
    simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hij ⟨k, ha ▸ hb ▸ hk⟩
    · exact hij ⟨k, (link_swap12 F _ _ _).mp (ha ▸ hb ▸ hk)⟩

theorem totalU_counts (p : V → Fin 4) (E : Finset (Sym2 V)) :
    totalU (unorderedCount p E) = E.card := by
  have h := total_edgeVec p E
  simp only [edgeVec_unorderedCount] at h
  rw [weighted_total _ (unorderedCount_swap p E)] at h
  linarith

theorem counts_parity [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v, Even (incidentLoad E v)) (i : Fin 4) :
    (2 : ℤ) ∣ ∑ j, if i = j then 0 else unorderedCount p E i j := by
  have h := class_row_two_dvd p E hloop heven i
  simp only [edgeVec_unorderedCount] at h
  rw [row_split] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k - unorderedCount p E i i, by linarith⟩

end Counts

/-- **Trivial lattice from a scalar solution.** -/
theorem trivialLattice_of_scalar (F : Finset (Multiset (Fin 4))) (hthree : ThreeStepLinks F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u, ScalarHyp F u → ∃ c, LatEq F u c) : TrivialLattice F := by
  intro V _ _ p E hloop
  constructor
  · intro h
    exact ⟨active_of_isIntDiv hcard h, PaddedTrivial.even3_of_isIntDiv hcard p hloop h⟩
  · rintro ⟨hact, h3, hev⟩
    rw [isIntDiv_iff hthree hcard hloop]
    refine ⟨hact, hev, ?_⟩
    have hS : ScalarHyp F (unorderedCount p E) :=
      ⟨unorderedCount_swap p E, unorderedCount_nonneg p E, counts_forbid hact,
        counts_parity p E hloop hev, by rw [totalU_counts]; exact_mod_cast h3⟩
    obtain ⟨c, hc⟩ := hsol _ hS
    exact ⟨c, (latEq_counts_iff F p E c).mp hc⟩

/-- **Witness bound from a scalar solution with a bounded negative mass.** -/
theorem witnessBound_of_scalar (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (K B : ℕ)
    (hsol : ∀ u, ScalarHyp F u → totalU u ≤ K → ∃ c, LatEq F u c ∧ negativeMass F c ≤ B) :
    WitnessBoundK F K B := by
  intro W _ p P hK hdiv
  obtain ⟨c0, hc0⟩ := hdiv.1
  have hact := active_of_isIntDiv hcard hdiv
  have hS : ScalarHyp F (unorderedCount p P) :=
    scalarHyp_of_latEq hcard (unorderedCount_swap p P) (unorderedCount_nonneg p P)
      (counts_forbid hact) ((latEq_counts_iff F p P c0).mpr hc0)
  obtain ⟨c, hc, hm⟩ := hsol _ hS (by rw [totalU_counts]; exact_mod_cast hK)
  exact ⟨c, (latEq_counts_iff F p P c).mp hc, hm⟩

theorem negativeMass_le_of_lower (F : Finset (Multiset (Fin 4))) (c : Multiset (Fin 4) → ℤ)
    (M : ℕ) (h : ∀ τ ∈ F, -(M : ℤ) ≤ c τ) : negativeMass F c ≤ F.card * M := by
  unfold negativeMass
  calc ∑ τ ∈ F, (-c τ).toNat ≤ ∑ _τ ∈ F, M := sum_le_sum fun τ hτ => by
        have := h τ hτ; omega
    _ = F.card * M := by rw [sum_const, smul_eq_mul]

/-- Both lattice inputs from one scalar solution whose coefficients are at least
`-(2 e + 4)`, where `e` is the number of edges. -/
theorem lattice_inputs_of_scalar (F : Finset (Multiset (Fin 4))) (hthree : ThreeStepLinks F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u, ScalarHyp F u →
      ∃ c, LatEq F u c ∧ ∀ τ ∈ F, -(2 * totalU u + 4) ≤ c τ) (K : ℕ) :
    TrivialLattice F ∧ WitnessBoundK F K (F.card * (2 * K + 4)) := by
  refine ⟨trivialLattice_of_scalar F hthree hcard fun u hu => ?_,
    witnessBound_of_scalar F hcard K _ fun u hu hK => ?_⟩
  · obtain ⟨c, hc, -⟩ := hsol u hu; exact ⟨c, hc⟩
  · obtain ⟨c, hc, hm⟩ := hsol u hu
    refine ⟨c, hc, negativeMass_le_of_lower F c _ fun τ hτ => ?_⟩
    have := hm τ hτ
    push_cast
    omega

end PaddedNoCommon
