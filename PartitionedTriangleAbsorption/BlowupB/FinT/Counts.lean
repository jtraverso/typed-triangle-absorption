/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.LatticeFrame

@[expose] public section

/-!
# Class-pair counts and the scalar lattice frame, for families on `Fin t`

Generic copies of the counting lemmas of `PaddedF12.PhysicalCounts` (`unorderedCount`,
`edgeVec_unorderedCount`, `total_edgeVec`, `class_row_two_dvd`) and of the scalar frame of
`PaddedNoCommon.LatticeFrame` (`ScalarHyp`, `LatEq`, `scalarHyp_of_latEq`, `witnessBound_of_scalar`),
with `Fin 4` replaced by `Fin t` (the `Fin 4`-specific `decide` / `Fin.sum_univ_four` steps are
replaced by generic arguments).
-/

namespace PartitionedTriangleAbsorption.BlowupB.FinT

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients

variable {t : ℕ}

section Counts

variable {V : Type*} [DecidableEq V]

def unorderedCount (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) : ℤ :=
  ((E.filter (fun e => Sym2.map p e = s(i, j))).card : ℤ)

theorem unorderedCount_nonneg (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    0 ≤ unorderedCount p E i j := by unfold unorderedCount; positivity

theorem unorderedCount_swap (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    unorderedCount p E i j = unorderedCount p E j i := by
  simp only [unorderedCount, Sym2.eq_swap]

theorem unorderedCount_sum (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    unorderedCount p E i j = ∑ e ∈ E, if Sym2.map p e = s(i, j) then (1 : ℤ) else 0 := by
  simp only [unorderedCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem count_pair_identity (a b i j : Fin t) :
    (if a = i ∧ b = j then (1 : ℤ) else 0) +
      (if b = i ∧ a = j then (1 : ℤ) else 0) =
    (if i = j then (2 : ℤ) else 1) * (if s(a, b) = s(i, j) then 1 else 0) := by
  by_cases hs : s(a, b) = s(i, j)
  · rw [if_pos hs, mul_one]
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
  · rw [if_neg hs, mul_zero]
    have h1 : ¬ (a = i ∧ b = j) := fun h => hs (by rw [h.1, h.2])
    have h2 : ¬ (b = i ∧ a = j) := fun h => hs (by rw [h.1, h.2]; exact Sym2.eq_swap)
    simp [h1, h2]

theorem edgeVec_unorderedCount (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = (if i = j then 2 else 1) * unorderedCount p E i j := by
  rw [unorderedCount_sum, mul_sum]
  simp only [edgeVec, Finset.sum_apply]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk, Sym2.map_mk]
    exact count_pair_identity (p a) (p b) i j

theorem unorderedCount_zero_of_forbidden (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t)
    (h : ∀ e ∈ E, Sym2.map p e ≠ s(i, j)) : unorderedCount p E i j = 0 := by
  have hz : E.filter (fun e => Sym2.map p e = s(i, j)) = ∅ := filter_eq_empty_iff.mpr h
  simp only [unorderedCount, hz, card_empty, Nat.cast_zero]

theorem pairVec_total (p : V → Fin t) (e : Sym2 V) : ∑ i, ∑ j, pairVec p e i j = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk, sum_add_distrib, ite_and]
    simp

theorem total_edgeVec (p : V → Fin t) (E : Finset (Sym2 V)) :
    (∑ i, ∑ j, edgeVec p E i j) = 2 * E.card := by
  simp only [edgeVec, Finset.sum_apply]
  calc ∑ i, ∑ j, ∑ e ∈ E, pairVec p e i j = ∑ i, ∑ e ∈ E, ∑ j, pairVec p e i j :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ e ∈ E, ∑ i, ∑ j, pairVec p e i j := sum_comm
    _ = ∑ _e ∈ E, (2 : ℤ) := sum_congr rfl fun e _ => pairVec_total p e
    _ = 2 * E.card := by rw [sum_const, nsmul_eq_mul]; ring

section ClassParity

variable [Fintype V]

theorem pairVec_class_sum (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    pairVec p e i j = ∑ v ∈ univ.filter (fun v => p v = i), degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, degContrib, Sym2.lift_mk, sum_add_distrib]
    rw [sum_filter, sum_filter]
    simp only [← ite_and]
    congr 1
    · rw [sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    · rw [sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp

theorem edgeVec_class_sum (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = ∑ v ∈ univ.filter (fun v => p v = i), degVec p E v j := by
  simp only [edgeVec, degVec, Finset.sum_apply]
  rw [sum_comm]
  exact sum_congr rfl fun e _ => pairVec_class_sum p e i j

theorem class_row_two_dvd (p : V → Fin t) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v, Even (incidentLoad E v)) (i : Fin t) :
    (2 : ℤ) ∣ ∑ j, edgeVec p E i j := by
  simp_rw [edgeVec_class_sum]
  rw [sum_comm]
  apply dvd_sum
  intro v hv
  rw [sum_degVec p E hloop v]
  exact_mod_cast (heven v).two_dvd

end ClassParity

end Counts

/-! ### The scalar frame -/

noncomputable def totalU (u : Fin t → Fin t → ℤ) : ℤ := ∑ i, ∑ j, if i ≤ j then u i j else 0

structure ScalarHyp (F : Finset (Multiset (Fin t))) (u : Fin t → Fin t → ℤ) : Prop where
  symm : ∀ i j, u i j = u j i
  nonneg : ∀ i j, 0 ≤ u i j
  forbid : ∀ i j, (¬ ∃ k, Link F i j k) → u i j = 0
  parity : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j
  three : (3 : ℤ) ∣ totalU u

def LatEq (F : Finset (Multiset (Fin t))) (u : Fin t → Fin t → ℤ)
    (c : Multiset (Fin t) → ℤ) : Prop :=
  ∀ i j, (if i = j then 2 else 1) * u i j = ∑ τ ∈ F, c τ * typeEdgeVec τ i j

def coeffList : List (Multiset (Fin t) × ℤ) → Multiset (Fin t) → ℤ
  | [], _ => 0
  | (s, a) :: l, τ => if τ = s then a else coeffList l τ

/-- The witness bound with an explicit size limit. -/
def WitnessBoundK (F : Finset (Multiset (Fin t))) (K B : ℕ) : Prop :=
  ∀ {W : Type} [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
    P.card ≤ K → IsIntDiv p F P → ∃ c : Multiset (Fin t) → ℤ,
      edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ negativeMass F c ≤ B

theorem typeEdgeVec_row {τ : Multiset (Fin t)} (hτ : Multiset.card τ = 3) (i : Fin t) :
    ∑ j, typeEdgeVec τ i j = 2 * (τ.count i : ℤ) := by
  have h : ∑ j : Fin t, (τ.count j : ℤ) = 3 := by
    exact_mod_cast (Multiset.sum_count_eq_card (by simp)).trans hτ
  simp only [typeEdgeVec, sum_sub_distrib, ← mul_sum, h]
  simp only [sum_ite_eq, mem_univ, if_true]
  ring

theorem row_split (u : Fin t → Fin t → ℤ) (i : Fin t) :
    ∑ j, (if i = j then (2 : ℤ) else 1) * u i j = 2 * u i i + ∑ j, if i = j then 0 else u i j := by
  have h : ∀ j, (if i = j then (2 : ℤ) else 1) * u i j =
      (if i = j then 2 * u i i else 0) + (if i = j then 0 else u i j) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [sum_congr rfl fun j _ => h j, sum_add_distrib, sum_ite_eq]
  simp

theorem weighted_total (u : Fin t → Fin t → ℤ) (hs : ∀ i j, u i j = u j i) :
    ∑ i, ∑ j, (if i = j then (2 : ℤ) else 1) * u i j = 2 * totalU u := by
  have h : ∀ i j, (if i = j then (2 : ℤ) else 1) * u i j =
      (if i ≤ j then u i j else 0) + (if j ≤ i then u i j else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp; ring
    · rcases lt_or_gt_of_ne hij with h | h
      · simp [hij, h.le, not_le.mpr h]
      · simp [hij, h.le, not_le.mpr h]
  have h2 : ∑ i, ∑ j, (if j ≤ i then u i j else 0) = totalU u := by
    unfold totalU
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hs]
  simp only [h, sum_add_distrib]
  rw [h2]
  unfold totalU
  ring

theorem scalarHyp_of_latEq {F : Finset (Multiset (Fin t))}
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) {u : Fin t → Fin t → ℤ}
    {c : Multiset (Fin t) → ℤ} (hs : ∀ i j, u i j = u j i) (hn : ∀ i j, 0 ≤ u i j)
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

section Counts2

variable {V : Type*} [DecidableEq V]

theorem link_swap12 (F : Finset (Multiset (Fin t))) (i j k : Fin t) :
    Link F i j k ↔ Link F j i k := by
  unfold Link
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.insert_eq_cons,
    Multiset.insert_eq_cons, Multiset.cons_swap]

theorem latEq_counts_iff (F : Finset (Multiset (Fin t))) (p : V → Fin t) (E : Finset (Sym2 V))
    (c : Multiset (Fin t) → ℤ) :
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

theorem counts_forbid {F : Finset (Multiset (Fin t))} {p : V → Fin t} {E : Finset (Sym2 V)}
    (hact : ActiveEdges F p E) (i j : Fin t) (hij : ¬ ∃ k, Link F i j k) :
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

theorem totalU_counts (p : V → Fin t) (E : Finset (Sym2 V)) :
    totalU (unorderedCount p E) = E.card := by
  have h := total_edgeVec p E
  simp only [edgeVec_unorderedCount] at h
  rw [weighted_total _ (unorderedCount_swap p E)] at h
  linarith

theorem counts_parity [Fintype V] (p : V → Fin t) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v, Even (incidentLoad E v)) (i : Fin t) :
    (2 : ℤ) ∣ ∑ j, if i = j then 0 else unorderedCount p E i j := by
  have h := class_row_two_dvd p E hloop heven i
  simp only [edgeVec_unorderedCount] at h
  rw [row_split] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k - unorderedCount p E i i, by linarith⟩

end Counts2

theorem witnessBound_of_scalar (F : Finset (Multiset (Fin t)))
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

theorem negativeMass_le_of_lower (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ)
    (M : ℕ) (h : ∀ τ ∈ F, -(M : ℤ) ≤ c τ) : negativeMass F c ≤ F.card * M := by
  unfold negativeMass
  calc ∑ τ ∈ F, (-c τ).toNat ≤ ∑ _τ ∈ F, M := sum_le_sum fun τ hτ => by
        have := h τ hτ; omega
    _ = F.card * M := by rw [sum_const, smul_eq_mul]

end PartitionedTriangleAbsorption.BlowupB.FinT

#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.witnessBound_of_scalar
#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.counts_parity
