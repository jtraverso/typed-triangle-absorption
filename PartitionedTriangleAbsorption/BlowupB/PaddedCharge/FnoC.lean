/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Lattice
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.FiniteTemplates

@[expose] public section

/-!
# The family `FnoC` and its one-charge lattice

`FnoC = {001, 002, 011, 022, 113, 133}`. Allowed pairs: `00 01 02 11 13 22 33`. Its type matrix
has rank 6 in the 7 allowed coordinates. The charge is

  `χ(i,i) = 2`, `χ(i,j) = -1` (`i ≠ j`),

so on an edge set with class-pair counts `u` it is `4 · (internal edges) - 2 · (crossing edges)`.

* `chargeLattice_FnoC`: for loopless `E`, `IsIntDiv FnoC E ↔ active ∧ even degrees ∧ charge = 0`.
  There is NO torsion (the integral witness is unique and given by explicit formulas), and
  `3 ∣ |E|` is implied by `charge = 0` (`e = 3 · internal`).
* `twelve_dvd_FnoC`: on active loopless `Even3` sets the charge is a multiple of `12`.
* `witnessBound_FnoC K`: every coefficient of every integral witness is `≥ -e`, so the negative
  mass is at most `6 K` for pieces of at most `K` edges (uniform in `m`).
* The two fixed token templates of `PaddedF12` (triangle in class `0`, six-cycle alternating
  between classes `0` and `2`) are active for `FnoC` and have charges `+12` and `-12`.
-/

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- Target family A: `{001, 002, 011, 022, 113, 133}`. -/
noncomputable def FnoC : Finset (Multiset (Fin 4)) :=
  {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}}

/-- The charge of `FnoC`: `2` on the diagonal, `-1` off the diagonal. -/
def chiNoC : Fin 4 → Fin 4 → ℤ := fun i j => if i = j then 2 else -1

/-- A family has a single integral charge `χ` and no torsion: integral divisibility of a loopless
edge set is "allowed support, even degrees, zero charge". -/
def ChargeLattice (F : Finset (Multiset (Fin 4))) (χ : Fin 4 → Fin 4 → ℤ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V)),
    (∀ e ∈ E, ¬ e.IsDiag) →
    (IsIntDiv p F E ↔ ActiveEdges F p E ∧ (∀ v, Even (incidentLoad E v)) ∧ charge χ p E = 0)

theorem baseFacts_FnoC : BaseFacts FnoC where
  card := by unfold FnoC; decide
  three := by unfold ThreeStepLinks Link FnoC; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnoC; decide
  facts := ⟨by unfold FnoC; decide, by unfold Link FnoC; decide,
    by intro i; fin_cases i <;> (unfold Link FnoC; decide)⟩

/-- `FnoC` has no common neighbour class for some pair of classes. -/
theorem not_common_FnoC :
    ¬ ∀ a b : Fin 4, ∃ c, (∃ k, Link FnoC a c k) ∧ (∃ k, Link FnoC b c k) := by
  unfold Link FnoC; decide

theorem chiNoC_bound : ∀ i j, |chiNoC i j| ≤ 2 := by
  intro i j; unfold chiNoC; split_ifs <;> norm_num

theorem kills_FnoC : Kills chiNoC FnoC := by
  unfold Kills pair FnoC chiNoC; decide

theorem plus_active_FnoC : ActiveEdges FnoC plusLabel triangleSlots := by
  unfold ActiveEdges Link; decide
theorem minus_active_FnoC : ActiveEdges FnoC minusLabel cycleSlots := by
  unfold ActiveEdges Link; decide
theorem plus_charge_FnoC : charge chiNoC plusLabel triangleSlots = 12 := by decide
theorem minus_charge_FnoC : charge chiNoC minusLabel cycleSlots = -12 := by decide

section Counts

variable {V : Type*} [DecidableEq V]

theorem charge_counts (χ : Fin 4 → Fin 4 → ℤ) (p : V → Fin 4) (E : Finset (Sym2 V)) :
    charge χ p E = ∑ i, ∑ j, χ i j * ((if i = j then 2 else 1) * unorderedCount p E i j) := by
  unfold charge pair
  simp only [edgeVec_unorderedCount]

end Counts

set_option maxHeartbeats 4000000 in
/-- The explicit (unique) integral witness of `FnoC`. -/
theorem scalar_FnoC (u : Fin 4 → Fin 4 → ℤ) (hs : ∀ i j, u i j = u j i)
    (hf : ∀ i j, (¬ ∃ k, Link FnoC i j k) → u i j = 0)
    (hp : ∀ i, (2 : ℤ) ∣ ∑ j, if i = j then 0 else u i j)
    (hc : ∑ i, ∑ j, chiNoC i j * ((if i = j then 2 else 1) * u i j) = 0) :
    ∃ c, LatEq FnoC u c := by
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnoC; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnoC; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FnoC; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  simp only [Fin.sum_univ_four, chiNoC, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hc
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  refine ⟨coeffList [({0,0,1}, u 0 1 / 2 - u 1 1 + u 1 3 / 2 - u 3 3),
    ({0,0,2}, u 0 2 / 2 - u 2 2),
    ({0,1,1}, u 1 1 - u 1 3 / 2 + u 3 3),
    ({0,2,2}, u 2 2),
    ({1,1,3}, u 1 3 / 2 - u 3 3),
    ({1,3,3}, u 3 3)], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FnoC, coeffList, typeEdgeVec, sum_insert] <;> omega

set_option maxHeartbeats 4000000 in
/-- Every integral `FnoC`-witness of nonnegative counts has all coefficients `≥ -e`. -/
theorem lower_FnoC (u : Fin 4 → Fin 4 → ℤ) (c : Multiset (Fin 4) → ℤ)
    (hs : ∀ i j, u i j = u j i) (hn : ∀ i j, 0 ≤ u i j) (h : LatEq FnoC u c) :
    ∀ τ ∈ FnoC, -(totalU u) ≤ c τ := by
  have e01 := h 0 1; have e02 := h 0 2; have e11 := h 1 1
  have e13 := h 1 3; have e22 := h 2 2; have e33 := h 3 3
  simp (config := {decide := true}) [FnoC, typeEdgeVec, sum_insert] at e01 e02 e11 e13 e22 e33
  unfold totalU
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3
  have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2
  have n23 := hn 2 3; have n33 := hn 3 3
  intro τ hτ
  simp only [FnoC, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Multiset.insert_eq_cons] at e01 e02 e11 e13 e22 e33 ⊢ <;> omega

/-- **The lattice of `FnoC`: one charge, no torsion.** -/
theorem chargeLattice_FnoC : ChargeLattice FnoC chiNoC := by
  intro V _ _ p E hloop
  constructor
  · intro h
    exact ⟨active_of_isIntDiv baseFacts_FnoC.card h, even_of_isIntDiv baseFacts_FnoC.card hloop h,
      charge_eq_zero_of_isIntDiv kills_FnoC h⟩
  · rintro ⟨hact, hev, hch⟩
    rw [isIntDiv_iff baseFacts_FnoC.three baseFacts_FnoC.card hloop]
    refine ⟨hact, hev, ?_⟩
    rw [charge_counts] at hch
    obtain ⟨c, hc⟩ := scalar_FnoC (unorderedCount p E) (unorderedCount_swap p E)
      (counts_forbid hact) (counts_parity p E hloop hev) hch
    exact ⟨c, (latEq_counts_iff FnoC p E c).mp hc⟩

set_option maxHeartbeats 4000000 in
/-- **The charge of an active loopless `Even3` set is a multiple of `12`.** -/
theorem twelve_dvd_FnoC {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (A : Finset (Sym2 V)) (hloop : ∀ e ∈ A, ¬ e.IsDiag) (hact : ActiveEdges FnoC p A)
    (h3 : OnePart.Even3 A) : (12 : ℤ) ∣ charge chiNoC p A := by
  rw [charge_counts]
  have hs := unorderedCount_swap p A
  have hf := counts_forbid (F := FnoC) hact
  have hp := counts_parity p A hloop h3.2
  have ht : (3 : ℤ) ∣ totalU (unorderedCount p A) := by
    rw [totalU_counts]; exact_mod_cast h3.1
  generalize unorderedCount p A = u at hs hf hp ht ⊢
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FnoC; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FnoC; decide)
  have z23 : u 2 3 = 0 := hf 2 3 (by unfold Link FnoC; decide)
  have p0 := hp 0
  have p1 := hp 1
  have p2 := hp 2
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p0 p1 p2 p3
  unfold totalU at ht
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at ht
  simp only [Fin.sum_univ_four, chiNoC, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  omega

/-- A lower bound `-(totalU u)` on every witness coefficient gives a witness bound. -/
theorem witnessBound_of_lower (F : Finset (Multiset (Fin 4)))
    (K : ℕ)
    (hlow : ∀ u c, (∀ i j, u i j = u j i) → (∀ i j, 0 ≤ u i j) → LatEq F u c →
      ∀ τ ∈ F, -(totalU u) ≤ c τ) :
    WitnessBoundK F K (F.card * K) := by
  intro W _ p P hK hdiv
  obtain ⟨c0, hc0⟩ := hdiv.1
  have hl := hlow _ c0 (unorderedCount_swap p P) (unorderedCount_nonneg p P)
    ((latEq_counts_iff F p P c0).mpr hc0)
  rw [totalU_counts] at hl
  refine ⟨c0, hc0, negativeMass_le_of_lower F c0 K fun τ hτ => ?_⟩
  have := hl τ hτ
  have hK' : (P.card : ℤ) ≤ K := by exact_mod_cast hK
  omega

theorem card_FnoC : FnoC.card = 6 := by unfold FnoC; decide

/-- **Explicit witness bound for `FnoC`**: negative mass `≤ 6 K` for pieces of `≤ K` edges. -/
theorem witnessBound_FnoC (K : ℕ) : WitnessBoundK FnoC K (6 * K) := by
  have h : WitnessBoundK FnoC K (FnoC.card * K) := witnessBound_of_lower FnoC K lower_FnoC
  rwa [card_FnoC] at h

end PaddedCharge

#print axioms PaddedCharge.chargeLattice_FnoC
#print axioms PaddedCharge.twelve_dvd_FnoC
#print axioms PaddedCharge.witnessBound_FnoC
#print axioms PaddedCharge.kills_FnoC
