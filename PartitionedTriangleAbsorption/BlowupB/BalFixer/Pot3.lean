/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalInside

@[expose] public section

/-!
# `3 ∣ |E|` from a local potential

`three_dvd_of_pot`: let `β` be a weight on ordered class pairs with `β i j + β j i ≡ 1 (mod 3)` on every
allowed pair, and with `∑_j β r j · d j ≡ 0 (mod 3)` for every admissible local degree vector `d` at a
class `r` (supported on the link, of even total, balanced when `r ∈ Bc`). Then every loopless, active,
even edge set, balanced at the vertices of the classes of `Bc`, has `3 ∣ |E|`:
summing `∑_j β (p v) j · deg_v(j)` over the vertices counts every edge `ab` with weight
`β(a,b) + β(b,a) ≡ 1`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_beta_degContrib (β : Fin t → Fin t → ℤ) (p : V → Fin t) (a b : V) :
    ∑ v, ∑ j, β (p v) j * degContrib p v s(a, b) j = β (p a) (p b) + β (p b) (p a) := by
  have h1 : ∀ v, ∑ j, β (p v) j * degContrib p v s(a, b) j =
      (if a = v then β (p v) (p b) else 0) + (if b = v then β (p v) (p a) else 0) := by
    intro v
    simp only [degContrib, Sym2.lift_mk, mul_add, sum_add_distrib, ite_and, mul_ite, mul_one,
      mul_zero]
    congr 1
    · by_cases h : a = v
      · simp [h, sum_ite_eq']
      · simp [h]
    · by_cases h : b = v
      · simp [h, sum_ite_eq']
      · simp [h]
  rw [sum_congr rfl fun v _ => h1 v, sum_add_distrib, sum_ite_eq, sum_ite_eq]
  simp

/-- **`3 ∣ |E|` from a local potential.** -/
theorem three_dvd_of_pot {F : Finset (Multiset (Fin t))} (σc : Fin t → Fin t → ℤ)
    (Bc : Finset (Fin t)) (β : Fin t → Fin t → ℤ)
    (hpair : ∀ i j, (∃ l, Link F i j l) → (3 : ℤ) ∣ β i j + β j i - 1)
    (hvert : ∀ (r : Fin t) (d : Fin t → ℤ), (∀ j, d j ≠ 0 → ∃ l, Link F r j l) →
      (2 : ℤ) ∣ ∑ j, d j → (r ∈ Bc → ∑ j, σc r j * d j = 0) → (3 : ℤ) ∣ ∑ j, β r j * d j)
    {p : V → Fin t} {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (hev : ∀ v, Even (incidentLoad E v))
    (hbal : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) : 3 ∣ E.card := by
  -- the vertex sum
  have hV : (3 : ℤ) ∣ ∑ v, ∑ j, β (p v) j * degVec p E v j := by
    refine dvd_sum fun v _ => hvert (p v) (degVec p E v) ?_ ?_ ?_
    · intro j hj
      obtain ⟨b, hb, rfl⟩ := exists_of_degVec_ne_zero hj
      exact hact v b hb
    · rw [sum_degVec p E hloop v]
      obtain ⟨m, hm⟩ := hev v
      exact ⟨m, by rw [hm]; push_cast; ring⟩
    · intro hr
      have := hbal v hr
      unfold vcharge at this
      exact this
  -- the edge sum
  have hsw : ∑ v, ∑ j, β (p v) j * degVec p E v j =
      ∑ e ∈ E, ∑ v, ∑ j, β (p v) j * degContrib p v e j := by
    calc ∑ v, ∑ j, β (p v) j * degVec p E v j
        = ∑ v, ∑ j, ∑ e ∈ E, β (p v) j * degContrib p v e j := by
          simp only [degVec, Finset.sum_apply, mul_sum]
      _ = ∑ v, ∑ e ∈ E, ∑ j, β (p v) j * degContrib p v e j :=
          sum_congr rfl fun v _ => Finset.sum_comm
      _ = ∑ e ∈ E, ∑ v, ∑ j, β (p v) j * degContrib p v e j := Finset.sum_comm
  have hE : (3 : ℤ) ∣ ∑ e ∈ E, ((∑ v, ∑ j, β (p v) j * degContrib p v e j) - 1) := by
    refine dvd_sum fun e he => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [sum_beta_degContrib]
      obtain ⟨l, hl⟩ := hact a b he
      exact hpair (p a) (p b) ⟨l, hl⟩
  rw [sum_sub_distrib, ← hsw, sum_const, nsmul_eq_mul, mul_one] at hE
  have := dvd_sub hV hE
  simp only [sub_sub_cancel] at this
  exact_mod_cast this

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.three_dvd_of_pot
