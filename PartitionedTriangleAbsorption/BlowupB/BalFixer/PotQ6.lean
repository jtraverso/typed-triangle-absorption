/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.PotQ

@[expose] public section

/-!
# Divisibility by six of a class-pair charge

`six_dvd_charge_of_pot`: a potential modulo `2` for `χ` and a potential modulo `3` for `χ - 1` give
`6 ∣ charge χ p E` on every loopless, active, even, balanced edge set with `3 ∣ |E|`
(`charge (χ - 1) p E = charge χ p E - 2 |E|`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem charge_sub_one (χ : Fin t → Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) :
    charge (fun i j => χ i j - 1) p E = charge χ p E - 2 * E.card := by
  rw [charge_eq_sum, charge_eq_sum, card_eq_sum_ones, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => rw [pair_pairVec_mk, pair_pairVec_mk]; push_cast; ring

/-- **Divisibility by six of a charge from two local potentials.** -/
theorem six_dvd_charge_of_pot {F : Finset (Multiset (Fin t))} (σc : Fin t → Fin t → ℤ)
    (Bc : Finset (Fin t)) (χ γ2 γ3 : Fin t → Fin t → ℤ)
    (hpair2 : ∀ i j, (∃ l, Link F i j l) → (2 : ℤ) ∣ γ2 i j + γ2 j i - (χ i j + χ j i))
    (hvert2 : ∀ (r : Fin t) (d : Fin t → ℤ), (∀ j, d j ≠ 0 → ∃ l, Link F r j l) →
      (2 : ℤ) ∣ ∑ j, d j → (r ∈ Bc → ∑ j, σc r j * d j = 0) → (2 : ℤ) ∣ ∑ j, γ2 r j * d j)
    (hpair3 : ∀ i j, (∃ l, Link F i j l) →
      (3 : ℤ) ∣ γ3 i j + γ3 j i - ((χ i j - 1) + (χ j i - 1)))
    (hvert3 : ∀ (r : Fin t) (d : Fin t → ℤ), (∀ j, d j ≠ 0 → ∃ l, Link F r j l) →
      (2 : ℤ) ∣ ∑ j, d j → (r ∈ Bc → ∑ j, σc r j * d j = 0) → (3 : ℤ) ∣ ∑ j, γ3 r j * d j)
    {p : V → Fin t} {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (hev : ∀ v, Even (incidentLoad E v))
    (hbal : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) (h3 : 3 ∣ E.card) :
    (6 : ℤ) ∣ charge χ p E := by
  have a := dvd_charge_of_pot σc Bc χ γ2 2 hpair2 hvert2 hloop hact hev hbal
  have b := dvd_charge_of_pot σc Bc (fun i j => χ i j - 1) γ3 3 hpair3 hvert3 hloop hact hev hbal
  rw [charge_sub_one] at b
  have c : (3 : ℤ) ∣ (E.card : ℤ) := by exact_mod_cast h3
  omega

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.six_dvd_charge_of_pot
