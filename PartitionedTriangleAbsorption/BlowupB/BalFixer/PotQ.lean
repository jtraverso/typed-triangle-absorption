/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.Pot3

@[expose] public section

/-!
# Divisibility of a class-pair charge from a local potential

`dvd_charge_of_pot`: let `χ` be a class-pair charge and `γ` a weight on ordered class pairs with
`γ i j + γ j i ≡ χ i j + χ j i (mod q)` on every allowed pair, and `∑_j γ r j · d j ≡ 0 (mod q)` for every
admissible local degree vector `d` at a class `r`. Then every loopless, active, even edge set, balanced
at the vertices of the classes of `Bc`, has `q ∣ charge χ p E`: both `charge χ p E` and the vertex sum
`∑_v ∑_j γ (p v) j · deg_v(j)` are sums over the edges, of values congruent modulo `q`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- **Divisibility of a charge from a local potential.** -/
theorem dvd_charge_of_pot {F : Finset (Multiset (Fin t))} (σc : Fin t → Fin t → ℤ)
    (Bc : Finset (Fin t)) (χ γ : Fin t → Fin t → ℤ) (q : ℤ)
    (hpair : ∀ i j, (∃ l, Link F i j l) → q ∣ γ i j + γ j i - (χ i j + χ j i))
    (hvert : ∀ (r : Fin t) (d : Fin t → ℤ), (∀ j, d j ≠ 0 → ∃ l, Link F r j l) →
      (2 : ℤ) ∣ ∑ j, d j → (r ∈ Bc → ∑ j, σc r j * d j = 0) → q ∣ ∑ j, γ r j * d j)
    {p : V → Fin t} {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (hev : ∀ v, Even (incidentLoad E v))
    (hbal : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) : q ∣ charge χ p E := by
  have hV : q ∣ ∑ v, ∑ j, γ (p v) j * degVec p E v j := by
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
  have hsw : ∑ v, ∑ j, γ (p v) j * degVec p E v j =
      ∑ e ∈ E, ∑ v, ∑ j, γ (p v) j * degContrib p v e j := by
    calc ∑ v, ∑ j, γ (p v) j * degVec p E v j
        = ∑ v, ∑ j, ∑ e ∈ E, γ (p v) j * degContrib p v e j := by
          simp only [degVec, Finset.sum_apply, mul_sum]
      _ = ∑ v, ∑ e ∈ E, ∑ j, γ (p v) j * degContrib p v e j :=
          sum_congr rfl fun v _ => Finset.sum_comm
      _ = ∑ e ∈ E, ∑ v, ∑ j, γ (p v) j * degContrib p v e j := Finset.sum_comm
  have hE : q ∣ ∑ e ∈ E, ((∑ v, ∑ j, γ (p v) j * degContrib p v e j) - pair χ (pairVec p e)) := by
    refine dvd_sum fun e he => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [sum_beta_degContrib, pair_pairVec_mk]
      obtain ⟨l, hl⟩ := hact a b he
      exact hpair (p a) (p b) ⟨l, hl⟩
  rw [sum_sub_distrib, ← hsw, ← charge_eq_sum] at hE
  have := dvd_sub hV hE
  simpa using this

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.dvd_charge_of_pot
