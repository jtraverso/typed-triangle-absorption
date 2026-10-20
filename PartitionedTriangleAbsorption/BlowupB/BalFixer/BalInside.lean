/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalSupply
public import PartitionedTriangleAbsorption.BlowupB.FinT.Lattice

@[expose] public section

/-!
# Integral divisibility for families with bipartite links

`σc r` is the side weight of the class `r` (`±1` on the two sides of its link, when the link is
bipartite); `Bc` is the set of classes with a bipartite link.

* `LocalSol F σc Bc`: at every class, a degree vector supported on the link, of even total, and (for
  `r ∈ Bc`) balanced, lies in the local lattice. It is a finite statement per family.
* `BalScalarHyp`: the scalar hypotheses of `FinT.ScalarHyp` on the class-pair counts, plus one balance
  equation per class of `Bc` (the sum of the signed degrees over the class) and a charge equation.
* `isIntDiv_of_bal`: local solution + scalar solution give `IsIntDiv` for every loopless active edge
  set inside a component, of even degrees, with `3 ∣ |E|`, signed degree `0` at every vertex of a class
  of `Bc`, and charge `0`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ}

/-- The local lattice at every class, explicitly solved. -/
def LocalSol (F : Finset (Multiset (Fin t))) (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t)) :
    Prop :=
  ∀ (r : Fin t) (d : Fin t → ℤ), (∀ j, d j ≠ 0 → ∃ l, Link F r j l) → (2 : ℤ) ∣ ∑ j, d j →
    (r ∈ Bc → ∑ j, σc r j * d j = 0) →
    ∃ c : Multiset (Fin t) → ℤ, d = ∑ τ ∈ F with r ∈ τ, c τ • typeDegVec τ r

/-- The scalar hypotheses of the counts, with the balance and charge equations. -/
def BalScalarHyp (F : Finset (Multiset (Fin t))) (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t))
    (χ : Fin t → Fin t → ℤ) (u : Fin t → Fin t → ℤ) : Prop :=
  FinT.ScalarHyp F u ∧
    (∀ r ∈ Bc, ∑ j, σc r j * ((if r = j then 2 else 1) * u r j) = 0) ∧
    ∑ i, ∑ j, χ i j * ((if i = j then 2 else 1) * u i j) = 0

section Counts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Summing the signed degrees over a class. -/
theorem sum_vcharge_class (σ : Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) (r : Fin t) :
    ∑ v ∈ univ.filter (fun v => p v = r), vcharge σ p v E =
      ∑ j, σ j * ((if r = j then 2 else 1) * FinT.unorderedCount p E r j) := by
  simp only [vcharge]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← FinT.edgeVec_unorderedCount, FinT.edgeVec_class_sum, mul_sum]

theorem charge_counts_eq (χ : Fin t → Fin t → ℤ) (p : V → Fin t) (E : Finset (Sym2 V)) :
    charge χ p E = ∑ i, ∑ j, χ i j * ((if i = j then 2 else 1) * FinT.unorderedCount p E i j) := by
  unfold charge pair
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [FinT.edgeVec_unorderedCount]

/-- The counts of a balanced edge set satisfy the balanced scalar hypotheses. -/
theorem balScalarHyp_counts {F : Finset (Multiset (Fin t))} {σc : Fin t → Fin t → ℤ}
    {Bc : Finset (Fin t)} {χ : Fin t → Fin t → ℤ} {p : V → Fin t} {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (hev : ∀ v, Even (incidentLoad E v)) (h3 : 3 ∣ E.card)
    (hbal : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) (hχ : charge χ p E = 0) :
    BalScalarHyp F σc Bc χ (FinT.unorderedCount p E) := by
  refine ⟨⟨FinT.unorderedCount_swap p E, FinT.unorderedCount_nonneg p E, FinT.counts_forbid hact,
    FinT.counts_parity p E hloop hev, by rw [FinT.totalU_counts]; exact_mod_cast h3⟩, ?_, ?_⟩
  · intro r hr
    rw [← sum_vcharge_class]
    refine sum_eq_zero fun v hv => ?_
    have hpv : p v = r := (mem_filter.mp hv).2
    have := hbal v (hpv ▸ hr)
    rwa [hpv] at this
  · rw [← charge_counts_eq]; exact hχ

/-- **Integral divisibility from the local and the scalar solutions.** -/
theorem isIntDiv_of_bal {F : Finset (Multiset (Fin t))} {σc : Fin t → Fin t → ℤ}
    {Bc : Finset (Fin t)} {χ : Fin t → Fin t → ℤ} (c : Fin t → Fin t) (k : Fin t)
    (hloc : LocalSol F σc Bc)
    (hsol : ∀ u, BalScalarHyp F σc Bc χ u → FinT.CountsInside c k u → ∃ w, FinT.LatEq F u w)
    {p : V → Fin t} {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (hin : ∀ e ∈ E, CompT.InsideE p c k e)
    (hev : ∀ v, Even (incidentLoad E v)) (h3 : 3 ∣ E.card)
    (hbal : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) (hχ : charge χ p E = 0) :
    IsIntDiv p F E := by
  obtain ⟨w, hw⟩ := hsol _ (balScalarHyp_counts hloop hact hev h3 hbal hχ)
    (FinT.countsInside_of_insideE hin)
  refine ⟨⟨w, (FinT.latEq_counts_iff F p E w).mp hw⟩, fun v => ?_⟩
  apply hloc (p v) (degVec p E v)
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := exists_of_degVec_ne_zero hj
    exact hact v b hb
  · rw [sum_degVec p E hloop v]
    obtain ⟨m, hm⟩ := hev v
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  · intro hr
    exact hbal v hr

end Counts

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.isIntDiv_of_bal
