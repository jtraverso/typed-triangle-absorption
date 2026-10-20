/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalInside

@[expose] public section

/-!
# Balanced pieces with a torsion congruence

For the components whose balanced lattice has torsion over the type lattice `Λ`, a class-pair weight
`ψ` with `D ∣ ψ(τ)` for every type (`KillsMod`) detects the torsion: `D ∣ charge ψ p E` holds for
every integrally divisible `E` (`dvd_charge_of_isIntDiv`), and a balanced piece with `D ∣ charge ψ p E`
is integrally divisible as soon as the congruence cuts the balanced lattice down to `Λ`
(`isIntDiv_of_bal_dvd`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ}

/-- `D` divides the `ψ`-weight of every type of `F`. -/
def KillsMod (D : ℤ) (ψ : Fin t → Fin t → ℤ) (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ τ ∈ F, D ∣ pair ψ (typeEdgeVec τ)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every integrally divisible edge set has `D ∣ charge ψ`. -/
theorem dvd_charge_of_isIntDiv {D : ℤ} {ψ : Fin t → Fin t → ℤ} {F : Finset (Multiset (Fin t))}
    (hψ : KillsMod D ψ F) {p : V → Fin t} {E : Finset (Sym2 V)} (h : IsIntDiv p F E) :
    D ∣ charge ψ p E := by
  obtain ⟨⟨c, hc⟩, -⟩ := h
  rw [charge, hc, pair_sum]
  exact dvd_sum fun τ hτ => by rw [pair_zsmul]; exact dvd_mul_of_dvd_right (hψ τ hτ) _

/-- **Integral divisibility of a balanced piece with the torsion congruence.** -/
theorem isIntDiv_of_bal_dvd {F : Finset (Multiset (Fin t))} {σc : Fin t → Fin t → ℤ}
    {Bc : Finset (Fin t)} (c : Fin t → Fin t) (k : Fin t)
    (hloc : LocalSol F σc Bc) (ψ : Fin t → Fin t → ℤ) (D : ℤ)
    (hsol : ∀ u, BalScalarHyp F σc Bc (fun _ _ => 0) u →
      D ∣ ∑ i, ∑ j, ψ i j * ((if i = j then 2 else 1) * u i j) →
      FinT.CountsInside c k u → ∃ w, FinT.LatEq F u w)
    {p : V → Fin t} {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (hin : ∀ e ∈ E, CompT.InsideE p c k e)
    (hev : ∀ v, Even (incidentLoad E v)) (h3 : 3 ∣ E.card)
    (hbal : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) (hD : D ∣ charge ψ p E) :
    IsIntDiv p F E := by
  obtain ⟨w, hw⟩ := hsol _
    (balScalarHyp_counts (χ := fun _ _ => 0) hloop hact hev h3 hbal (by simp [charge, pair]))
    (by rw [← charge_counts_eq]; exact hD) (FinT.countsInside_of_insideE hin)
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

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.dvd_charge_of_isIntDiv
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.isIntDiv_of_bal_dvd
