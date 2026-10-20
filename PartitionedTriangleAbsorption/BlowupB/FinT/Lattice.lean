/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.FinT.Counts
public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.ComponentsT
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Collapse

@[expose] public section

/-!
# Componentwise lattice conditions for families on `Fin t`

Generic copies of `PaddedComponents.{LocalWalk4, Even3Inside, CountsInside, even3Inside_of_scalar,
witnessBound_of_latEq, witnessBound_of_latEq_lowerK}` and of `even3Inside_of_scalar_five`
(`Kappa/Components`), over the generic component layer `VertexSplit.CompT`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.FinT

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ}

/-- Paths of length four between any two classes of component `k`. -/
def LocalWalk (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t) : Prop :=
  ∀ a b, c a = k → c b = k → ∃ c1 c2 c3, (∃ l, Link F a c1 l) ∧ (∃ l, Link F c2 c1 l) ∧
    (∃ l, Link F c2 c3 l) ∧ (∃ l, Link F b c3 l)

/-- Inside component `k` the lattice is trivial. -/
def Even3Inside (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t) : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
    (∀ e ∈ P, ¬ e.IsDiag) → ActiveEdges F p P → (∀ e ∈ P, CompT.InsideE p c k e) →
      OnePart.Even3 P → IsIntDiv p F P

/-- Class-pair counts supported inside component `k`. -/
def CountsInside (c : Fin t → Fin t) (k : Fin t) (u : Fin t → Fin t → ℤ) : Prop :=
  ∀ i j, (c i ≠ k ∨ c j ≠ k) → u i j = 0

theorem countsInside_of_insideE {V : Type*} [DecidableEq V] {p : V → Fin t} {c : Fin t → Fin t}
    {k : Fin t} {E : Finset (Sym2 V)} (hin : ∀ e ∈ E, CompT.InsideE p c k e) :
    CountsInside c k (unorderedCount p E) := by
  intro i j hij
  apply unorderedCount_zero_of_forbidden
  intro e he hmap
  have h := hin e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [CompT.insideE_mk] at h
    simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hij with hi | hj
      · exact hi (ha ▸ h.1)
      · exact hj (hb ▸ h.2)
    · rcases hij with hi | hj
      · exact hi (hb ▸ h.2)
      · exact hj (ha ▸ h.1)

/-- **`Even3Inside` from a scalar solution** (`ThreeStepLinks`). -/
theorem even3Inside_of_scalar (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (hthree : ThreeStepLinks F) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u, ScalarHyp F u → CountsInside c k u → ∃ w, LatEq F u w) :
    Even3Inside F c k := by
  intro W _ _ p P hloop hact hin hE3
  obtain ⟨h3, hev⟩ := hE3
  rw [isIntDiv_iff hthree hcard hloop]
  refine ⟨hact, hev, ?_⟩
  have hS : ScalarHyp F (unorderedCount p P) :=
    ⟨unorderedCount_swap p P, unorderedCount_nonneg p P, counts_forbid hact,
      counts_parity p P hloop hev, by rw [totalU_counts]; exact_mod_cast h3⟩
  obtain ⟨w, hw⟩ := hsol _ hS (countsInside_of_insideE hin)
  exact ⟨w, (latEq_counts_iff F p P w).mp hw⟩

/-- **`Even3Inside` from a scalar solution** (`FiveStepLinks`). -/
theorem even3Inside_of_scalar_five (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (hthree : FiveStepLinks F)
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u, ScalarHyp F u → CountsInside c k u → ∃ w, LatEq F u w) :
    Even3Inside F c k := by
  intro W _ _ p P hloop hact hin hE3
  obtain ⟨h3, hev⟩ := hE3
  rw [isIntDiv_iff_five hthree hcard hloop]
  refine ⟨hact, hev, ?_⟩
  have hS : ScalarHyp F (unorderedCount p P) :=
    ⟨unorderedCount_swap p P, unorderedCount_nonneg p P, counts_forbid hact,
      counts_parity p P hloop hev, by rw [totalU_counts]; exact_mod_cast h3⟩
  obtain ⟨w, hw⟩ := hsol _ hS (countsInside_of_insideE hin)
  exact ⟨w, (latEq_counts_iff F p P w).mp hw⟩

/-- **Witness bound from a given integral witness.** -/
theorem witnessBound_of_latEq (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (K B : ℕ)
    (hsol : ∀ u c0, ScalarHyp F u → LatEq F u c0 → totalU u ≤ K →
      ∃ c, LatEq F u c ∧ negativeMass F c ≤ B) :
    WitnessBoundK F K B := by
  intro W _ p P hK hdiv
  obtain ⟨c0, hc0⟩ := hdiv.1
  have hact := active_of_isIntDiv hcard hdiv
  have hL : LatEq F (unorderedCount p P) c0 := (latEq_counts_iff F p P c0).mpr hc0
  have hS : ScalarHyp F (unorderedCount p P) :=
    scalarHyp_of_latEq hcard (unorderedCount_swap p P) (unorderedCount_nonneg p P)
      (counts_forbid hact) hL
  obtain ⟨c, hc, hm⟩ := hsol _ c0 hS hL (by rw [totalU_counts]; exact_mod_cast hK)
  exact ⟨c, (latEq_counts_iff F p P c).mp hc, hm⟩

theorem witnessBound_of_latEq_lowerK (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (K0 : ℕ)
    (hsol : ∀ u c0, ScalarHyp F u → LatEq F u c0 →
      ∃ c, LatEq F u c ∧ ∀ τ ∈ F, -((K0 : ℤ) * totalU u + 4) ≤ c τ) (K : ℕ) :
    WitnessBoundK F K (F.card * (K0 * K + 4)) := by
  apply witnessBound_of_latEq F hcard K
  intro u c0 hu hc0 hK
  obtain ⟨c, hc, hm⟩ := hsol u c0 hu hc0
  refine ⟨c, hc, negativeMass_le_of_lower F c _ fun τ hτ => ?_⟩
  have := hm τ hτ
  have hT : (0 : ℤ) ≤ totalU u := by
    unfold totalU
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => by
      split_ifs
      · exact hu.nonneg i j
      · exact le_refl 0
  push_cast
  nlinarith

end PartitionedTriangleAbsorption.BlowupB.FinT

#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.even3Inside_of_scalar
#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.even3Inside_of_scalar_five
#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.witnessBound_of_latEq_lowerK
