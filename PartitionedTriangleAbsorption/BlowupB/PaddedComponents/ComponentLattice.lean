/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ComponentEven3
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.LatticeFrame

@[expose] public section

/-!
# Scalar form of the componentwise lattice conditions

* `even3Inside_of_scalar`: a scalar solution for class-pair counts supported inside component
  `k` gives `Even3Inside F c k`.
* `witnessBound_of_latEq`: the explicit witness bound may use a given integral witness `c₀`
  (and not only ordinary divisibility); this is the form needed for disconnected families,
  whose lattice is smaller than ordinary divisibility.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- Class-pair counts supported inside component `k`. -/
def CountsInside (c : Fin 4 → Fin 4) (k : Fin 4) (u : Fin 4 → Fin 4 → ℤ) : Prop :=
  ∀ i j, (c i ≠ k ∨ c j ≠ k) → u i j = 0

theorem countsInside_of_insideE {V : Type*} [DecidableEq V] {p : V → Fin 4} {c : Fin 4 → Fin 4}
    {k : Fin 4} {E : Finset (Sym2 V)} (hin : ∀ e ∈ E, InsideE p c k e) :
    CountsInside c k (unorderedCount p E) := by
  intro i j hij
  apply unorderedCount_zero_of_forbidden
  intro e he hmap
  have h := hin e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [insideE_mk] at h
    simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hij with hi | hj
      · exact hi (ha ▸ h.1)
      · exact hj (hb ▸ h.2)
    · rcases hij with hi | hj
      · exact hi (hb ▸ h.2)
      · exact hj (ha ▸ h.1)

/-- **`Even3Inside` from a scalar solution.** -/
theorem even3Inside_of_scalar (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) (k : Fin 4)
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

/-- **Witness bound from a given integral witness.** -/
theorem witnessBound_of_latEq (F : Finset (Multiset (Fin 4)))
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

/-- The witness bound with coefficients at least `-(2 e + 4)`. -/
theorem witnessBound_of_latEq_lower (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hsol : ∀ u c0, ScalarHyp F u → LatEq F u c0 →
      ∃ c, LatEq F u c ∧ ∀ τ ∈ F, -(2 * totalU u + 4) ≤ c τ) (K : ℕ) :
    WitnessBoundK F K (F.card * (2 * K + 4)) := by
  apply witnessBound_of_latEq F hcard K
  intro u c0 hu hc0 hK
  obtain ⟨c, hc, hm⟩ := hsol u c0 hu hc0
  refine ⟨c, hc, negativeMass_le_of_lower F c _ fun τ hτ => ?_⟩
  have := hm τ hτ
  push_cast
  omega

end PaddedComponents

#print axioms PaddedComponents.even3Inside_of_scalar
#print axioms PaddedComponents.witnessBound_of_latEq_lower
