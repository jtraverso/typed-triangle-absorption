/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.FinT.Lattice
public import PartitionedTriangleAbsorption.TypedRefinerCharge

@[expose] public section

/-!
# The charge layer of a component, for families on `Fin t`

Generic copies of `PaddedComponents.ChargeInside`, `PaddedComponents.Template` (Kappa/ComponentCharge,
Kappa/ComponentChargeTorsion), `PaddedCharge.charge_counts` and
`PaddedComponents.witnessBound_of_latEq_lowerA`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.FinT

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ}

/-- Inside component `k`, the lattice is cut out by ordinary divisibility and the charge `χ`. -/
def ChargeInside (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (χ : Fin t → Fin t → ℤ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin t) (E : Finset (Sym2 V)),
    (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F p E → (∀ e ∈ E, CompT.InsideE p c k e) →
      (∀ v, Even (incidentLoad E v)) → charge χ p E = 0 → IsIntDiv p F E

/-- A template: loopless, allowed, even, at most six edges, labels inside component `k`. -/
structure Template (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t) where
  E : Finset (Sym2 (Fin 6))
  L : Fin 6 → Fin t
  loop : ∀ e ∈ E, ¬ e.IsDiag
  act : ActiveEdges F L E
  even : ∀ w, Even (incidentLoad E w)
  card : E.card ≤ 6
  inside : ∀ w, c (L w) = k

theorem charge_counts {V : Type*} [DecidableEq V] (χ : Fin t → Fin t → ℤ) (p : V → Fin t)
    (E : Finset (Sym2 V)) :
    charge χ p E = ∑ i, ∑ j, χ i j * ((if i = j then 2 else 1) * unorderedCount p E i j) := by
  unfold charge pair
  simp only [edgeVec_unorderedCount]

theorem witnessBound_of_latEq_lowerA (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (a : Multiset (Fin t) → ℕ)
    (hsol : ∀ u c0, ScalarHyp F u → LatEq F u c0 →
      ∃ c, LatEq F u c ∧ ∀ τ ∈ F, -((a τ : ℤ) * totalU u + 4) ≤ c τ) (K : ℕ) :
    WitnessBoundK F K (∑ τ ∈ F, (a τ * K + 4)) := by
  apply witnessBound_of_latEq F hcard K
  intro u c0 hu hc0 hK
  obtain ⟨c, hc, hm⟩ := hsol u c0 hu hc0
  refine ⟨c, hc, ?_⟩
  have hT : (0 : ℤ) ≤ totalU u := by
    unfold totalU
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => by
      split_ifs
      · exact hu.nonneg i j
      · exact le_refl 0
  unfold negativeMass
  apply sum_le_sum
  intro τ hτ
  have h1 := hm τ hτ
  have hK' : (a τ : ℤ) * totalU u ≤ (a τ : ℤ) * K :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hK) (by positivity)
  omega

end PartitionedTriangleAbsorption.BlowupB.FinT

#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.charge_counts
