/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAnchors
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CataloguePrecharge
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRoutes
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRouteLoad

@[expose] public section

/-! Construct one weighted physical path system for the entire fixed
catalogue. Anchors are chosen first; the subsequent path iteration uses
their actual endpoint charges. Neither map nor path system is a premise. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueEmbedding

open Finset Cycles AntiEdgeSelection StructuralF3General PaddedNoCommon WeightedEdgeLedger

def third (i j : Fin 3) : Fin 3 :=
  if i ≠ 0 ∧ j ≠ 0 then 0 else if i ≠ 1 ∧ j ≠ 1 then 1 else 2

theorem third_ne : ∀ i j : Fin 3, i ≠ j → i ≠ third i j ∧ j ≠ third i j := by
  decide

variable {A V : Type} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V] [Nonempty V]

theorem exists_embedding (lib : Finset (Finset (A × A)))
    (I : Finset (A × A)) (hI : I ⊆ CatalogueWeights.arcs lib)
    (pin : A → Option V) (label : A → Fin 3) (p : V → Fin 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset (Sym2 V))
    (a d T W M : ℝ) (hd : 0 ≤ d) (hT : 0 < T) (hW : 0 ≤ W)
    (hs : GuardedSupply p G (fun i j => i ≠ j) 2 a) (hX : DegBounded X d)
    (hpin : ∀ v r, pin v = some r → p r = label v)
    (hproper : ∀ e ∈ CatalogueWeights.arcs lib, label e.1 ≠ label e.2)
    (hicap : ∀ r, CatalogueAnchors.pinnedLoad pin
      (fun v => (catalogLoad lib v : ℝ)) r ≤ T)
    (hwcap : ∀ v, (catalogLoad lib v : ℝ) ≤ W)
    (hsupply : ∀ i, a ≤ (univ.filter (fun r : V => p r = i)).card)
    (hanchor : M < a * T) (hmass : (∑ v, (catalogLoad lib v : ℝ)) ≤ M)
    (hbudget : 4 * M / T + 4 + 2 * (d + T + 2 * W) < a) :
    ∃ (f : A → V) (x y z : (A × A) → V),
      (∀ v r, pin v = some r → f v = r) ∧
      (∀ v, p (f v) = label v) ∧
      (∀ e ∈ CatalogueWeights.arcs lib \ I,
        p (x e) = label e.2 ∧ p (y e) = third (label e.1) (label e.2) ∧
        p (z e) = label e.1 ∧ IsPath4 G (f e.1) (x e) (y e) (z e) (f e.2)) ∧
      (∀ e ∈ CatalogueWeights.arcs lib \ I,
        Disjoint (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) X) ∧
      (∀ e ∈ CatalogueWeights.arcs lib \ I, ∀ q ∈ CatalogueWeights.arcs lib \ I,
        e ≠ q → Disjoint (pathEdges (f e.1) (x e) (y e) (z e) (f e.2))
          (pathEdges (f q.1) (x q) (y q) (z q) (f q.2))) ∧
      (∀ r, (∑ e ∈ I, endpointCharge (CatalogueWeights.weight lib e : ℝ)
          (f e.1) (f e.2) r) +
        (∑ e ∈ CatalogueWeights.arcs lib \ I, (CatalogueWeights.weight lib e : ℝ) *
          (incidentLoad (pathEdges (f e.1) (x e) (y e) (z e) (f e.2)) r : ℝ)) ≤
        T + 2 * W) := by
  obtain ⟨f, hfix, hcolour, hcap, htotal⟩ := CatalogueAnchors.exists_anchors lib pin
    label p a T W M hT hW hpin hicap hwcap hsupply hanchor hmass
  let E := CatalogueWeights.arcs lib \ I
  let weight := fun e => (CatalogueWeights.weight lib e : ℝ)
  let initial := fun r => ∑ v, if f v = r then (catalogLoad lib v : ℝ) else 0
  let base := fun r => ∑ e ∈ I, endpointCharge (weight e) (f e.1) (f e.2) r
  have hpre : ∀ r, base r +
      (∑ e ∈ E, endpointCharge (weight e) (f e.1) (f e.2) r) ≤ initial r :=
    CataloguePrecharge.retained_endpoint_load_le lib I hI f
  have hbase : ∀ r, 0 ≤ base r := by
    intro r
    apply sum_nonneg
    intro e _
    unfold endpointCharge
    split_ifs <;> positivity
  have hpre' : ∀ r,
      (∑ e ∈ E, endpointCharge (weight e) (f e.1) (f e.2) r) ≤ initial r := by
    intro r
    linarith [hpre r, hbase r]
  have hi : ∀ r, 0 ≤ initial r := by
    intro r
    apply sum_nonneg
    intro v _
    split_ifs <;> positivity
  have hw : ∀ e ∈ E, 1 ≤ weight e ∧ weight e ≤ W := by
    intro e he
    have ha := (mem_sdiff.mp he).1
    constructor
    · change (1 : ℝ) ≤ (CatalogueWeights.weight lib e : ℝ)
      exact_mod_cast CatalogueWeights.positive lib ha
    · have hh : (CatalogueWeights.weight lib e : ℝ) ≤ (catalogLoad lib e.1 : ℝ) := by
        exact_mod_cast CatalogueWeights.weight_le_load lib ha
      exact hh.trans (hwcap e.1)
  have hwmass : 2 * (∑ e ∈ E, weight e) ≤ M := by
    have hsub : (∑ e ∈ E, weight e) ≤ ∑ e ∈ CatalogueWeights.arcs lib, weight e :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
    have htotal : (∑ v, (catalogLoad lib v : ℝ)) =
        2 * ∑ e ∈ CatalogueWeights.arcs lib, weight e := by
      dsimp [weight]
      exact_mod_cast CataloguePrecharge.total_degree lib
    linarith
  have hneq : ∀ e ∈ E, label e.1 ≠ label e.2 :=
    fun e he => hproper e (mem_sdiff.mp he).1
  obtain ⟨x, y, z, hp, ha, hdis, hpathcap, _⟩ := WeightedRoutes.exists_paths
    p G E (fun e => f e.1) (fun e => f e.2)
    (fun e => label e.1) (fun e => label e.2) (fun e => third (label e.1) (label e.2))
    weight X initial a d T W M hs hd hT hW hX hi hcap htotal hwmass hw hpre'
    (fun e _ => hcolour e.1) (fun e _ => hcolour e.2) hneq
    (fun e he => (third_ne _ _ (hneq e he)).1)
    (fun e he => (third_ne _ _ (hneq e he)).2) hbudget
  refine ⟨f, x, y, z, hfix, hcolour, hp, ha, hdis, ?_⟩
  apply WeightedRouteLoad.family_load_cap G E (fun e => f e.1) (fun e => f e.2)
    x y z weight base initial ?_ (fun e he => (hp e he).2.2.2) hpre (T + 2 * W) hpathcap
  intro e he heq
  exact hneq e he ((hcolour e.1).symm.trans ((congrArg p heq).trans (hcolour e.2)))

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueEmbedding

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueEmbedding.exists_embedding
