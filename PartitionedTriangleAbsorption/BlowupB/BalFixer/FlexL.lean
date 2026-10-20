/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.TypedConsumer

@[expose] public section

/-!
# Flexible certificates at the scale `2^L`

`FlexScalesL L` is `Flex.FlexScales` with the reserve scale `(ωδ/2^48)²` replaced by `(ω²δ/2^L)²`, and
`UniversalCertFlexL F L` the corresponding family certificate. The consumers of the flexible
certificate choose the reserve density themselves, so they work verbatim at any scale `L`
(`decomposition_of_flexible_absorberL`, `keevashTypedSpec_of_flexible_absorberL`). This lets a family
certificate use constants (for instance the size of a terminal absorber) known only to exist.
-/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PaddedF12 KeevashQuantitative
open PaddedInputs
open PartitionedTriangleAbsorption.BlowupB
open PartitionedTriangleAbsorption.BlowupB.Flex
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.TypedTransformer

/-- The flexible scales at the reserve scale `2^L`. -/
structure FlexScalesL (L : ℕ) (ω δ ρ n : ℝ) : Prop where
  ω_pos : 0 < ω
  ω_le : ω ≤ 1
  δ_pos : 0 < δ
  δ_le : 2 ^ 63 * δ ≤ ω
  ρ_sq : 2 ^ 24 * ρ ≤ (ω ^ 2 * δ / 2 ^ L) ^ 2
  n_nonneg : 0 ≤ n
  ρn : 1 ≤ ρ * n

/-- The family certificate at the scale `2^L`. -/
def UniversalCertFlexL (F : Finset (Multiset (Fin 4))) (L : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω δ ρ : ℝ),
    FlexScalesL L ω δ ρ (Fintype.card V) →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    UniversalAbsorbers p F G ρ δ

/-- A proved flexible family certificate discharges the host-level universal
absorber premise. All numerical choices precede the graph and its weights. -/
theorem decomposition_of_flexible_absorberL
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (L : ℕ) (hU : UniversalCertFlexL F L) (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ ρ ε : ℝ, ∃ N : ℕ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < ε ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
          (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
          GuardedSupply p G (fun i j => ∃ k, Link F i j k)
            (2 ^ 21) (ω * Fintype.card V) →
          IsIntDiv p F G.edgeFinset →
          ∀ φ : Finset V → ℝ,
          (∀ T, IsCopy p F G T →
            ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
          (∀ e ∈ G.edgeFinset,
            |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) →
          HasDecomp p F G.edgeFinset := by
  set C := generalInverseConstant F hF.card_three
  have hC : 0 ≤ C := (generalInverseConstant_pos F hF.card_three).le
  set κ := inverseKappa C ω
  have hκ : 0 < κ := (inverse_scales_pos hC hω).1
  have hκω : κ ≤ ω / 8 := min_le_left _ _
  refine ⟨min (ω / (2 : ℝ)^63) (κ / 8), by positivity, ?_⟩
  intro δ hδ hδmax
  have hδκ : δ ≤ κ / 8 := hδmax.trans (min_le_right _ _)
  have hδω : (2 : ℝ)^63 * δ ≤ ω := by
    have hd := hδmax.trans (min_le_left _ _)
    have hd' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^63)).mp hd
    nlinarith
  set ρ := min (κ / 8) ((ω ^ 2 * δ / (2 : ℝ)^L)^2 / (2 : ℝ)^24)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρκ : ρ ≤ κ / 8 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := by linarith
  have hρsq : (2 : ℝ)^24 * ρ ≤ (ω ^ 2 * δ / (2 : ℝ)^L)^2 := by
    have hr : ρ ≤ (ω ^ 2 * δ / (2 : ℝ)^L)^2 / (2 : ℝ)^24 := min_le_right _ _
    have hr' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^24)).mp hr
    nlinarith
  set ε := min (inverseEpsilon C ω)
    (loadTolerance (min (ω / 8) (min 1 (ω^2)))) / 2
  have hmin : 0 < min (inverseEpsilon C ω)
      (loadTolerance (min (ω / 8) (min 1 (ω^2)))) :=
    lt_min (inverse_scales_pos hC hω).2 (initial_loadTolerance_pos hω)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ρ, ε, max (scaledOrder ω ρ) ⌈1 / ρ⌉₊, hρ, hρ1, hε, ?_⟩
  intro V _ _ hN p G _ hG hs hdiv φ hw hload
  have hn : scaledOrder ω ρ ≤ Fintype.card V := (le_max_left _ _).trans hN
  have hnρ : 1 ≤ ρ * (Fintype.card V : ℝ) := by
    have hn' : ⌈1 / ρ⌉₊ ≤ Fintype.card V := (le_max_right _ _).trans hN
    have hh : 1 / ρ ≤ (Fintype.card V : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn')
    have hh' := (div_le_iff₀ hρ).mp hh
    nlinarith
  have hsc : FlexScalesL L ω δ ρ (Fintype.card V) :=
    ⟨hω, hω1, hδ, hδω, hρsq, Nat.cast_nonneg _, hnρ⟩
  have hnum : ScaledNumericInputs (Fintype.card V) C ω ε ρ δ :=
    scaled_numeric_inputs_of_order C ω ε ρ δ hC hω hω1 hε.le hρ hρ1
      (by dsimp [ε]; linarith) (by linarith) _ hn
  exact decomposition_general F hF ω ε ρ δ V hnum p G
    (hU V p G ω δ ρ hsc hG hs) hG (hs.mono (by norm_num) le_rfl)
    hdiv φ hw hload


theorem keevashTypedSpec_of_flexible_absorberL
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (L : ℕ) (hU : UniversalCertFlexL F L) : KeevashTypedSpec F := by
  intro γ _hγ
  refine ⟨2^21, 1, by norm_num, ?_⟩
  intro ω hω hω1
  obtain ⟨δ₀, hδ₀, hall⟩ := decomposition_of_flexible_absorberL F hF L hU ω hω hω1
  obtain ⟨ρ, ε, N, _hρ, _hρ1, hε, hdec⟩ := hall δ₀ hδ₀ le_rfl
  refine ⟨ε, hε, N, ?_⟩
  intro V _ _ p J hN _hclasses hloop hallowed hreg hcn hdiv
  classical
  letI : Fintype (edgeGraph J).edgeSet := (edgeGraph J).fintypeEdgeSet
  have hJ : (edgeGraph J).edgeFinset = J := edgeGraph_edges J hloop
  have hs : GuardedSupply p (edgeGraph J) (fun i j => ∃ k, Link F i j k)
      (2^21) (ω * Fintype.card V) := by
    intro S hS i hguard
    have hc := hcn S S i hS (Subset.refl _) (fun u hu =>
      (allowedPair_iff_link F _ _).mpr (hguard u hu))
    refine hc.trans ?_
    exact_mod_cast card_le_card (show
      (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ S, s(a,v) ∈ J) ⊆
        guardedNeighbours p (edgeGraph J) S i from by
      intro v hv
      obtain ⟨_, hvi, hvS, hvadj⟩ := mem_filter.mp hv
      refine mem_filter.mpr ⟨mem_univ _, hvi, ?_⟩
      intro a ha
      change s(a,v) ∈ J ∧ a ≠ v
      exact ⟨hvadj a ha, fun hav => hvS (hav ▸ ha)⟩)
  obtain ⟨φ, hw, hload⟩ := hreg
  have hweights : ∀ T, IsCopy p F (edgeGraph J) T →
      ω^2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27/ω) / Fintype.card V := by
    intro T hT
    have ht := hw T (PaddedNibble.TypedNibble.isTypedTri_of_isCopy hT)
      (by simpa only [hJ] using PaddedNibble.TypedNibble.triEdges_subset_of_isCopy hT)
    constructor
    · exact (div_le_div_of_nonneg_right
        (pow_le_of_le_one hω.le hω1 (by norm_num : (2:ℕ) ≠ 0))
        (Nat.cast_nonneg _)).trans ht.1
    · refine ht.2.trans ?_
      rw [div_div]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hloads : ∀ e ∈ (edgeGraph J).edgeFinset,
      |(∑ T ∈ copies p F (edgeGraph J) with e ∈ triEdges T, φ T) - 1| ≤ ε := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : (edgeGraph J).Adj u v :=
        (edgeGraph J).mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
      rw [sum_copies_through p F (edgeGraph J) φ huv, hJ]
      exact hload u v (hJ ▸ he)
  have result := hdec V hN p (edgeGraph J) (edgeGraph_allowed p F J hallowed)
    hs (by simpa only [hJ] using hdiv) φ hweights hloads
  simpa only [hJ] using result


end PaddedGeneral.RealInverse

#print axioms PaddedGeneral.RealInverse.keevashTypedSpec_of_flexible_absorberL
