/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.FinT.BudgetKappa
public import PartitionedTriangleAbsorption.BlowupB.Flex.Component

@[expose] public section

set_option exponentiation.threshold 512

/-!
# Flexible component certificates for families on `Fin t`

`ComponentUniversalCertFlexT F c k`: the statement of `Flex.ComponentUniversalCertFlex` for a family on
`Fin t` (component layer `VertexSplit.CompT`). The two walk certificates (`ThreeStepLinks`,
`KappaLinks`) are the `Fin t` copies of `Flex.componentUniversalCert_of_even3_walk(_kappa)_flex`,
on top of the `Fin t` budgets `FinT.component_budget_walk(_kappa)`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.FinT

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.VertexSplit
open PaddedF12 PaddedGeneral

variable {t : ℕ}

/-- Componentwise universal certificate at flexible scales, for a family on `Fin t`. -/
def ComponentUniversalCertFlexT (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω δ ρ : ℝ),
    Flex.FlexScales ω δ ρ (Fintype.card V) →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
      DegBounded X (2 * ρ * Fintype.card V) → (∀ e ∈ X, CompT.InsideE p c k e) →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, CompT.InsideE p c k e) ∧
        HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)

theorem hasDecomp_empty_t {V : Type*} [DecidableEq V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) : HasDecomp p F (∅ : Finset (Sym2 V)) :=
  ⟨∅, fun s hs => absurd hs (by simp), by simp, by simp⟩

/-- An empty component has the trivial flexible certificate. -/
theorem componentUniversalCertFlexT_empty (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t)
    (k : Fin t) (hk : ∀ i, c i ≠ k) : ComponentUniversalCertFlexT F c k := by
  intro V _ _ p G _ ω δ ρ hfl _ _ X _ _ hXin
  have hX : X = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro e he
    have h := hXin e he
    induction e using Sym2.ind with
    | _ a b => exact hk _ ((CompT.insideE_mk p c k a b).mp h).1
  subst hX
  refine ⟨∅, empty_subset _, disjoint_empty_left _, by simp, hasDecomp_empty_t p F, ?_, ?_⟩
  · intro v
    simp only [filter_empty, card_empty, Nat.cast_zero]
    have : 0 ≤ δ := hfl.δ_pos.le
    positivity
  · intro L hL _
    have : L = ∅ := subset_empty.mp hL
    subst this
    simpa using hasDecomp_empty_t p F

variable {V : Type} [Fintype V] [DecidableEq V]

theorem componentCertFlexT_of_even3_walk (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t)
    (k : Fin t) (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hthree : ThreeStepLinks F) (hwalk : FinT.LocalWalk F c k) (hlat : FinT.Even3Inside F c k)
    (B : ℕ) (hB : FinT.WitnessBoundK F 168 B)
    (hord : terminalOrder 168 B t ≤ 2 ^ 21) (hsize : terminalSize 168 B ≤ 2 ^ 21) :
    ComponentUniversalCertFlexT F c k := by
  intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hX hXin
  have hω := hfl.ω_pos
  have hω1 := hfl.ω_le
  have hn := hfl.ρn
  by_cases hempty : ∀ i, c i ≠ k
  · exact componentUniversalCertFlexT_empty F c k hempty V p G ω δ ρ hfl hG hs X hXG hX hXin
  push Not at hempty
  obtain ⟨i0, hi0⟩ := hempty
  obtain ⟨hlam, hlam64, hrho, hscale, hn2, hδ0, hQ, hpathB, hembed, hfixed, hledgerB, hrootB,
    hcountB⟩ := Flex.walk_scales_flex ω (Fintype.card V) δ ρ
      (ω * δ / 2 ^ 40) (δ * Fintype.card V / 2 ^ 25) hfl rfl rfl
  have hW : 64 * (ω * δ / 2 ^ 40) * Fintype.card V ≤
      (Fintype.card {v // c (p v) = k} : ℝ) := by
    have hcl := hs.class_card i0
    have hsub : (univ.filter fun w => p w = i0).card ≤ Fintype.card {v // c (p v) = k} := by
      rw [Fintype.card_subtype]
      exact card_le_card (fun w hw => mem_filter.mpr ⟨mem_univ _,
        by rw [(mem_filter.mp hw).2]; exact hi0⟩)
    have hsubR : ((univ.filter fun w => p w = i0).card : ℝ) ≤
        (Fintype.card {v // c (p v) = k} : ℝ) := by exact_mod_cast hsub
    have hd1 : δ ≤ 1 := hfl.δ_le_one
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hδ0' : 0 ≤ δ := hδ0.le
    have h1 : 64 * (ω * δ / 2 ^ 40) ≤ ω := by
      have : ω * δ ≤ ω := mul_le_of_le_one_right hω.le hd1
      have : (0 : ℝ) ≤ ω * δ := by positivity
      nlinarith
    nlinarith
  exact component_budget_walk F c k hc hcard hthree hwalk hlat B hB hord hsize p G ω
    (ω * δ / 2 ^ 40) (ρ) (δ)
    (δ * Fintype.card V / 2 ^ 25) hG hs hlam hlam64 hrho hscale hn hn2 hδ0 hQ hW
    hpathB hembed hfixed hledgerB hrootB hcountB X hXG hX hXin

theorem componentCertFlexT_of_even3_walk_kappa (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t)
    (k : Fin t) (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F) (hwalk : FinT.LocalWalk F c k) (hlat : FinT.Even3Inside F c k)
    (B : ℕ) (hB : FinT.WitnessBoundK F 168 B)
    (hord : terminalOrder 168 B t ≤ 2 ^ 21) (hsize : terminalSize 168 B ≤ 2 ^ 21) :
    ComponentUniversalCertFlexT F c k := by
  intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hX hXin
  have hω := hfl.ω_pos
  have hω1 := hfl.ω_le
  have hn := hfl.ρn
  by_cases hempty : ∀ i, c i ≠ k
  · exact componentUniversalCertFlexT_empty F c k hempty V p G ω δ ρ hfl hG hs X hXG hX hXin
  push Not at hempty
  obtain ⟨i0, hi0⟩ := hempty
  obtain ⟨hlam, hlam64, hrho, hscale, hn2, hδ0, hQ, hpathB, hembed, hfixed, hledgerB, hrootB,
    hcountB⟩ := Flex.walk_scales_flex ω (Fintype.card V) δ ρ
      (ω * δ / 2 ^ 40) (δ * Fintype.card V / 2 ^ 25) hfl rfl rfl
  have hW : 64 * (ω * δ / 2 ^ 40) * Fintype.card V ≤
      (Fintype.card {v // c (p v) = k} : ℝ) := by
    have hcl := hs.class_card i0
    have hsub : (univ.filter fun w => p w = i0).card ≤ Fintype.card {v // c (p v) = k} := by
      rw [Fintype.card_subtype]
      exact card_le_card (fun w hw => mem_filter.mpr ⟨mem_univ _,
        by rw [(mem_filter.mp hw).2]; exact hi0⟩)
    have hsubR : ((univ.filter fun w => p w = i0).card : ℝ) ≤
        (Fintype.card {v // c (p v) = k} : ℝ) := by exact_mod_cast hsub
    have hd1 : δ ≤ 1 := hfl.δ_le_one
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hδ0' : 0 ≤ δ := hδ0.le
    have h1 : 64 * (ω * δ / 2 ^ 40) ≤ ω := by
      have : ω * δ ≤ ω := mul_le_of_le_one_right hω.le hd1
      have : (0 : ℝ) ≤ ω * δ := by positivity
      nlinarith
    nlinarith
  exact component_budget_walk_kappa F c k hc hcard hthree hwalk hlat B hB hord hsize p G ω
    (ω * δ / 2 ^ 40) (ρ) (δ)
    (δ * Fintype.card V / 2 ^ 25) hG hs hlam hlam64 hrho hscale hn hn2 hδ0 hQ hW
    hpathB hembed hfixed hledgerB hrootB hcountB X hXG hX hXin

end PartitionedTriangleAbsorption.BlowupB.FinT

#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.componentCertFlexT_of_even3_walk
#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.componentCertFlexT_of_even3_walk_kappa
