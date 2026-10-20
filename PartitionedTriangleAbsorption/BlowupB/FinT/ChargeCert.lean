/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.FinT.ChargeU12
public import PartitionedTriangleAbsorption.BlowupB.FinT.Cert
public import PartitionedTriangleAbsorption.BlowupB.Flex.TokenScales

@[expose] public section

set_option exponentiation.threshold 512

/-! # Flexible component certificate with one charge (unit `12`, templates), on `Fin t` -/

namespace PartitionedTriangleAbsorption.BlowupB.FinT

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.VertexSplit
open PaddedF12 PaddedGeneral

variable {t : ℕ}

variable {V : Type} [Fintype V] [DecidableEq V]

theorem componentCertFlexT_of_charge_walk_U12 (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t)
    (k : Fin t) (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F) (hwalk : FinT.LocalWalk F c k)
    (χ : Fin t → Fin t → ℤ) (hχ : ∀ i j, |χ i j| ≤ 4) (hkill : Kills χ F)
    (hlat : FinT.ChargeInside F c k χ)
    (hdvd : ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin t) (A : Finset (Sym2 W)),
      (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → (∀ e ∈ A, CompT.InsideE p c k e) →
        OnePart.Even3 A → (12 : ℤ) ∣ charge χ p A)
    (Tp Tm : FinT.Template F c k) (hpc : charge χ Tp.L Tp.E = 12) (hmc : charge χ Tm.L Tm.E = -12)
    (B : ℕ) (hB : FinT.WitnessBoundK F 840 B)
    (hord : terminalOrder 840 B t ≤ 2 ^ 21) (hsize : terminalSize 840 B ≤ 2 ^ 21) :
    ComponentUniversalCertFlexT F c k := by
  intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hX hXin
  have hω := hfl.ω_pos
  have hω1 := hfl.ω_le
  have hn := hfl.ρn
  by_cases hempty : ∀ i, c i ≠ k
  · exact componentUniversalCertFlexT_empty F c k hempty V p G ω δ ρ hfl hG hs X hXG hX hXin
  push Not at hempty
  obtain ⟨i0, hi0⟩ := hempty
  obtain ⟨hlam, hlam64, hrho, hscale, hn2, hδ0, hQ, hlamT, hlamTω, hscaleT, hpathB, hembed,
    hfixed, htokB, hledgerB, hrootB, hcountB⟩ := Flex.charge_scales_N_flex ω (Fintype.card V) δ ρ (ω * δ / 2 ^ 48)
      (δ * Fintype.card V / 2 ^ 33) (δ / 2 ^ 33) hfl rfl rfl rfl
  have hW : 64 * (ω * δ / 2 ^ 48) * Fintype.card V ≤
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
    have h1 : 64 * (ω * δ / 2 ^ 48) ≤ ω := by
      have : ω * δ ≤ ω := mul_le_of_le_one_right hω.le hd1
      have : (0 : ℝ) ≤ ω * δ := by positivity
      nlinarith
    nlinarith
  exact component_budget_charge_walk_U12 F c k hc hcard hthree hwalk χ hχ hkill hlat Tp Tm
    hpc hmc B hB hord hsize p G (fun A hA hact hin h3 => hdvd p A hA hact hin h3) ω
    (ω * δ / 2 ^ 48) (ρ) (δ)
    (δ * Fintype.card V / 2 ^ 33) (δ / 2 ^ 33) hG hs hlam hlam64
    hrho hscale hn hn2 hδ0 hQ hω1 hlamT hlamTω hscaleT hW hpathB hembed hfixed htokB hledgerB
    hrootB hcountB X hXG hX hXin

end PartitionedTriangleAbsorption.BlowupB.FinT

#print axioms PartitionedTriangleAbsorption.BlowupB.FinT.componentCertFlexT_of_charge_walk_U12
