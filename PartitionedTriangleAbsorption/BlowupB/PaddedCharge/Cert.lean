/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedCharge.Universal

@[expose] public section

set_option exponentiation.threshold 512

/-!
# `UniversalCert` for one-charge families with walks of length four

The scales are the padded ones of `UniversalCert`: `γ = ω`, `δ = paddedAbsDelta ω = ω¹²/2⁶³`,
`ρ = paddedRho ω = ω²⁶/2²⁶²`. The refiner runs at `λ = ω δ / 2⁴⁸ = ω¹³/2¹¹¹` (so `2²⁴ ρ ≤ λ²`), the
path internal-load threshold is `Q = δ n / 2³³`, and the token scale is `λ_T = δ / 2³³` (so the
tokens put at most `Q` on any vertex). The supply budget `2^21` and the terminal budget `2^21` (for
pieces of at most `504` edges) are unchanged: `NumericInputs` is not touched.
-/

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- The explicit scale inequalities (pure real arithmetic). -/
theorem charge_scales (ω n δ ρ lam Q lamT : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hδ : δ = ω ^ 12 / 2 ^ 63) (hρ : ρ = ω ^ 26 / 2 ^ 262) (hlam : lam = ω * δ / 2 ^ 48)
    (hQ : Q = δ * n / 2 ^ 33) (hlamT : lamT = δ / 2 ^ 33) (hn : 1 ≤ ρ * n) :
    0 < lam ∧ lam ≤ 1 / 64 ∧ 0 < ρ ∧ 2 ^ 24 * ρ ≤ lam ^ 2 ∧ 256 ≤ lam * n ∧ 0 < δ ∧ 0 < Q ∧
    0 < lamT ∧ 1024 * lamT ≤ ω ∧ (2 ^ 32 : ℝ) * ρ ≤ lamT ^ 2 ∧
    3 * (4100 * lam * n ^ 2) / Q + 3 +
      2 * (2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 2) < ω * n ∧
    (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < ω * n / 2 ∧
    (2 ^ 21 : ℝ) ≤ δ * n / 4 ∧
    2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) ≤ 6 * lamT * n ∧
    2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + lamT * n ≤ δ * n ∧
    (2 ^ 21 : ℝ) * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 44 * (lamT * n)) ≤
      δ * n / 2 ∧
    4 * (2 * ρ + 16 * lam + 6 * 2 ^ 20 * ρ + 2 ^ 23 * ρ * 2 ^ 21) ≤ δ * ω := by
  have hA0 : 0 < ω ^ 12 := by positivity
  have hA1 : ω ^ 12 ≤ ω := pow_le_of_le_one hω.le hω1 (by norm_num)
  have hA2 : ω ^ 12 ≤ 1 := hA1.trans hω1
  have h26 : ω ^ 26 = (ω * ω ^ 12) * (ω * ω ^ 12) := by ring
  have hB : ω * ω ^ 12 ≤ ω ^ 12 := mul_le_of_le_one_left hA0.le hω1
  have hB0 : 0 < ω * ω ^ 12 := by positivity
  have hBB : (ω * ω ^ 12) * (ω * ω ^ 12) ≤ ω * ω ^ 12 :=
    mul_le_of_le_one_left hB0.le (hB.trans hA2)
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlamT0 : 0 < lamT := by rw [hlamT]; positivity
  have e1 : lam = (ω * ω ^ 12) / 2 ^ 111 := by rw [hlam, hδ]; ring
  have e2 : ρ = (ω * ω ^ 12) * (ω * ω ^ 12) / 2 ^ 262 := by rw [hρ, h26]
  have hρlam : 2 ^ 150 * ρ ≤ lam := by
    rw [e1, e2]; norm_num; linarith
  have hlamsq : 2 ^ 24 * ρ ≤ lam ^ 2 := by
    rw [e1, e2]
    have : ((ω * ω ^ 12) / 2 ^ 111) ^ 2 = (ω * ω ^ 12) * (ω * ω ^ 12) / 2 ^ 222 := by ring
    rw [this]
    have : 0 ≤ (ω * ω ^ 12) * (ω * ω ^ 12) := by positivity
    norm_num; linarith
  have hlamδ : 2 ^ 48 * lam ≤ δ := by
    rw [hlam]; nlinarith
  have hδω : 2 ^ 63 * δ ≤ ω := by rw [hδ]; nlinarith
  have hTsq : (2 ^ 32 : ℝ) * ρ ≤ lamT ^ 2 := by
    rw [hlamT, hδ, hρ]
    have h1 : (ω ^ 12 / 2 ^ 63 / 2 ^ 33) ^ 2 = ω ^ 12 * ω ^ 12 / 2 ^ 192 := by ring
    have h2 : ω ^ 26 = (ω * ω) * (ω ^ 12 * ω ^ 12) := by ring
    rw [h1, h2]
    have hωω : ω * ω ≤ 1 := by nlinarith
    have h3 : 0 ≤ ω ^ 12 * ω ^ 12 := by positivity
    have h4 : (ω * ω) * (ω ^ 12 * ω ^ 12) ≤ ω ^ 12 * ω ^ 12 :=
      mul_le_of_le_one_left h3 hωω
    norm_num; linarith
  have hn0 : 0 < n := by
    by_contra h
    have h' : n ≤ 0 := le_of_not_gt h
    nlinarith
  have hρn : 2 ^ 150 ≤ lam * n := by nlinarith
  have hlamn : 2 ^ 48 * (lam * n) ≤ δ * n := by nlinarith
  have hδn : 2 ^ 63 * (δ * n) ≤ ω * n := by nlinarith
  have hρn' : 2 ^ 150 * (ρ * n) ≤ lam * n := by nlinarith
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hTn : lamT * n = Q := by rw [hlamT, hQ]; ring
  have hdiv : 3 * (4100 * lam * n ^ 2) / Q = 12300 / 2 ^ 15 * ω * n := by
    rw [hQ, hlam]; field_simp; ring
  have hQd : Q = δ * n / 2 ^ 33 := hQ
  have hlamn1 : 2 ^ 150 ≤ lam * n := hρn
  refine ⟨hlam0, ?_, hρ0, hlamsq, by linarith, hδ0, hQ0, hlamT0, ?_, hTsq, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · nlinarith
  · rw [hlamT]; linarith
  · rw [hdiv, hQd]; linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [hlam]
    have : 0 ≤ ω * δ := by positivity
    have h1 : ρ ≤ lam / 2 ^ 150 := by linarith
    rw [hlam] at h1
    linarith

/-- **`UniversalCert` for one-charge families without common neighbour classes.** For every
family with `ThreeStepLinks`, walks of length four in the allowed-pair graph, a single integral
charge `χ` (`|χ| ≤ 2`) and no torsion (`ChargeLattice F χ`), charges of `Even3` sets divisible by
`12`, the two fixed token templates of charges `±12`, and an explicit witness bound `B` for pieces
of at most `504` edges whose terminal order and size fit into `2^21`. -/
theorem universalCert_of_charge_walk (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (hwalk : Walk4 (fun i j : Fin 4 => ∃ k, Link F i j k))
    (χ : Fin 4 → Fin 4 → ℤ) (hχ : ∀ i j, |χ i j| ≤ 2) (hlat : ChargeLattice F χ)
    (hdvd : ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4) (A : Finset (Sym2 W)),
      (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → OnePart.Even3 A → (12 : ℤ) ∣ charge χ p A)
    (hplus : ActiveEdges F plusLabel triangleSlots) (hminus : ActiveEdges F minusLabel cycleSlots)
    (hpc : charge χ plusLabel triangleSlots = 12) (hmc : charge χ minusLabel cycleSlots = -12)
    (B : ℕ) (hB : WitnessBoundK F 504 B)
    (hord : terminalOrder 504 B 4 ≤ 2 ^ 21) (hsize : terminalSize 504 B ≤ 2 ^ 21) :
    UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  have hδ : paddedAbsDelta ω = ω ^ 12 / 2 ^ 63 := by
    unfold paddedAbsDelta paddedKappa; ring
  obtain ⟨hlam, hlam64, hrho, hscale, hn2, hδ0, hQ, hlamT, hlamTω, hscaleT, hpathB, hembed,
    hfixed, htokB, hledgerB, hrootB, hcountB⟩ := charge_scales ω (Fintype.card V)
      (paddedAbsDelta ω) (paddedRho ω) (ω * paddedAbsDelta ω / 2 ^ 48)
      (paddedAbsDelta ω * Fintype.card V / 2 ^ 33) (paddedAbsDelta ω / 2 ^ 33) hω hω1 hδ rfl
      rfl rfl rfl hn
  exact universal_budget_charge_walk F hcard hthree hwalk χ hχ hlat hplus hminus hpc hmc B hB
    hord hsize p G (fun A hA hact h3 => hdvd p A hA hact h3) ω
    (ω * paddedAbsDelta ω / 2 ^ 48) (paddedRho ω) (paddedAbsDelta ω)
    (paddedAbsDelta ω * Fintype.card V / 2 ^ 33) (paddedAbsDelta ω / 2 ^ 33) hG hs hω1
    hlam hlam64 hrho hscale hn hn2 hδ0 hQ hlamT hlamTω hscaleT hpathB hembed hfixed htokB
    hledgerB hrootB hcountB

/-- The terminal budgets for `FnoC` (`K = 504`, `B = 6 · 504 = 3024`): order `335668`,
size `1014552`, both `≤ 2^21`. -/
theorem terminal_budgets_FnoC :
    terminalOrder 504 (6 * 504) 4 ≤ 2 ^ 21 ∧ terminalSize 504 (6 * 504) ≤ 2 ^ 21 := by
  unfold terminalOrder terminalSize; norm_num

/-- **Target A, universal certificate: `UniversalCert FnoC`.** -/
theorem universalCert_FnoC : UniversalCert FnoC :=
  universalCert_of_charge_walk FnoC baseFacts_FnoC.card baseFacts_FnoC.three baseFacts_FnoC.walk
    chiNoC chiNoC_bound chargeLattice_FnoC (fun p A hA hact h3 => twelve_dvd_FnoC p A hA hact h3)
    plus_active_FnoC minus_active_FnoC plus_charge_FnoC minus_charge_FnoC (6 * 504)
    (witnessBound_FnoC 504) terminal_budgets_FnoC.1 terminal_budgets_FnoC.2

end PaddedCharge

#print axioms PaddedCharge.charge_scales
#print axioms PaddedCharge.universalCert_of_charge_walk
#print axioms PaddedCharge.universalCert_FnoC
