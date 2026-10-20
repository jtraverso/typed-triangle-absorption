/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPhysicalRefiner
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.NativePhysicalScales
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge.TriAbsorber

@[expose] public section

/-! Native physical three-colour producer. Its fixed reserve, catalogue,
anchors and paths are constructed before all balanced residual demands. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer

open Finset Cycles AntiEdgeSelection StructuralF3General PartitionedTriangleAbsorption.TypedTransformer

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

theorem physicalCycRefiner3 : Bridge.PhysicalCycRefiner3 := by
  let q := RootPhysicalEmbedding.factor
  have hq := WeightedEmbeddingBudget.factor_bounds RootCatalogueBudget.constant 20
  have hq1 : (1 : ℝ) ≤ q := by dsimp [q, RootPhysicalEmbedding.factor]; linarith [hq.1]
  refine ⟨80, 4 * q, q, ?_⟩
  intro V _ _ p G _ ω lam rho hω hω1 hlam hsmall hrho hscale hsize hG hs X hXG hXdeg
  let n : ℝ := Fintype.card V
  let t := lam / 4096
  have hsmall' : (q : ℝ) * lam ≤ ω ^ 3 :=
    NativePhysicalScales.small_of_power q lam ω hlam.le hsmall
  obtain ⟨ht, ht1, hn, hρt, htn, hqt, htl⟩ :=
    NativePhysicalScales.parameters q ω lam rho n hq1 hω hω1 hlam hrho hsmall' hscale hsize
  change rho ≤ t ^ 2 at hρt
  have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := hn
  have hpos : 0 < Fintype.card V := by exact_mod_cast hnR
  have : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hallowed : ∀ i j : Fin 3, (∃ k, Link Bridge.F_tri i j k) ↔ i ≠ j := by
    unfold Link Bridge.F_tri
    decide
  have hs' : GuardedSupply p G (fun i j => i ≠ j) 2 (ω * n) := by
    intro S hS i hguard
    exact hs S (hS.trans (by norm_num)) i (fun v hv => (hallowed _ _).mpr (hguard v hv))
  have hcolour : ∀ i, CatalogueColours.colour i = Bridge.triColour i := by decide
  have hcolourFun : CatalogueColours.colour ∘ p = fun v => Bridge.triColour (p v) :=
    funext (fun v => hcolour (p v))
  let OX := Bridge.orientTri p X
  have hOXcyc : IsCyc (CatalogueColours.colour ∘ p) OX := by
    have hh := Bridge.isCyc_orientBy (fun v => Bridge.triColour (p v)) X
    rw [hcolourFun]
    exact hh
  have hforget : PhysicalPathArcs.forget OX = X := by
    change Bridge.symImage (Bridge.orientTri p X) = X
    apply Bridge.symImage_orientBy
    intro a b hab
    obtain ⟨k, hk⟩ := hG a b (SimpleGraph.mem_edgeFinset.mp (hXG hab))
    exact Bridge.tri_link_consecutive _ _ _ hk
  have hDX : ∀ v, (deg OX v : ℝ) ≤ 2 * rho * n := by
    intro v
    have hh := Bridge.incidentLoad_symImageBy hOXcyc v
    change incidentLoad (PhysicalPathArcs.forget OX) v = deg OX v at hh
    rw [hforget] at hh
    rw [← hh]
    exact hXdeg v
  have hcard : (OX.card : ℝ) ≤ rho * n ^ 2 := NativePhysicalScales.input_card OX rho hDX
  have hcard' : (OX.card : ℝ) ≤ t ^ 2 * n ^ 2 :=
    hcard.trans (mul_le_mul_of_nonneg_right hρt (sq_nonneg n))
  have hdeg' : ∀ v, (deg OX v : ℝ) ≤ 2 * t ^ 2 * n := by
    intro v
    exact (hDX v).trans (by nlinarith [mul_le_mul_of_nonneg_right hρt hn.le])
  have hB : DegBounded (PhysicalPathArcs.forget OX) (2 * t ^ 2 * n) := by
    rw [hforget]
    intro v
    have hh : (incidentLoad X v : ℝ) ≤ 2 * rho * n := hXdeg v
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hρt hn.le])
  obtain ⟨R, lib, hRG, hRC, hRX, hRdeg, hp, hcount, hload, hpart⟩ :=
    RootPhysicalRefiner.exists_refiner p G OX ω t n hω ht ht1 hn htn hqt hOXcyc hcard' hdeg' hB hs'
  have htarget : ∀ b : ℝ, b ≤ 3 * (q : ℝ) * t * n → b ≤ (4 * q : ℕ) * lam * n / ω := by
    intro b hb
    have hh := WeightedEmbeddingBudget.load_target q t n lam ω b (by linarith) hn.le hlam.le
      hω hω1 htl hb
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hlam1 : lam ≤ 1 := by
    have hω2 : ω * ω ≤ ω := mul_le_of_le_one_right hω.le hω1
    have hω3 : ω ^ 3 ≤ 1 := by nlinarith
    nlinarith
  have hcount' : (lib.card : ℝ) ≤ (q : ℝ) * rho * n ^ 2 := by
    have hh : (lib.card : ℝ) ≤ (49 * (RootCatalogueBudget.constant : ℝ) + 16) * (OX.card : ℝ) := by
      exact_mod_cast hcount
    have hcoeff : 49 * (RootCatalogueBudget.constant : ℝ) + 16 ≤ (q : ℝ) := hq.2.2.2
    calc
      _ ≤ (49 * (RootCatalogueBudget.constant : ℝ) + 16) * (OX.card : ℝ) := hh
      _ ≤ (49 * (RootCatalogueBudget.constant : ℝ) + 16) * (rho * n ^ 2) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ (q : ℝ) * (rho * n ^ 2) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = _ := by ring
  have hcountTarget := WeightedEmbeddingBudget.count_target q rho lam n ω lib.card
    (by linarith) hlam.le hlam1 hω hω1 hscale hcount'
  refine ⟨R, lib, hRG, ?_, hRX, (fun v => htarget _ (hRdeg v)), hp, ?_,
    (fun v => htarget _ (hload v)), hpart⟩
  · rwa [hcolourFun] at hRC
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcountTarget

theorem triUniversalCert : ∃ L, RefinerAbsorber.UniversalFamilyCert Bridge.F_tri L :=
  Bridge.triUniversalCert_of_physicalCycRefiner3 physicalCycRefiner3

theorem latinTarget : LatinTarget := Bridge.latinTarget_of_physicalCycRefiner3 physicalCycRefiner3

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer.physicalCycRefiner3
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer.triUniversalCert
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer.latinTarget
