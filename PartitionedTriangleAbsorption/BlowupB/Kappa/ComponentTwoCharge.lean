/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.ComponentChargeTorsion
public import PartitionedTriangleAbsorption.BlowupB.Kappa.TokenLayerTrack

@[expose] public section

set_option exponentiation.threshold 512

/-!
# Componentwise universal certificate for a component with two integral charges of unit `4`

Inside the component the lattice is "even, `χ = 0`, `χ₂ = 0`" (`TwoChargeInside`). Route:
Aristotle's component walk (`KappaLinks` terminals), a first charge layer for `χ` with physical
templates of charge `±4` and `χ₂ = 0` (`token_layer_track`: every new piece keeps the `χ₂` of its old
piece, so `|χ₂| ≤ 672` and at most `168` second tokens are needed), then a second charge layer for
`χ₂` with templates of charge `±4` and `χ = 0` (`χ` stays zero). Pieces of at most `2184` edges; the
second token family runs at the scale `2¹³ ρ`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PaddedF12 PaddedGeneral PaddedNoCommon PaddedCharge
open GuardedTemplates TorsionQ

/-- Inside component `k`: "even, both charges zero" is divisibility. -/
def TwoChargeInside (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) (k : Fin 4)
    (χ χ₂ : Fin 4 → Fin 4 → ℤ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4) (E : Finset (Sym2 V)),
    (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F p E → (∀ e ∈ E, InsideE p c k e) →
      (∀ v, Even (incidentLoad E v)) → charge χ p E = 0 → charge χ₂ p E = 0 → IsIntDiv p F E

section Tokens

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem host_charge_tokens_gen2 {κ : Type*}
    (F : Finset (Multiset (Fin 4))) (χ χ' : Fin 4 → Fin 4 → ℤ)
    (c : Fin 4 → Fin 4) (k : Fin 4) (Tp Tm : Template F c k)
    (hplusCharge : charge χ Tp.L Tp.E = 4) (hminusCharge : charge χ Tm.L Tm.E = -4)
    (hplus' : charge χ' Tp.L Tp.E = 0) (hminus' : charge χ' Tm.L Tm.E = 0)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Tok κ)) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : Tok κ → Finset (Sym2 V), TokReal χ χ' p 4 6 B S tok ∧
      (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      (∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V) ∧
      ∀ τ ∈ S, ∀ e ∈ tok τ, InsideE p c k e := by
  classical
  let E : Tok κ → Finset (Sym2 (Fin 6)) := fun τ => if τ.sign then Tp.E else Tm.E
  let label : Tok κ → Fin 6 → Fin 4 := fun τ => if τ.sign then Tp.L else Tm.L
  have hdata (τ : Tok κ) : (∀ e ∈ E τ, ¬ e.IsDiag) ∧ ActiveEdges F (label τ) (E τ) ∧
      (∀ w, Even (incidentLoad (E τ) w)) ∧ (E τ).card ≤ 6 ∧
      charge χ (label τ) (E τ) = if τ.sign then 4 else -4 := by
    by_cases hτ : τ.sign = true
    · simp only [E, label, ite_eq_left hτ]
      exact ⟨Tp.loop, Tp.act, Tp.even, Tp.card, hplusCharge⟩
    · simp only [E, label, ite_eq_right hτ]
      exact ⟨Tm.loop, Tm.act, Tm.even, Tm.card, hminusCharge⟩
  obtain ⟨f, hf, hload⟩ := guarded_template_family_scaled p G (fun i j => ∃ k, Link F i j k)
    S E label (fun τ _ => (hdata τ).1) (fun τ _ => (hdata τ).2.1)
    (fun τ _ => (hdata τ).2.2.2.1) ω lam rho hs B hB hω hlam hlamω hrho hscale hn1 hcount
  let tok := fun τ => mapped (E τ) (f τ)
  refine ⟨tok, ⟨hf.disjoint, hf.avoid, ?_, ?_, ?_, ?_, ?_⟩, hf.subgraph, hload, ?_⟩
  rotate_right
  · intro τ hτ e he
    obtain ⟨e0, -, rfl⟩ := Finset.mem_image.mp he
    induction e0 using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, insideE_mk, hf.labels τ hτ x, hf.labels τ hτ y]
      by_cases hs : τ.sign = true
      · simp only [label, hs, ite_true]; exact ⟨Tp.inside x, Tp.inside y⟩
      · simp only [label, hs]; exact ⟨Tm.inside x, Tm.inside y⟩
  · intro τ hτ
    exact loopless_image (f τ) (hf.injective τ hτ) (E τ) (hdata τ).1
  · intro τ hτ
    exact even_image (f τ) (hf.injective τ hτ) (E τ) (hdata τ).2.2.1
  · intro τ hτ
    change charge χ p ((E τ).image (Sym2.map (f τ))) = _
    rw [charge_image (f τ) (hf.injective τ hτ) p (label τ) (hf.labels τ hτ)]
    exact (hdata τ).2.2.2.2
  · intro τ hτ
    change charge χ' p ((E τ).image (Sym2.map (f τ))) = 0
    rw [charge_image (f τ) (hf.injective τ hτ) p (label τ) (hf.labels τ hτ)]
    by_cases hs : τ.sign = true
    · simp only [E, label, ite_eq_left hs]; exact hplus'
    · simp only [E, label, ite_eq_right hs]; exact hminus'
  · intro τ _
    exact card_image_le.trans (hdata τ).2.2.2.1

end Tokens

variable {V : Type} [Fintype V] [DecidableEq V]

theorem twoc_scales (ω n δ ρ lam Q lamT : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1)
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
    4 * (2 * ρ + 16 * lam + 2 ^ 38 * ρ + 2 ^ 39 * ρ * 2 ^ 21) ≤ δ * ω ∧
    2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + lamT * n ≤ 6 * lamT * n ∧
    2 * ρ * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + 2 * (lamT * n) ≤ δ * n ∧
    (2 ^ 21 : ℝ) * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 88 * (lamT * n)) ≤
      δ * n / 2 ∧
    (2 ^ 32 : ℝ) * (2 ^ 13 * ρ) ≤ lamT ^ 2 := by
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
  have hTsq2 : (2 ^ 32 : ℝ) * (2 ^ 13 * ρ) ≤ lamT ^ 2 := by
    rw [hlamT, hδ, hρ]
    have h1 : (ω ^ 12 / 2 ^ 63 / 2 ^ 33) ^ 2 = ω ^ 12 * ω ^ 12 / 2 ^ 192 := by ring
    have h2 : ω ^ 26 = (ω * ω) * (ω ^ 12 * ω ^ 12) := by ring
    rw [h1, h2]
    have hωω : ω * ω ≤ 1 := by nlinarith
    have h3 : 0 ≤ ω ^ 12 * ω ^ 12 := by positivity
    have h4 : (ω * ω) * (ω ^ 12 * ω ^ 12) ≤ ω ^ 12 * ω ^ 12 :=
      mul_le_of_le_one_left h3 hωω
    norm_num; linarith
  refine ⟨hlam0, ?_, hρ0, hlamsq, by linarith, hδ0, hQ0, hlamT0, ?_, hTsq, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hTsq2⟩
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
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 4000000 in
theorem component_budget_twoc_walk (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) (k : Fin 4)
    (hc : CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F)
    (hwalk : LocalWalk4 F c k)
    (χ χ₂ : Fin 4 → Fin 4 → ℤ) (hχ : ∀ i j, |χ i j| ≤ 2) (hχ₂ : ∀ i j, |χ₂ i j| ≤ 2)
    (hkill : Kills χ F) (hkill₂ : Kills χ₂ F)
    (hlat : TwoChargeInside F c k χ χ₂)
    (Tp Tm Up Um : Template F c k)
    (hpc : charge χ Tp.L Tp.E = 4) (hmc : charge χ Tm.L Tm.E = -4)
    (hpc₂ : charge χ₂ Tp.L Tp.E = 0) (hmc₂ : charge χ₂ Tm.L Tm.E = 0)
    (hup : charge χ₂ Up.L Up.E = 4) (hum : charge χ₂ Um.L Um.E = -4)
    (hup₁ : charge χ Up.L Up.E = 0) (hum₁ : charge χ Um.L Um.E = 0)
    (B : ℕ) (hB : WitnessBoundK F 2184 B)
    (hord : terminalOrder 2184 B 4 ≤ 2 ^ 21) (hsize : terminalSize 2184 B ≤ 2 ^ 21)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdvd : ∀ A : Finset (Sym2 V), (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A →
      (∀ e ∈ A, InsideE p c k e) → OnePart.Even3 A → (4 : ℤ) ∣ charge χ p A)
    (hdvd₂ : ∀ A : Finset (Sym2 V), (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A →
      (∀ e ∈ A, InsideE p c k e) → OnePart.Even3 A → (4 : ℤ) ∣ charge χ₂ p A)
    (γ lam rho δ Q lamT : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (γ * Fintype.card V))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hQ : 0 < Q) (hγ1 : γ ≤ 1) (hlamT : 0 < lamT) (hlamTγ : 1024 * lamT ≤ γ)
    (hscaleT : (2 ^ 32 : ℝ) * rho ≤ lamT ^ 2)
    (hW : 64 * lam * Fintype.card V ≤ (Fintype.card {v // c (p v) = k} : ℝ))
    (hpathB : 3 * (4100 * lam * (Fintype.card V : ℝ) ^ 2) / Q + 3 +
      2 * (2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)) + 2) < γ * Fintype.card V)
    (hembed : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * Fintype.card V) < γ * Fintype.card V / 2)
    (hfixed : (2 ^ 21 : ℝ) ≤ δ * Fintype.card V / 4)
    (htokB : 2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) ≤ 6 * lamT * Fintype.card V)
    (htokB2 : 2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) + lamT * Fintype.card V ≤
        6 * lamT * Fintype.card V)
    (hledgerB : 2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) + 2 * (lamT * Fintype.card V) ≤
        δ * Fintype.card V)
    (hrootB : (2 ^ 21 : ℝ) * (4096 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1)) + 88 * (lamT * Fintype.card V)) ≤
        δ * Fintype.card V / 2)
    (hcountB : 4 * (2 * rho + 16 * lam + 2 ^ 38 * rho + 2 ^ 39 * rho * 2 ^ 21) ≤ δ * γ)
    (hscaleT2 : (2 ^ 32 : ℝ) * (2 ^ 13 * rho) ≤ lamT ^ 2)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) (hXin : ∀ e ∈ X, InsideE p c k e) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, InsideE p c k e) ∧
      HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ 21 := ⟨_, rfl⟩
  have hCR : (C : ℝ) = 2 ^ 21 := by rw [hCdef]; norm_num
  have hterminal : ∀ (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V),
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a →
      DegBounded L d → 0 ≤ d → (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a →
      ∀ P : Finset (Sym2 V), P.card ≤ 2184 → (∀ e ∈ P, ¬ e.IsDiag) → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (2 ^ 21) A := by
    intro a d L Z hsa hL hd hbudget P hK hloop hdiv
    have hqR : (terminalOrder 2184 B 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hord
    have hbudget' : (terminalOrder 2184 B 4 : ℝ) + Z.card + terminalOrder 2184 B 4 * d < a := by
      have hm := mul_le_mul_of_nonneg_right hqR hd
      linarith
    obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass_kappa F hcard hthree 2184 B
      (fun pW PW hKW hdivW => hB pW PW hKW hdivW)
      p G a d L Z (hsa.mono hord le_rfl) hL hd hbudget' P hK hloop hdiv
    exact ⟨A, { hA with card_le := hA.card_le.trans hsize }⟩
  have hstep : PrivateStep p F G 2184 C (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    intro L hL hLc P hPG hm hdiv
    let High : Finset V := univ.filter fun v => (δ * n) < (incidentLoad L v : ℝ)
    have hHigh : (High.card : ℝ) ≤ γ * n / 2 := by
      have hc := card_highLoad_le L (δ * n)
      change (High.card : ℝ) * (δ * n) ≤ 2 * L.card at hc
      have hnpos : 0 < n := by
        by_contra h
        have heq : n = 0 := le_antisymm (le_of_not_gt h) hn0
        rw [heq, mul_zero] at hn1
        norm_num at hn1
      have hδn : 0 < δ * n := by positivity
      nlinarith
    have hbudget' : (2 ^ 21 : ℝ) + High.card + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n := by
      linarith
    have hloop : ∀ e ∈ P, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeFinset (hPG he)
    obtain ⟨A, hA⟩ := hterminal (γ * n) (2 * δ * n) L High hs hL (by positivity) hbudget' P hm
      hloop hdiv
    refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
    intro v hv
    rcases hA.vertices v hv with hp | hz
    · exact Or.inl hp
    · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hloopG : ∀ P ⊆ G.edgeFinset, ∀ e ∈ P, ¬ e.IsDiag :=
    fun P hP e he => G.not_isDiag_of_mem_edgeFinset (hP he)
  have hactG : ∀ P ⊆ G.edgeFinset, ActiveEdges F p P := fun P hP a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hP hab))
  -- 1. the refiner inside the component
  obtain ⟨indices, P, R, hRin, hRX, href, hpieces, hRdeg, hcardI, hinc⟩ :=
    exists_component_refiner p c k lam rho hlam hlam64 hrho hscale hn1 hn2 hW X hXin
      (hloopG X hXG) hX
  have hRloop : ∀ e ∈ R, ¬ e.IsDiag := fun e he => (hRin e he).2
  -- 2. weights and the physical paths inside the component
  let wt : Sym2 V → ℕ := fun e => (∑ i ∈ indices, if e ∈ P i then 1 else 0) + 1
  have hwt1 : ∀ e ∈ R, 1 ≤ wt e := fun e _ => Nat.le_add_left _ _
  have hwtM : ∀ e ∈ R, (wt e : ℝ) ≤ 4096 * lam * n + 1 := by
    intro e _
    have h1 := multiplicity_le_incidence P indices e
    have h2 : ((∑ i ∈ indices, incidentLoad (P i) (endU e) : ℕ) : ℝ) ≤ 4096 * lam * n :=
      hinc (endU e)
    have h3 : ((∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) ≤ 4096 * lam * n :=
      le_trans (by exact_mod_cast h1) h2
    change (((∑ i ∈ indices, if e ∈ P i then 1 else 0) + 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hW' : ∑ e ∈ R, (wt e : ℝ) ≤ 4100 * lam * n ^ 2 := by
    have h1 := sum_multiplicity_le P indices R
    have h2 : ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) ≤ n * (4096 * lam * n) := by
      calc ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ)
          = ∑ w, ((∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) := Nat.cast_sum _ _
        _ ≤ ∑ _w : V, 4096 * lam * n := sum_le_sum fun w _ => hinc w
        _ = n * (4096 * lam * n) := by rw [sum_const, card_univ, nsmul_eq_mul]
    have h3 := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    have hsum : ∑ e ∈ R, (wt e : ℝ) =
        ((∑ e ∈ R, ∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) + R.card := by
      simp only [wt]
      push_cast
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    have h1' : ((∑ e ∈ R, ∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) ≤
        ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hsum]
    change _ ≤ n * (4 * lam * n) at h3
    nlinarith
  have hwalkR : ∀ e ∈ R, ∃ c1 c2 c3, (∃ l, Link F (p (endU e)) c1 l) ∧ (∃ l, Link F c2 c1 l) ∧
      (∃ l, Link F c2 c3 l) ∧ (∃ l, Link F (p (endV e)) c3 l) := by
    intro e he
    have hin := (hRin e he).1
    rw [← mk_ends e, insideE_mk] at hin
    exact hwalk _ _ hin.1 hin.2
  obtain ⟨x, y, z, hpath, havoid, hdisj, hint⟩ := exists_path_system_local p G _ (γ * n)
    (hs.mono (by norm_num) le_rfl) X R hRloop hwalkR (2 * rho * n) (4 * lam * n) hX hRdeg wt
    (4096 * lam * n + 1) (4100 * lam * n ^ 2) Q hwt1 hwtM hW' (by positivity) (by positivity)
    (by positivity) hQ hpathB
  have hsys : PathSystem G X R x y z := ⟨hRX, hRloop, hpath, havoid, hdisj⟩
  -- 3. the physical pieces
  set R' := R.biUnion (physPath x y z) with hR'
  let P' : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V) := fun i => physPiece X x y z (P i)
  have hR'G : R' ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun e he => pathEdges_subset (hpath e he)
  have hR'X : Disjoint R' X := (disjoint_biUnion_left _ _ _).mpr fun e he => havoid e he
  have hR'in : ∀ e ∈ R', InsideE p c k e := by
    intro e he
    obtain ⟨e0, he0, hee0⟩ := mem_biUnion.mp he
    have hin := (hRin e0 he0).1
    rw [← mk_ends e0, insideE_mk] at hin
    exact path_insideE hc hG (hpath e0 he0) hin.1 e hee0
  have hPsub : ∀ i ∈ indices, P i ⊆ X ∪ R := fun i hi => (hpieces i hi).1
  have href' : RefinerAssembly.RefinesReserve (p := p) (F := F) indices P' X R' := by
    intro L hL hdivL
    have hloop := hloopG L (hL.trans hXG)
    have h3 : OnePart.Even3 L := PaddedTrivial.even3_of_isIntDiv hcard p hloop hdivL
    obtain ⟨s, hs_sub, hsdis, hsU⟩ := href L hL h3
    exact ⟨s, hs_sub, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL
      hsU).1, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL hsU).2⟩
  have hP'G : ∀ i ∈ indices, P' i ⊆ G.edgeFinset := fun i hi =>
    hsys.physPiece_subset_G hXG (hPsub i hi)
  have hP'sub : ∀ i ∈ indices, P' i ⊆ X ∪ R' := fun i hi => hsys.physPiece_subset (hPsub i hi)
  have hP'card : ∀ i ∈ indices, (P' i).card ≤ 168 := fun i hi =>
    (hsys.physPiece_card_le (hPsub i hi)).trans (by have := (hpieces i hi).2.2; omega)
  -- 4. the charge layer with physical tokens inside the component
  have hR'deg : DegBounded R' (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) := by
    intro v
    have h1 := incidentLoad_biUnion_physPath_le R x y z hRloop hpath wt hwt1 v
    have h1' : ((incidentLoad R' v : ℕ) : ℝ) ≤
        (incidentLoad R v : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by exact_mod_cast h1
    have h2 := hRdeg v
    have h3 := hint v
    change ((incidentLoad R' v : ℕ) : ℝ) ≤ _
    change ((incidentLoad R v : ℕ) : ℝ) ≤ _ at h2
    linarith
  have hP'in : ∀ i ∈ indices, ∀ e ∈ P' i, InsideE p c k e := by
    intro i hi e he
    rcases mem_union.mp (hP'sub i hi he) with h | h
    · exact hXin e h
    · exact hR'in e h
  let E0 : PredRefiner (ℕ × Bool × Fin 3 × Fin 3) X OnePart.Even3 :=
    { lib := indices
      P := P'
      R0 := R'
      loopP := fun i hi => hloopG _ (hP'G i hi)
      evenP := fun i hi => (hsys.physPiece_even3 (hPsub i hi) (hpieces i hi).2.1).2
      subP := fun i hi => by rw [union_comm]; exact hP'sub i hi
      disjRX := hR'X
      refines := fun L hL h3 => by
        obtain ⟨s, hs_sub, hsdis, hsU⟩ := href L hL h3
        exact ⟨s, hs_sub, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL
          hsU).1, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL hsU).2⟩ }
  have hQ0 : OnePart.Even3 (∅ : Finset (Sym2 V)) :=
    ⟨by simp, fun v => by simp [incidentLoad]⟩
  have hdvd0 : ∀ i ∈ E0.lib, (4 : ℤ) ∣ charge χ p (E0.P i) := fun i hi =>
    hdvd _ (hloopG _ (hP'G i hi)) (hactG _ (hP'G i hi)) (hP'in i hi)
      (hsys.physPiece_even3 (hPsub i hi) (hpieces i hi).2.1)
  have habs : ∀ i ∈ E0.lib, (charge χ p (E0.P i) / 4).natAbs ≤ 168 := by
    intro i hi
    have hb := abs_charge_le p (fun e => abs_pair_pairVec_le hχ p e) (E0.P i)
    have hc : ((E0.P i).card : ℤ) ≤ 168 := by exact_mod_cast hP'card i hi
    have heq : charge χ p (E0.P i) = 4 * (charge χ p (E0.P i) / 4) :=
      (Int.mul_ediv_cancel' (hdvd0 i hi)).symm
    rw [heq, abs_mul] at hb
    norm_num at hb
    have hnat : ((charge χ p (E0.P i) / 4).natAbs : ℤ) ≤ 168 := by
      rw [Int.natCast_natAbs]
      omega
    exact_mod_cast hnat
  have hsum : ∑ i ∈ E0.lib, (charge χ p (E0.P i) / 4).natAbs ≤ 168 * E0.lib.card := by
    calc
      _ ≤ ∑ _i ∈ E0.lib, 168 := sum_le_sum habs
      _ = _ := by simp [mul_comm]
  have hlibR : (E0.lib.card : ℝ) ≤ 1224 * rho * n ^ 2 := hcardI
  have hBdeg : DegBounded (E0.R0 ∪ X) (6 * lamT * n) := by
    intro v
    have h := degBounded_union hR'deg hX v
    change (incidentLoad (R' ∪ X) v : ℝ) ≤ 6 * lamT * n
    change (incidentLoad (R' ∪ X) v : ℝ) ≤ _ at h
    have : 0 ≤ lamT * n := mul_nonneg hlamT.le hn0
    linarith
  let ExtraC : Finset (Tok (ℕ × Bool × Fin 3 × Fin 3)) →
      (Tok (ℕ × Bool × Fin 3 × Fin 3) → Finset (Sym2 V)) → Prop :=
    fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      (∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lamT * n) ∧
      ∀ a ∈ S, ∀ e ∈ tok a, InsideE p c k e
  obtain ⟨S, tok, E1, hreal, hextra, hS, hE1R, hzero1, _, htrack1, hsize1, hload1, hlib1⟩ :=
    token_layer_track E0 hQ0 χ χ₂ p 4 (by norm_num) hdvd0 6 ExtraC (by
      intro S hS
      have hsN : S.card ≤ 1512 * E0.lib.card := by omega
      have hsR : (S.card : ℝ) ≤ 1512 * (E0.lib.card : ℝ) := by exact_mod_cast hsN
      have hSbound : (S.card : ℝ) ≤ 2 ^ 22 * rho * n ^ 2 := by
        nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
      obtain ⟨tk, h1, h2, h3, h4⟩ := host_charge_tokens_gen2 F χ χ₂ c k Tp Tm hpc hmc hpc₂ hmc₂ p G S _
        γ lamT rho (hs.mono (by norm_num) le_rfl) hBdeg hγ1 hlamT hlamTγ hrho hscaleT hn1 hSbound
      exact ⟨tk, h1, h2, h3, h4⟩)
  have hE1R' : E1.R0 = R' ∪ S.biUnion tok := hE1R
  have hTG : S.biUnion tok ⊆ G.edgeFinset := biUnion_subset.mpr hextra.1
  have hTin : ∀ e ∈ S.biUnion tok, InsideE p c k e := by
    intro e he
    obtain ⟨a, ha, hea⟩ := mem_biUnion.mp he
    exact hextra.2.2 a ha e hea
  have hR1G : E1.R0 ⊆ G.edgeFinset := by rw [hE1R']; exact union_subset hR'G hTG
  have hP1G : ∀ j ∈ E1.lib, E1.P j ⊆ G.edgeFinset := fun j hj =>
    (E1.subP j hj).trans (union_subset hR1G hXG)
  have hP1in : ∀ j ∈ E1.lib, ∀ e ∈ E1.P j, InsideE p c k e := by
    intro j hj e he
    rcases mem_union.mp (E1.subP j hj he) with h | h
    · rw [hE1R'] at h
      rcases mem_union.mp h with h | h
      · exact hR'in e h
      · exact hTin e h
    · exact hXin e h
  have hP1card : ∀ j ∈ E1.lib, (E1.P j).card ≤ 1176 := by
    intro j hj
    rcases hsize1 j hj with h | ⟨i, hi, h⟩
    · omega
    · have hP : (E0.P i).card ≤ 168 := hP'card i hi
      have hA := habs i hi
      have : 6 * (charge χ p (E0.P i) / 4).natAbs ≤ 6 * 168 := Nat.mul_le_mul_left 6 hA
      omega
  -- 5. the second charge layer (χ₂); the first charge stays zero
  have hQ1 : OnePart.Even3 (∅ : Finset (Sym2 V)) ∧ charge χ p (∅ : Finset (Sym2 V)) = 0 :=
    ⟨hQ0, charge_empty _ _⟩
  have hE0₂ : ∀ i ∈ E0.lib, (4 : ℤ) ∣ charge χ₂ p (E0.P i) := fun i hi =>
    hdvd₂ _ (hloopG _ (hP'G i hi)) (hactG _ (hP'G i hi)) (hP'in i hi)
      (hsys.physPiece_even3 (hPsub i hi) (hpieces i hi).2.1)
  have hE0₂abs : ∀ i ∈ E0.lib, |charge χ₂ p (E0.P i)| ≤ 672 := by
    intro i hi
    have hb := abs_charge_le p (fun e => abs_pair_pairVec_le hχ₂ p e) (E0.P i)
    have hc : ((E0.P i).card : ℤ) ≤ 168 := by exact_mod_cast hP'card i hi
    norm_num at hb
    linarith
  have hdvd1 : ∀ j ∈ E1.lib, (4 : ℤ) ∣ charge χ₂ p (E1.P j) := by
    intro j hj
    rcases htrack1 j hj with h | ⟨i, hi, h⟩
    · rw [h]; exact dvd_zero _
    · rw [h]; exact hE0₂ i hi
  have habs1 : ∀ j ∈ E1.lib, (charge χ₂ p (E1.P j) / 4).natAbs ≤ 168 := by
    intro j hj
    have hb : |charge χ₂ p (E1.P j)| ≤ 672 := by
      rcases htrack1 j hj with h | ⟨i, hi, h⟩
      · rw [h]; norm_num
      · rw [h]; exact hE0₂abs i hi
    have heq : charge χ₂ p (E1.P j) = 4 * (charge χ₂ p (E1.P j) / 4) :=
      (Int.mul_ediv_cancel' (hdvd1 j hj)).symm
    rw [heq, abs_mul] at hb
    norm_num at hb
    have hnat : ((charge χ₂ p (E1.P j) / 4).natAbs : ℤ) ≤ 168 := by
      rw [Int.natCast_natAbs]
      omega
    exact_mod_cast hnat
  have hsum1 : ∑ j ∈ E1.lib, (charge χ₂ p (E1.P j) / 4).natAbs ≤ 168 * E1.lib.card := by
    calc
      _ ≤ ∑ _j ∈ E1.lib, 168 := sum_le_sum habs1
      _ = _ := by simp [mul_comm]
  have hlib1R : (E1.lib.card : ℝ) ≤ 16297 * (1224 * rho * n ^ 2) := by
    have : E1.lib.card ≤ 16297 * E0.lib.card := by omega
    have h' : (E1.lib.card : ℝ) ≤ 16297 * (E0.lib.card : ℝ) := by exact_mod_cast this
    nlinarith
  have hBdeg2 : DegBounded (E1.R0 ∪ X) (6 * lamT * n) := by
    have hTdeg := degree_biUnion_of_sum S tok (lamT * n) hextra.2.1
    intro v
    have h := degBounded_union (degBounded_union hR'deg hTdeg) hX v
    rw [hE1R']
    change (incidentLoad (R' ∪ S.biUnion tok ∪ X) v : ℝ) ≤ 6 * lamT * n
    change (incidentLoad (R' ∪ S.biUnion tok ∪ X) v : ℝ) ≤ _ at h
    linarith
  have hn1' : 1 ≤ 2 ^ 13 * rho * n := by nlinarith
  let ExtraC2 : Finset (Tok (JIdx (ℕ × Bool × Fin 3 × Fin 3))) →
      (Tok (JIdx (ℕ × Bool × Fin 3 × Fin 3)) → Finset (Sym2 V)) → Prop :=
    fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      (∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lamT * n) ∧
      ∀ a ∈ S, ∀ e ∈ tok a, InsideE p c k e
  obtain ⟨S2, tok2, E2, hreal2, hextra2, hS2, hE2R, hzero2, hkeep, hsize2, hload2, hlib2⟩ :=
    token_layer E1 hQ1 χ₂ χ p 4 (by norm_num) hdvd1 6 ExtraC2 (by
      intro S hS
      have hsN : S.card ≤ 1512 * E1.lib.card := by omega
      have hsR : (S.card : ℝ) ≤ 1512 * (E1.lib.card : ℝ) := by exact_mod_cast hsN
      have hSbound : (S.card : ℝ) ≤ 2 ^ 22 * (2 ^ 13 * rho) * n ^ 2 := by
        nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
      obtain ⟨tk, h1, h2, h3, h4⟩ := host_charge_tokens_gen2 F χ₂ χ c k Up Um hup hum hup₁ hum₁ p G
        S _ γ lamT (2 ^ 13 * rho) (hs.mono (by norm_num) le_rfl) hBdeg2 hγ1 hlamT hlamTγ
        (by positivity) hscaleT2 hn1' hSbound
      exact ⟨tk, h1, h2, h3, h4⟩)
  have hzero2' : ∀ j ∈ E2.lib, charge χ p (E2.P j) = 0 := hkeep hzero1
  have hE2R' : E2.R0 = E1.R0 ∪ S2.biUnion tok2 := hE2R
  have hT2G : S2.biUnion tok2 ⊆ G.edgeFinset := biUnion_subset.mpr hextra2.1
  have hT2in : ∀ e ∈ S2.biUnion tok2, InsideE p c k e := by
    intro e he
    obtain ⟨a, ha, hea⟩ := mem_biUnion.mp he
    exact hextra2.2.2 a ha e hea
  have hR2G : E2.R0 ⊆ G.edgeFinset := by rw [hE2R']; exact union_subset hR1G hT2G
  have hP2G : ∀ j ∈ E2.lib, E2.P j ⊆ G.edgeFinset := fun j hj =>
    (E2.subP j hj).trans (union_subset hR2G hXG)
  have hP2sub : ∀ j ∈ E2.lib, E2.P j ⊆ X ∪ E2.R0 := fun j hj => by
    rw [union_comm]; exact E2.subP j hj
  have hP2in : ∀ j ∈ E2.lib, ∀ e ∈ E2.P j, InsideE p c k e := by
    intro j hj e he
    rcases mem_union.mp (E2.subP j hj he) with h | h
    · rw [hE2R'] at h
      rcases mem_union.mp h with h | h
      · rw [hE1R'] at h
        rcases mem_union.mp h with h | h
        · exact hR'in e h
        · exact hTin e h
      · exact hT2in e h
    · exact hXin e h
  have hP2div : ∀ j ∈ E2.lib, IsIntDiv p F (E2.P j) := fun j hj =>
    hlat p _ (E2.loopP j hj) (hactG _ (hP2G j hj)) (hP2in j hj) (E2.evenP j hj) (hzero2' j hj)
      (hzero2 j hj)
  have hP2card : ∀ j ∈ E2.lib, (E2.P j).card ≤ 2184 := by
    intro j hj
    rcases hsize2 j hj with h | ⟨i, hi, h⟩
    · omega
    · have hP : (E1.P i).card ≤ 1176 := hP1card i hi
      have hA := habs1 i hi
      have : 6 * (charge χ₂ p (E1.P i) / 4).natAbs ≤ 6 * 168 := Nat.mul_le_mul_left 6 hA
      omega
  have href2 : RefinerAssembly.RefinesReserve (p := p) (F := F) E2.lib E2.P X E2.R0 :=
    E2.refinesReserve (by
      intro L hLX hL
      have hloop := hloopG L (hLX.trans hXG)
      exact ⟨⟨PaddedTrivial.even3_of_isIntDiv hcard p hloop hL, charge_eq_zero_of_isIntDiv hkill hL⟩,
        charge_eq_zero_of_isIntDiv hkill₂ hL⟩)
  -- 6. loads, ledger, count
  set Λ0 : ℝ := 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hΛ0
  have hload0 : ∀ v, ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤ Λ0 := by
    intro v
    have h1 := hsys.sum_physPiece_incidentLoad P indices hPsub wt
      (fun e _ => Nat.le_succ _) v
    have h1' : ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤
        ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by
      exact_mod_cast h1
    have h2 := hinc v
    have h3 := hint v
    linarith
  have hloadE1 : ∀ v, ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) ≤
      Λ0 + 44 * (lamT * n) := by
    intro v
    have h1 : ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) ≤
        ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) +
          44 * ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) := by exact_mod_cast hload1 v
    have h2 := hextra.2.1 v
    have h3 := hload0 v
    linarith
  have hload : ∀ v, ((∑ j ∈ E2.lib, incidentLoad (E2.P j) v : ℕ) : ℝ) ≤
      Λ0 + 88 * (lamT * n) := by
    intro v
    have h1 : ((∑ j ∈ E2.lib, incidentLoad (E2.P j) v : ℕ) : ℝ) ≤
        ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) +
          44 * ((∑ a ∈ S2, incidentLoad (tok2 a) v : ℕ) : ℝ) := by exact_mod_cast hload2 v
    have h2 := hextra2.2.1 v
    have h3 := hloadE1 v
    linarith
  set ρL : ℝ := 2 * rho * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + 2 * (lamT * n)
    with hρL
  have hledger : DegBounded (X ∪ E2.R0) ρL := by
    have hTdeg := degree_biUnion_of_sum S tok (lamT * n) hextra.2.1
    have hTdeg2 := degree_biUnion_of_sum S2 tok2 (lamT * n) hextra2.2.1
    have h := degBounded_union hX (degBounded_union (degBounded_union hR'deg hTdeg) hTdeg2)
    rw [hE2R', hE1R']
    intro v
    have h' := h v
    rw [hρL]
    linarith
  have hdegree : max ρL (δ * n + C) + C * (Λ0 + 88 * (lamT * n)) ≤ 2 * δ * n := by
    have hmax : max ρL (δ * n + C) ≤ δ * n + C :=
      max_le (by rw [hρL, hCR]; linarith [hledgerB]) le_rfl
    rw [hCR] at hmax ⊢
    linarith
  have hcount : 4 * (((X ∪ E2.R0).card : ℝ) + E2.lib.card * C) ≤ (δ * n) * (γ * n) := by
    have hXc := FiniteLibrary.card_le_order_mul_degree X _ hX
    change (X.card : ℝ) ≤ n * (2 * rho * n) at hXc
    have hRc := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    change (R.card : ℝ) ≤ n * (4 * lam * n) at hRc
    have hR'c : (R'.card : ℝ) ≤ 4 * R.card := by
      have : R'.card ≤ ∑ e ∈ R, (physPath x y z e).card := card_biUnion_le
      have h4 : ∑ e ∈ R, (physPath x y z e).card = ∑ _e ∈ R, 4 :=
        sum_congr rfl fun e he => pathEdges_card (ends_ne (hRloop e he)) (hpath e he)
      rw [h4, sum_const, smul_eq_mul] at this
      exact_mod_cast (this.trans (by rw [mul_comm]))
    have hTc : ((S.biUnion tok).card : ℝ) ≤ 6 * S.card := by
      have := hreal.card_biUnion_le (subset_refl S)
      exact_mod_cast this
    have hSc : (S.card : ℝ) ≤ 1512 * E0.lib.card := by
      have : S.card ≤ 1512 * E0.lib.card := by omega
      exact_mod_cast this
    have hT2c : ((S2.biUnion tok2).card : ℝ) ≤ 6 * S2.card := by
      have := hreal2.card_biUnion_le (subset_refl S2)
      exact_mod_cast this
    have hS2c : (S2.card : ℝ) ≤ 1512 * E1.lib.card := by
      have : S2.card ≤ 1512 * E1.lib.card := by omega
      exact_mod_cast this
    have hL1 : (E1.lib.card : ℝ) ≤ 16297 * E0.lib.card := by
      have : E1.lib.card ≤ 16297 * E0.lib.card := by omega
      exact_mod_cast this
    have hL2 : (E2.lib.card : ℝ) ≤ 16297 * E1.lib.card := by
      have : E2.lib.card ≤ 16297 * E1.lib.card := by omega
      exact_mod_cast this
    have hU : ((X ∪ E2.R0).card : ℝ) ≤
        X.card + R'.card + (S.biUnion tok).card + (S2.biUnion tok2).card := by
      rw [hE2R', hE1R']
      have h1 := card_union_le X (R' ∪ S.biUnion tok ∪ S2.biUnion tok2)
      have h2 := card_union_le (R' ∪ S.biUnion tok) (S2.biUnion tok2)
      have h3 := card_union_le R' (S.biUnion tok)
      have : (X ∪ (R' ∪ S.biUnion tok ∪ S2.biUnion tok2)).card ≤
          X.card + R'.card + (S.biUnion tok).card + (S2.biUnion tok2).card := by omega
      exact_mod_cast this
    rw [hCR]
    have hgoal : 4 * (2 * rho + 16 * lam + 2 ^ 38 * rho + 2 ^ 39 * rho * 2 ^ 21) * n ^ 2 ≤
        δ * γ * n ^ 2 := mul_le_mul_of_nonneg_right hcountB (sq_nonneg n)
    have hrn : 0 ≤ rho * n ^ 2 := mul_nonneg hrho.le (sq_nonneg n)
    have hE0 : (0 : ℝ) ≤ E0.lib.card := Nat.cast_nonneg _
    nlinarith
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩ :=
    FiniteLibrary.universal_from_finite_library p F G 2184 C (δ * n) (2 * δ * n)
      (Λ0 + 88 * (lamT * n)) ρL (γ * n) hstep X E2.R0 E2.disjRX hXG hR2G
      hledger hdegree E2.lib E2.P href2 hP2sub hP2card hP2div hload hcount
  exact absorber_insideE hc p G hG k _ X hXG hXin A hAG hAX hAdec hAdeg hAL

theorem componentUniversalCert_of_twoc_walk (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4)
    (k : Fin 4) (hc : CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F) (hwalk : LocalWalk4 F c k)
    (χ χ₂ : Fin 4 → Fin 4 → ℤ) (hχ : ∀ i j, |χ i j| ≤ 2) (hχ₂ : ∀ i j, |χ₂ i j| ≤ 2)
    (hkill : Kills χ F) (hkill₂ : Kills χ₂ F)
    (hlat : TwoChargeInside F c k χ χ₂)
    (hdvd : ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4) (A : Finset (Sym2 W)),
      (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → (∀ e ∈ A, InsideE p c k e) →
        OnePart.Even3 A → (4 : ℤ) ∣ charge χ p A)
    (hdvd₂ : ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4) (A : Finset (Sym2 W)),
      (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → (∀ e ∈ A, InsideE p c k e) →
        OnePart.Even3 A → (4 : ℤ) ∣ charge χ₂ p A)
    (Tp Tm Up Um : Template F c k)
    (hpc : charge χ Tp.L Tp.E = 4) (hmc : charge χ Tm.L Tm.E = -4)
    (hpc₂ : charge χ₂ Tp.L Tp.E = 0) (hmc₂ : charge χ₂ Tm.L Tm.E = 0)
    (hup : charge χ₂ Up.L Up.E = 4) (hum : charge χ₂ Um.L Um.E = -4)
    (hup₁ : charge χ Up.L Up.E = 0) (hum₁ : charge χ Um.L Um.E = 0)
    (B : ℕ) (hB : WitnessBoundK F 2184 B)
    (hord : terminalOrder 2184 B 4 ≤ 2 ^ 21) (hsize : terminalSize 2184 B ≤ 2 ^ 21) :
    ComponentUniversalCert F c k := by
  intro V _ _ p G _ ω hG hs hω hω1 hn X hXG hX hXin
  by_cases hempty : ∀ i, c i ≠ k
  · exact componentUniversalCert_empty F c k hempty V p G ω hG hs hω hω1 hn X hXG hX hXin
  push Not at hempty
  obtain ⟨i0, hi0⟩ := hempty
  have hδ : paddedAbsDelta ω = ω ^ 12 / 2 ^ 63 := by
    unfold paddedAbsDelta paddedKappa; ring
  obtain ⟨hlam, hlam64, hrho, hscale, hn2, hδ0, hQ, hlamT, hlamTω, hscaleT, hpathB, hembed,
    hfixed, htokB, -, -, hcountB, htokB2, hledgerB, hrootB, hscaleT2⟩ := twoc_scales ω (Fintype.card V)
      (paddedAbsDelta ω) (paddedRho ω) (ω * paddedAbsDelta ω / 2 ^ 48)
      (paddedAbsDelta ω * Fintype.card V / 2 ^ 33) (paddedAbsDelta ω / 2 ^ 33) hω hω1 hδ rfl
      rfl rfl rfl hn
  have hW : 64 * (ω * paddedAbsDelta ω / 2 ^ 48) * Fintype.card V ≤
      (Fintype.card {v // c (p v) = k} : ℝ) := by
    have hcl := hs.class_card i0
    have hsub : (univ.filter fun w => p w = i0).card ≤ Fintype.card {v // c (p v) = k} := by
      rw [Fintype.card_subtype]
      exact card_le_card (fun w hw => mem_filter.mpr ⟨mem_univ _,
        by rw [(mem_filter.mp hw).2]; exact hi0⟩)
    have hsubR : ((univ.filter fun w => p w = i0).card : ℝ) ≤
        (Fintype.card {v // c (p v) = k} : ℝ) := by exact_mod_cast hsub
    have hd1 : paddedAbsDelta ω ≤ 1 := by
      rw [hδ]
      have : ω ^ 12 ≤ 1 := pow_le_one₀ hω.le hω1
      have : (0 : ℝ) < 2 ^ 63 := by positivity
      rw [div_le_one this]; linarith
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hδ0' : 0 ≤ paddedAbsDelta ω := hδ0.le
    have h1 : 64 * (ω * paddedAbsDelta ω / 2 ^ 48) ≤ ω := by
      have : ω * paddedAbsDelta ω ≤ ω := mul_le_of_le_one_right hω.le hd1
      have : (0 : ℝ) ≤ ω * paddedAbsDelta ω := by positivity
      nlinarith
    nlinarith
  exact component_budget_twoc_walk F c k hc hcard hthree hwalk χ χ₂ hχ hχ₂ hkill hkill₂ hlat
    Tp Tm Up Um hpc hmc hpc₂ hmc₂ hup hum hup₁ hum₁ B hB hord hsize p G
    (fun A hA hact hin h3 => hdvd p A hA hact hin h3)
    (fun A hA hact hin h3 => hdvd₂ p A hA hact hin h3) ω
    (ω * paddedAbsDelta ω / 2 ^ 48) (paddedRho ω) (paddedAbsDelta ω)
    (paddedAbsDelta ω * Fintype.card V / 2 ^ 33) (paddedAbsDelta ω / 2 ^ 33) hG hs hlam hlam64
    hrho hscale hn hn2 hδ0 hQ hω1 hlamT hlamTω hscaleT hW hpathB hembed hfixed htokB htokB2
    hledgerB hrootB hcountB hscaleT2 X hXG hX hXin

/-- **`UniversalCert` with one component `0` carrying two charges of unit `4`, and `Even3`
components elsewhere.** -/
theorem universalCert_of_twoc_components (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4)
    (hc : CompLabel F c) (hτ : TypesInside F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F)
    (hwalk : ∀ k, LocalWalk4 F c k) (hlat0 : ∀ k, k ≠ c 0 → Even3Inside F c k)
    (χ χ₂ : Fin 4 → Fin 4 → ℤ) (hχ : ∀ i j, |χ i j| ≤ 2) (hχ₂ : ∀ i j, |χ₂ i j| ≤ 2)
    (hkill : Kills χ F) (hkill₂ : Kills χ₂ F)
    (hlat : TwoChargeInside F c (c 0) χ χ₂)
    (hdvd : ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4) (A : Finset (Sym2 W)),
      (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → (∀ e ∈ A, InsideE p c (c 0) e) →
        OnePart.Even3 A → (4 : ℤ) ∣ charge χ p A)
    (hdvd₂ : ∀ {W : Type} [Fintype W] [DecidableEq W] (p : W → Fin 4) (A : Finset (Sym2 W)),
      (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A → (∀ e ∈ A, InsideE p c (c 0) e) →
        OnePart.Even3 A → (4 : ℤ) ∣ charge χ₂ p A)
    (Tp Tm Up Um : Template F c (c 0))
    (hpc : charge χ Tp.L Tp.E = 4) (hmc : charge χ Tm.L Tm.E = -4)
    (hpc₂ : charge χ₂ Tp.L Tp.E = 0) (hmc₂ : charge χ₂ Tm.L Tm.E = 0)
    (hup : charge χ₂ Up.L Up.E = 4) (hum : charge χ₂ Um.L Um.E = -4)
    (hup₁ : charge χ Up.L Up.E = 0) (hum₁ : charge χ Um.L Um.E = 0)
    (B : ℕ) (hB : WitnessBoundK F 2184 B)
    (hord : terminalOrder 2184 B 4 ≤ 2 ^ 21) (hsize : terminalSize 2184 B ≤ 2 ^ 21) :
    UniversalCert F :=
  universalCert_of_components F c hc hτ fun k => by
    by_cases hk : k = c 0
    · subst hk
      exact componentUniversalCert_of_twoc_walk F c (c 0) hc hcard hthree (hwalk _) χ χ₂ hχ hχ₂
        hkill hkill₂ hlat hdvd hdvd₂ Tp Tm Up Um hpc hmc hpc₂ hmc₂ hup hum hup₁ hum₁ B hB hord hsize
    · exact componentUniversalCert_of_even3_walk_kappa F c k hc hcard hthree (hwalk k)
        (hlat0 k hk) B (fun p P hK hdiv => hB p P (hK.trans (by norm_num)) hdiv)
        (by unfold terminalOrder at hord ⊢; omega) (by unfold terminalSize at hsize ⊢; omega)

end PaddedComponents

#print axioms PaddedComponents.host_charge_tokens_gen2
#print axioms PaddedComponents.component_budget_twoc_walk
#print axioms PaddedComponents.universalCert_of_twoc_components
