/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Converse
public import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Universal
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.OrdinaryHost

@[expose] public section

/-!
# Universal `Ftriv` absorbers at the padded scales

Since the lattice of `Ftriv` is trivial (`isIntDiv_Ftriv_iff_even3`), the ordinary universal
refiner `exists_universal_refiner_alpha` (pieces with even degrees, `3 ∣ e`, at most `42` edges)
is already an `Ftriv`-refiner in every host whose edges join allowed class pairs. The ordinary
anti-edge condition follows from guarded supply because any two classes of `Ftriv` have a
common allowed partner (`Ftriv_common`).

The terminal absorbers come from the explicit witness bound `negativeMass ≤ 2 K + 16`
(`Ftriv_bounded_coefficients`) with `K = 42`, hence `B = 100`, terminal order `12016` and
terminal size `36210`, both below `2^21`.

Quantifier order: the constants `2^21` are fixed first; then the host, then the reserve `X`;
then ONE absorber `A` (fixed before `L`); then every integrally divisible `L ⊆ X`.
-/

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12

universe u

theorem Ftriv_terminal_budgets :
    terminalOrder 42 100 4 = 12016 ∧ terminalSize 42 100 = 36210 ∧
    terminalOrder 42 100 4 ≤ 2 ^ 21 ∧ terminalSize 42 100 ≤ 2 ^ 21 := by decide

/-- Terminal absorbers for `Ftriv` pieces with at most 42 edges, with order and size `2^21`. -/
theorem guarded_terminal_Ftriv {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Ftriv i j k) (2 ^ 21) a)
    (hL : DegBounded L d) (hd : 0 ≤ d)
    (hbudget : (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a)
    (P : Finset (Sym2 V)) (hK : P.card ≤ 42) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hdiv : IsIntDiv p Ftriv P) :
    ∃ A : Finset (Sym2 V), TerminalAbsorber p Ftriv G P L Z (2 ^ 21) A := by
  have hq : terminalOrder 42 100 4 ≤ 2 ^ 21 := Ftriv_terminal_budgets.2.2.1
  have hqR : (terminalOrder 42 100 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hq
  have hbudget' : (terminalOrder 42 100 4 : ℝ) + Z.card +
      terminalOrder 42 100 4 * d < a := by
    have hm := mul_le_mul_of_nonneg_right hqR hd
    linarith
  obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass Ftriv Ftriv_card_three Ftriv_three_step
    42 100 (fun pW PW hKW hdivW => Ftriv_bounded_coefficients 42 pW PW hKW hdivW)
    p G a d L Z (hs.mono hq le_rfl) hL hd hbudget' P hK hloop hdiv
  exact ⟨A, { hA with card_le := hA.card_le.trans Ftriv_terminal_budgets.2.2.2 }⟩

/-- The private terminal step for 42-edge `Ftriv` pieces with `2^21` budgets. -/
theorem guarded_privateStep_Ftriv {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (a T D : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Ftriv i j k) (2 ^ 21) a)
    (hD0 : 0 ≤ D) (hT : 0 < T)
    (hbudget : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * D < a / 2) :
    PrivateStep p Ftriv G 42 (2 ^ 21) T D a := by
  intro L hL hLc P hPG hm hdiv
  classical
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ a / 2 := by
    have hc := card_highLoad_le L T
    change (High.card : ℝ) * T ≤ 2 * L.card at hc
    nlinarith
  have hbudget' : (2 ^ 21 : ℝ) + High.card + (2 ^ 21 : ℝ) * D < a := by
    linarith
  have hloop : ∀ e ∈ P, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hPG he)
      intro hd
      exact G.ne_of_adj hxy (by simpa using hd)
  obtain ⟨A, hA⟩ := guarded_terminal_Ftriv p G a D L High hs hL hD0 hbudget' P hm hloop hdiv
  refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
  intro v hv
  rcases hA.vertices v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

/-- **The `Ftriv` refiner** is the ordinary refiner: no typed layer is needed. -/
theorem exists_Ftriv_refiner {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Ftriv (p a) (p b) k)
    (γ lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Ftriv i j k) 2 (γ * Fintype.card V))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hlamγ : 8 * lam ≤ γ) (hrho : 0 < rho)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset (ℕ × Bool × Fin 3 × Fin 3))
      (P : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := p) (F := Ftriv) indices P X R ∧
      (∀ j ∈ indices, P j ⊆ X ∪ R ∧ IsIntDiv p Ftriv (P j) ∧ (P j).card ≤ 42) ∧
      DegBounded R (4 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ indices, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  have hanti : AntiEdgeful OnePart.part1 OnePart.triFam G γ :=
    hs.to_ordinaryAntiEdgeful le_rfl Ftriv_common
  obtain ⟨indices, P, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    exists_universal_refiner_alpha G X hXG lam rho hlam hlam64 hrho hscale hn1 hn2 hX γ
      hlamγ hanti
  refine ⟨indices, P, R, hRG, hRX, ?_, ?_, hRdeg, hcard, hinc⟩
  · intro L hLX hL
    have hloop : ∀ e ∈ L, ¬ e.IsDiag := PaddedF12.loopless_of_host G (hLX.trans hXG)
    exact href L hLX ((OnePart.isIntDiv_part1_iff L hloop).mpr
      (even3_of_isIntDiv Ftriv_card_three p hloop hL))
  · intro j hj
    obtain ⟨hsub, hloop, hev, h3, hcard42⟩ := hpieces j hj
    refine ⟨hsub, isIntDiv_Ftriv_of_even3 p (P j) hloop ?_ ⟨h3, hev⟩, hcard42⟩
    exact PaddedF12.active_of_host p Ftriv G hG (hsub.trans (union_subset hXG hRG))

/-- The universal `Ftriv` absorber with explicit scalar budgets (`S = C = 2^21`). -/
theorem universal_Ftriv_budget_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ lam rho δ : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Ftriv (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Ftriv i j k) (2 ^ 21) (γ * Fintype.card V))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hlamγ : 32 * lam ≤ γ) (hrho : 0 < rho)
    (hscale : 2 ^ 42 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hembed : ((2 ^ 21 : ℕ) : ℝ) + ((2 ^ 21 : ℕ) : ℝ) * (2 * δ * Fintype.card V) <
        γ * Fintype.card V / 2)
    (hfixed : ((2 ^ 21 : ℕ) : ℝ) ≤ δ * Fintype.card V / 4)
    (hledgerScale : 8 * lam + 2 * rho ≤ δ)
    (hrootScale : 4200 * ((2 ^ 21 : ℕ) : ℝ) * lam ≤ δ / 4)
    (hcountScale : 8 * lam + 2 * rho + (2 ^ 35 : ℝ) * ((2 ^ 21 : ℕ) : ℝ) * rho ≤ γ * δ / 4) :
    UniversalAbsorbers p Ftriv G rho δ := by
  classical
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ 21 := ⟨_, rfl⟩
  rw [← hCdef] at hembed hfixed hrootScale hcountScale
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := le_antisymm (le_of_not_gt h) hn0
    change 1 ≤ rho * n at hn1
    rw [heq, mul_zero] at hn1
    norm_num at hn1
  have hs2 : GuardedSupply p G (fun i j => ∃ k, Link Ftriv i j k) 2 (γ * Fintype.card V) :=
    hs.mono (by norm_num) le_rfl
  have hembed' : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n / 2 := by
    rw [hCdef] at hembed
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hembed
  have hstep : PrivateFamily.PrivateStep p Ftriv G 42 C (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    exact guarded_privateStep_Ftriv p G (γ * n) (δ * n) (2 * δ * n) hs (by positivity)
      (by positivity) hembed'
  intro X hXG hX
  have hscale24 : 2 ^ 24 * rho ≤ lam ^ 2 := by nlinarith
  obtain ⟨indices, pieces, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    exists_Ftriv_refiner p G hG γ lam rho hs2 hlam hlam64 (by linarith) hrho hscale24 hn1 hn2
      X hXG hX
  have hledger : DegBounded (X ∪ R) ((8 * lam + 2 * rho) * n) := by
    intro v
    have h := degBounded_union hX hRdeg v
    have hl : 0 ≤ lam * n := mul_nonneg hlam.le hn0
    calc _ ≤ 2 * rho * Fintype.card V + 4 * lam * Fintype.card V := h
      _ ≤ (8 * lam + 2 * rho) * n := by dsimp only [n]; nlinarith
  have hdegree : max ((8 * lam + 2 * rho) * n) (δ * n + C) +
      C * (4200 * lam * n) ≤ 2 * δ * n := by
    have hledgerN := mul_le_mul_of_nonneg_right hledgerScale hn0
    have hrootN := mul_le_mul_of_nonneg_right hrootScale hn0
    have hmax : max ((8 * lam + 2 * rho) * n) (δ * n + C) ≤ δ * n + C :=
      max_le (by linarith) le_rfl
    change (C : ℝ) ≤ δ * n / 4 at hfixed
    have h1 : (C : ℝ) * (4200 * lam * n) = 4200 * C * lam * n := by ring
    have h2 : 0 ≤ δ * n := mul_nonneg hδ.le hn0
    linarith [hmax, hfixed, hrootN, h1, h2]
  have hinc' : ∀ v, ((∑ j ∈ indices, incidentLoad (pieces j) v : ℕ) : ℝ) ≤
      4200 * lam * n := by
    intro v
    have h := hinc v
    have hl : 0 ≤ lam * n := mul_nonneg hlam.le hn0
    change _ ≤ 4096 * lam * n at h
    linarith
  have hcount : 4 * (((X ∪ R).card : ℝ) + indices.card * C) ≤ (δ * n) * (γ * n) := by
    have hLC := FiniteLibrary.card_le_order_mul_degree (X ∪ R) ((8 * lam + 2 * rho) * n) hledger
    have hcard' : (indices.card : ℝ) ≤ 2 ^ 35 * rho * n ^ 2 := by
      have hr : 0 ≤ rho * n ^ 2 := mul_nonneg hrho.le (sq_nonneg n)
      change (indices.card : ℝ) ≤ 1224 * rho * n ^ 2 at hcard
      nlinarith
    have hKC := mul_le_mul_of_nonneg_right hcard' hC0
    change ((X ∪ R).card : ℝ) ≤ n * ((8 * lam + 2 * rho) * n) at hLC
    calc
      _ ≤ 4 * (n * ((8 * lam + 2 * rho) * n) + (2 ^ 35 * rho * n ^ 2) * C) := by
        linarith
      _ = 4 * (8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho) * n ^ 2 := by ring
      _ ≤ 4 * (γ * δ / 4) * n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountScale (by norm_num))
          (sq_nonneg n)
      _ = (δ * n) * (γ * n) := by ring
  exact FiniteLibrary.universal_from_finite_library p Ftriv G 42 C (δ * n) (2 * δ * n)
    (4200 * lam * n) ((8 * lam + 2 * rho) * n) (γ * n) hstep X R hRX hXG hRG
    hledger hdegree indices pieces href (fun i hi => (hpieces i hi).1)
    (fun i hi => (hpieces i hi).2.2) (fun i hi => (hpieces i hi).2.1) hinc' hcount

/-- The uniform version, with the explicit query order and terminal size `2^21`. -/
theorem universal_Ftriv_uniform_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Ftriv (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Ftriv i j k) (2 ^ 21) (γ * Fintype.card V))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hsmall : 64 * (((2 ^ 21 : ℕ) : ℝ) + 1) * δ ≤ γ)
    (hn1 : 1 ≤ refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ * Fintype.card V) :
    UniversalAbsorbers p Ftriv G (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ := by
  obtain ⟨hlam, hlam64, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩ :=
    uniform_scalar_budget ((2 ^ 21 : ℕ) : ℝ) ((2 ^ 21 : ℕ) : ℝ) γ δ (Fintype.card V)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hγ hγ1 hδ hsmall (Nat.cast_nonneg _) hn1
  exact universal_Ftriv_budget_explicit p G γ (refinerLambda ((2 ^ 21 : ℕ) : ℝ) γ δ)
    (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ hG hs hlam hlam64 hlamγ hrho hscale hn1 hn2 hδ
    hembed hfixed hledger hroot hcount

/-- **Certificate 1 for `Ftriv`**: universal absorbers at the padded scales. -/
theorem universalCert_Ftriv : PaddedGeneral.UniversalCert Ftriv := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  have hsmall : 64 * ((((2 ^ 21 : ℕ) : ℝ)) + 1) * paddedAbsDelta ω ≤ ω := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using padded_delta_small hω.le hω1
  have hρ : paddedRho ω ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using paddedRho_le_refiner hω.le
  have hn' : 1 ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) *
      Fintype.card V := hn.trans (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
  exact universalAbsorbers_mono_rho p Ftriv G
    (universal_Ftriv_uniform_explicit p G ω (paddedAbsDelta ω) hG hs hω hω1
      (paddedAbsDelta_pos hω) hsmall hn') hρ

#print axioms guarded_terminal_Ftriv
#print axioms exists_Ftriv_refiner
#print axioms universalCert_Ftriv

end PaddedTrivial
