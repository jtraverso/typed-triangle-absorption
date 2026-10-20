/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Lattice
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.UniversalF12
public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Universal

@[expose] public section

/-!
# A universal Fbit absorber: ordinary refiner + one torsion layer

Same architecture as F† (`PaddedFbit.Universal`): the ordinary refiner
`exists_universal_refiner_alpha` followed directly by `torsion_layer` with `fbitParity`
(`x01 mod 2`) on the domain `FbitGood`. The parity tokens are physical 6-cycles with class sequence
`0,0,1,3,2,0` (one 01-edge). Pieces have at most `42 + 3·6 = 60` edges; terminal absorbers use the
explicit witness bound `8·60 = 480` (order 52564, size 158940, both below `2^21`).
-/

namespace PaddedFbit

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PartitionedTriangleAbsorption.OnePart
open PaddedF12 GuardedTemplates

universe u

theorem fbit_common : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link Fbit a c k) ∧ (∃ k, Link Fbit b c k) := by
  unfold Link Fbit
  decide

/-! ### The torsion token -/

def torsionFbitLabel : Fin 6 → Fin 4 := ![0, 0, 1, 3, 2, 0]

theorem torsion_active_Fbit : ActiveEdges Fbit torsionFbitLabel cycleSlots := by
  unfold ActiveEdges Link; decide

theorem torsion_count_Fbit : unorderedCount torsionFbitLabel cycleSlots 0 1 = 1 := by decide

theorem torsion_Fbit_image {V : Type*} [Fintype V] [DecidableEq V]
    (f : Fin 6 → V) (hf : Function.Injective f)
    (p : V → Fin 4) (hlabel : ∀ w, p (f w) = torsionFbitLabel w) :
    FbitGood p (mapped cycleSlots f) ∧ (fbitParity p).value (mapped cycleSlots f) = 1 := by
  refine ⟨⟨loopless_image f hf cycleSlots cycleSlots_loopless,
    active_image Fbit f p torsionFbitLabel hlabel cycleSlots torsion_active_Fbit,
    even_image f hf cycleSlots cycleSlots_even, ?_⟩, ?_⟩
  · unfold mapped
    rw [card_image_of_injective _ (Sym2.map.injective hf), cycleSlots_card]
    decide
  · change intParity (unorderedCount p (cycleSlots.image (Sym2.map f)) 0 1) = 1
    rw [unorderedCount_image f hf p torsionFbitLabel hlabel, torsion_count_Fbit]
    decide

theorem host_torsion_tokens_Fbit {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset TorsionChain.Atom) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : TorsionChain.Atom → Finset (Sym2 V), ParityTokenReal (fbitParity p) B S tok ∧
      (∀ τ ∈ S, (tok τ).card ≤ 6) ∧ (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V :=
  host_parity_template Fbit p (FbitGood p) (fbitParity p) torsionFbitLabel torsion_active_Fbit
    (fun f hf hp => torsion_Fbit_image f hf p hp) G S B ω lam rho hs hB
    hω hlam hlamω hrho hscale hn1 hcount

/-! ### The shared refiner -/

/-- Ordinary refiner followed by the F† torsion layer: pieces are F†-divisible with at most 60
edges, at most `2^23 rho n^2` pieces, incidence at most `2^14 lam n`. -/
theorem exists_Fbit_refiner {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Fbit (p a) (p b) k)
    (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) 6 (ω * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset TorsionChain.Index) (P : TorsionChain.Index → Finset (Sym2 V))
      (R : Finset (Sym2 V)), R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := p) (F := Fbit) indices P X R ∧
      (∀ i ∈ indices, P i ⊆ X ∪ R ∧ IsIntDiv p Fbit (P i) ∧ (P i).card ≤ 60) ∧
      DegBounded R (6 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 2 ^ 23 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) ≤
        2 ^ 14 * lam * Fintype.card V := by
  classical
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hscale24 : 2 ^ 24 * rho ≤ lam ^ 2 := by nlinarith
  have hlam1 : lam ≤ 1 / 1024 := by linarith
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith
  have hrholam : 2 * rho ≤ lam := by nlinarith
  have hanti : AntiEdgeful part1 triFam G ω :=
    hs.to_ordinaryAntiEdgeful (by norm_num) fbit_common
  have hQ0 : IsIntDiv (part1 : V → Fin 1) triFam ∅ :=
    isIntDiv_of_hasDecomp hasDecomp_empty
  obtain ⟨I0, P0, R0, hR0G, hR0X, href0, hp0, hR0deg, hcard0, hinc0⟩ :=
    exists_universal_refiner_alpha G X hXG lam rho hlam (by linarith) hrho hscale24
      hn1 hn2 hX ω (by linarith) hanti
  let E0 : PredRefiner OrdinaryIndex X (IsIntDiv part1 triFam) :=
    { lib := I0
      P := P0
      R0 := R0
      loopP := fun j hj => (hp0 j hj).2.1
      evenP := fun j hj => (hp0 j hj).2.2.1
      subP := fun j hj => by rw [union_comm]; exact (hp0 j hj).1
      disjRX := hR0X
      refines := href0 }
  have hgood0 : ∀ i ∈ E0.lib, FbitGood p (E0.P i) := by
    intro i hi
    exact ⟨E0.loopP i hi,
      active_of_host p Fbit G hG ((E0.subP i hi).trans (union_subset hR0G hXG)),
      E0.evenP i hi, (hp0 i hi).2.2.2.1⟩
  have hsize0 : ∀ i ∈ E0.lib, (E0.P i).card ≤ 42 := fun i hi => (hp0 i hi).2.2.2.2
  have hledger0 : DegBounded (E0.R0 ∪ X) (6 * lam * Fintype.card V) := by
    intro v
    have h := degBounded_union hR0deg hX v
    have hnum := mul_le_mul_of_nonneg_right hrholam hn0
    change (incidentLoad (R0 ∪ X) v : ℝ) ≤ 4 * lam * n + 2 * rho * n at h
    change (incidentLoad (R0 ∪ X) v : ℝ) ≤ 6 * lam * n
    nlinarith
  have hQgood : ∀ L ⊆ X, IsIntDiv part1 triFam L → FbitGood p L := by
    intro L hLX hL
    have hLG := hLX.trans hXG
    have hloop := loopless_of_host G hLG
    obtain ⟨h3, heven⟩ := (isIntDiv_part1_iff L hloop).mp hL
    exact ⟨hloop, active_of_host p Fbit G hG hLG, heven, h3⟩
  let ExtraP : Finset TorsionChain.Atom → (TorsionChain.Atom → Finset (Sym2 V)) → Prop :=
    fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lam * n
  obtain ⟨SP, tokP, E2, hrealP, hextraP, hSP, hE2R, hpieces2, hlib2, hload2⟩ :=
    torsion_layer E0 (fbitParity p) hQ0 hgood0 hQgood
      (fun A hA => hA.1) (fun A hA => hA.2.2.1) 42 6 hsize0 ExtraP (by
        intro S hS
        have hsR : (S.card : ℝ) ≤ 2 * (I0.card : ℝ) := by exact_mod_cast hS
        have hbound : (S.card : ℝ) ≤ 2 ^ 22 * rho * n ^ 2 := by
          change (I0.card : ℝ) ≤ 1224 * rho * n ^ 2 at hcard0
          nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
        obtain ⟨tok, hreal, hcardT, hsub, hload⟩ :=
          host_torsion_tokens_Fbit p G S _ ω lam rho hs hledger0 hω hlam hlamω hrho hscale hn1
            hbound
        exact ⟨tok, hreal, hcardT, hsub, hload⟩)
  have hR2G : E2.R0 ⊆ G.edgeFinset := by
    rw [hE2R]
    exact union_subset hR0G (biUnion_subset.mpr hextraP.1)
  refine ⟨E2.lib, E2.P, E2.R0, hR2G, E2.disjRX, ?_, ?_, ?_, ?_, ?_⟩
  · apply E2.refinesReserve
    intro L hLX hL
    have hloop := loopless_of_host G (hLX.trans hXG)
    obtain ⟨hgood, hbit⟩ := (isIntDiv_Fbit_iff_good_bit p L hloop).mp hL
    exact ⟨(isIntDiv_part1_iff L hloop).mpr ⟨hgood.2.2.2, hgood.2.2.1⟩, hbit⟩
  · intro i hi
    have hp := hpieces2 i hi
    refine ⟨?_, (isIntDiv_Fbit_iff_good_bit p _ (E2.loopP i hi)).mpr ⟨hp.1, hp.2.1⟩, ?_⟩
    · simpa only [union_comm] using E2.subP i hi
    · have := hp.2.2
      omega
  · rw [hE2R]
    have hTPdegree := degree_biUnion_of_sum SP tokP (lam * n) hextraP.2
    intro v
    have h := degBounded_union hR0deg hTPdegree v
    change (incidentLoad (R0 ∪ SP.biUnion tokP) v : ℝ) ≤ 4 * lam * n + lam * n at h
    change (incidentLoad (R0 ∪ SP.biUnion tokP) v : ℝ) ≤ 6 * lam * n
    have : 0 ≤ lam * n := mul_nonneg hlam.le hn0
    linarith
  · have h2 : (E2.lib.card : ℝ) ≤ 4 * (I0.card : ℝ) := by exact_mod_cast hlib2
    change (I0.card : ℝ) ≤ 1224 * rho * n ^ 2 at hcard0
    change (E2.lib.card : ℝ) ≤ 2 ^ 23 * rho * n ^ 2
    nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
  · intro v
    have h2 : ((∑ i ∈ E2.lib, incidentLoad (E2.P i) v : ℕ) : ℝ) ≤
        2 * ((∑ i ∈ I0, incidentLoad (P0 i) v : ℕ) : ℝ) +
          4 * ((∑ a ∈ SP, incidentLoad (tokP a) v : ℕ) : ℝ) := by exact_mod_cast hload2 v
    have h1 := hinc0 v
    have ht := hextraP.2 v
    change ((∑ i ∈ I0, incidentLoad (P0 i) v : ℕ) : ℝ) ≤ 4096 * lam * n at h1
    change ((∑ i ∈ E2.lib, incidentLoad (E2.P i) v : ℕ) : ℝ) ≤ 2 ^ 14 * lam * n
    have : 0 ≤ lam * n := mul_nonneg hlam.le hn0
    nlinarith

/-! ### Terminal absorbers -/

theorem fbit_terminal_budgets :
    terminalOrder 60 (8 * 60) 4 = 52564 ∧
    terminalSize 60 (8 * 60) = 158940 ∧
    terminalOrder 60 (8 * 60) 4 ≤ 2 ^ 21 ∧
    terminalSize 60 (8 * 60) ≤ 2 ^ 21 := by decide

theorem guarded_terminal_Fbit {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) (2 ^ 21) a)
    (hL : DegBounded L d) (hd : 0 ≤ d)
    (hbudget : (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a)
    (P : Finset (Sym2 V)) (hK : P.card ≤ 60) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hdiv : IsIntDiv p Fbit P) :
    ∃ A : Finset (Sym2 V), TerminalAbsorber p Fbit G P L Z (2 ^ 21) A := by
  have hq : terminalOrder 60 (8 * 60) 4 ≤ 2 ^ 21 := fbit_terminal_budgets.2.2.1
  have hqR : (terminalOrder 60 (8 * 60) 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hq
  have hbudget' : (terminalOrder 60 (8 * 60) 4 : ℝ) + Z.card +
      terminalOrder 60 (8 * 60) 4 * d < a := by
    have hm := mul_le_mul_of_nonneg_right hqR hd
    linarith
  obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass Fbit Fbit_card Fbit_three_step
    60 (8 * 60)
    (fun pW PW hKW hdivW => fbit_bounded_coefficients 60 pW PW hKW hdivW)
    p G a d L Z (hs.mono hq le_rfl) hL hd hbudget' P hK hloop hdiv
  exact ⟨A, { hA with card_le := hA.card_le.trans fbit_terminal_budgets.2.2.2 }⟩

theorem guarded_privateStep_Fbit {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (a T D : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) (2 ^ 21) a)
    (hD0 : 0 ≤ D) (hT : 0 < T)
    (hbudget : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * D < a / 2) :
    PrivateStep p Fbit G 60 (2 ^ 21) T D a := by
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
  obtain ⟨A, hA⟩ := guarded_terminal_Fbit p G a D L High hs hL hD0 hbudget' P hm hloop hdiv
  refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
  intro v hv
  rcases hA.vertices v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

/-! ### Universal absorbers -/

/-- The universal F† absorber with explicit scalar budgets (the F1/F2 budget shape). -/
theorem universal_Fbit_budget {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ lam rho δ : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Fbit (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) (2 ^ 21) (γ * Fintype.card V))
    (hγ1 : γ ≤ 1) (hlam : 0 < lam) (hlamγ : 1024 * lam ≤ γ) (hrho : 0 < rho)
    (hscale : 2 ^ 32 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hembed : ((2 ^ 21 : ℕ) : ℝ) + ((2 ^ 21 : ℕ) : ℝ) * (2 * δ * Fintype.card V) <
      γ * Fintype.card V / 2)
    (hfixed : ((2 ^ 21 : ℕ) : ℝ) ≤ δ * Fintype.card V / 4)
    (hledgerScale : 6 * lam + 2 * rho ≤ δ)
    (hrootScale : (2 ^ 14 : ℝ) * ((2 ^ 21 : ℕ) : ℝ) * lam ≤ δ / 4)
    (hcountScale : 6 * lam + 2 * rho + (2 ^ 23 : ℝ) * ((2 ^ 21 : ℕ) : ℝ) * rho ≤ γ * δ / 4) :
    UniversalAbsorbers p Fbit G rho δ := by
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
  have hs6 : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) 6 (γ * Fintype.card V) :=
    hs.mono (by norm_num) le_rfl
  have hembed' : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n / 2 := by
    rw [hCdef] at hembed
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hembed
  have hstep : PrivateFamily.PrivateStep p Fbit G 60 C (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    exact guarded_privateStep_Fbit p G (γ * n) (δ * n) (2 * δ * n) hs (by positivity)
      (by positivity) hembed'
  intro X hXG hX
  obtain ⟨indices, pieces, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    exists_Fbit_refiner p G hG γ lam rho hs6 hγ1 hlam hlamγ hrho hscale hn1 hn2 X hXG hX
  have hledger : DegBounded (X ∪ R) ((6 * lam + 2 * rho) * n) := by
    have h := degBounded_union hX hRdeg
    convert h using 1
    dsimp [n]
    ring
  have hdegree : max ((6 * lam + 2 * rho) * n) (δ * n + C) +
      C * ((2 ^ 14 : ℝ) * lam * n) ≤ 2 * δ * n := by
    have hledgerN := mul_le_mul_of_nonneg_right hledgerScale hn0
    have hrootN := mul_le_mul_of_nonneg_right hrootScale hn0
    have hmax : max ((6 * lam + 2 * rho) * n) (δ * n + C) ≤ δ * n + C :=
      max_le (by linarith) le_rfl
    change (C : ℝ) ≤ δ * n / 4 at hfixed
    have hrootN' : C * ((2 ^ 14 : ℝ) * lam * n) ≤ δ * n / 4 := by
      convert hrootN using 1 <;> ring
    calc
      _ ≤ δ * n + C + δ * n / 4 := add_le_add hmax hrootN'
      _ ≤ 2 * δ * n := by nlinarith only [hfixed, mul_nonneg hδ.le hn0]
  have hcount : 4 * (((X ∪ R).card : ℝ) + indices.card * C) ≤ (δ * n) * (γ * n) := by
    have hLC := FiniteLibrary.card_le_order_mul_degree (X ∪ R) ((6 * lam + 2 * rho) * n) hledger
    have hKC := mul_le_mul_of_nonneg_right hcard hC0
    change (indices.card : ℝ) * C ≤ (2 ^ 23 * rho * n ^ 2) * C at hKC
    change ((X ∪ R).card : ℝ) ≤ n * ((6 * lam + 2 * rho) * n) at hLC
    calc
      _ ≤ 4 * (n * ((6 * lam + 2 * rho) * n) + (2 ^ 23 * rho * n ^ 2) * C) := by linarith
      _ = 4 * (6 * lam + 2 * rho + (2 ^ 23 : ℝ) * C * rho) * n ^ 2 := by ring
      _ ≤ 4 * (γ * δ / 4) * n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountScale (by norm_num))
          (sq_nonneg n)
      _ = (δ * n) * (γ * n) := by ring
  exact FiniteLibrary.universal_from_finite_library p Fbit G 60 C (δ * n) (2 * δ * n)
    ((2 ^ 14 : ℝ) * lam * n) ((6 * lam + 2 * rho) * n) (γ * n) hstep X R hRX hXG hRG
    hledger hdegree indices pieces href (fun i hi => (hpieces i hi).1)
    (fun i hi => (hpieces i hi).2.2) (fun i hi => (hpieces i hi).2.1) hinc hcount

/-- The uniform version at the refiner scales. -/
theorem universal_Fbit_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (γ δ : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link Fbit (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) (2 ^ 21) (γ * Fintype.card V))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hsmall : 64 * (((2 ^ 21 : ℕ) : ℝ) + 1) * δ ≤ γ)
    (hn1 : 1 ≤ refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ * Fintype.card V) :
    UniversalAbsorbers p Fbit G (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ := by
  obtain ⟨hlam, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩ :=
    uniform_scalar_budget_F12 ((2 ^ 21 : ℕ) : ℝ) ((2 ^ 21 : ℕ) : ℝ) γ δ (Fintype.card V)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hγ hγ1 hδ hsmall (Nat.cast_nonneg _) hn1
  exact universal_Fbit_budget p G γ (refinerLambda ((2 ^ 21 : ℕ) : ℝ) γ δ)
    (refinerRho ((2 ^ 21 : ℕ) : ℝ) γ δ) δ hG hs hγ1 hlam hlamγ hrho hscale hn1 hn2 hδ
    hembed hfixed hledger hroot hcount

/-- **`UniversalCert Fbit`** at the padded scales. -/
theorem universal_simple_Fbit {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link Fbit (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link Fbit i j k) (2 ^ 21) (ω * Fintype.card V))
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 1 ≤ paddedRho ω * Fintype.card V) :
    UniversalAbsorbers p Fbit G (paddedRho ω) (paddedAbsDelta ω) := by
  have hsmall : 64 * ((((2 ^ 21 : ℕ) : ℝ)) + 1) * paddedAbsDelta ω ≤ ω := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using padded_delta_small hω.le hω1
  have hρ : paddedRho ω ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using paddedRho_le_refiner hω.le
  have hn' : 1 ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) *
      Fintype.card V := hn.trans (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
  exact universalAbsorbers_mono_rho p Fbit G
    (universal_Fbit_uniform p G ω (paddedAbsDelta ω) hG hs hω hω1
      (paddedAbsDelta_pos hω) hsmall hn') hρ

#print axioms host_torsion_tokens_Fbit
#print axioms exists_Fbit_refiner
#print axioms universal_simple_Fbit

end PaddedFbit
