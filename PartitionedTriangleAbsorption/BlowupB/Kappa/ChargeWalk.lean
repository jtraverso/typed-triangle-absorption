/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedCharge.Cert
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Terminal

@[expose] public section

-- Resource budget for elaborating the unchanged universal absorber proof.
set_option maxHeartbeats 1600000

/-!
# Aristotle's one-charge walk certificate under `KappaLinks`

Copies of `PaddedCharge.universal_budget_charge_walk` and `universalCert_of_charge_walk` with
`ThreeStepLinks F` replaced by `KappaLinks F`; the only use of that hypothesis is the terminal
absorber, now `guarded_terminal_absorber_of_mass_kappa`.
-/

namespace PaddedCharge

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12 PaddedGeneral PaddedNoCommon

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The universal absorber budget for a one-charge family with `Walk4`.** -/
theorem universal_budget_charge_walk_kappa (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F)
    (hwalk : Walk4 (fun i j : Fin 4 => ∃ k, Link F i j k))
    (χ : Fin 4 → Fin 4 → ℤ) (hχ : ∀ i j, |χ i j| ≤ 2) (hlat : ChargeLattice F χ)
    (hplus : ActiveEdges F plusLabel triangleSlots) (hminus : ActiveEdges F minusLabel cycleSlots)
    (hpc : charge χ plusLabel triangleSlots = 12) (hmc : charge χ minusLabel cycleSlots = -12)
    (B : ℕ) (hB : WitnessBoundK F 504 B)
    (hord : terminalOrder 504 B 4 ≤ 2 ^ 21) (hsize : terminalSize 504 B ≤ 2 ^ 21)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdvd : ∀ A : Finset (Sym2 V), (∀ e ∈ A, ¬ e.IsDiag) → ActiveEdges F p A →
      OnePart.Even3 A → (12 : ℤ) ∣ charge χ p A)
    (γ lam rho δ Q lamT : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (γ * Fintype.card V))
    (hγ1 : γ ≤ 1)
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hQ : 0 < Q) (hlamT : 0 < lamT) (hlamTγ : 1024 * lamT ≤ γ)
    (hscaleT : (2 ^ 32 : ℝ) * rho ≤ lamT ^ 2)
    (hpathB : 3 * (4100 * lam * (Fintype.card V : ℝ) ^ 2) / Q + 3 +
      2 * (2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)) + 2) < γ * Fintype.card V)
    (hembed : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * Fintype.card V) < γ * Fintype.card V / 2)
    (hfixed : (2 ^ 21 : ℝ) ≤ δ * Fintype.card V / 4)
    (htokB : 2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) ≤ 6 * lamT * Fintype.card V)
    (hledgerB : 2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) + lamT * Fintype.card V ≤
        δ * Fintype.card V)
    (hrootB : (2 ^ 21 : ℝ) * (4096 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1)) + 44 * (lamT * Fintype.card V)) ≤
        δ * Fintype.card V / 2)
    (hcountB : 4 * (2 * rho + 16 * lam + 6 * 2 ^ 20 * rho + 2 ^ 23 * rho * 2 ^ 21) ≤ δ * γ) :
    UniversalAbsorbers p F G rho δ := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ 21 := ⟨_, rfl⟩
  have hCR : (C : ℝ) = 2 ^ 21 := by rw [hCdef]; norm_num
  -- the terminal step for pieces of at most 504 edges
  have hterminal : ∀ (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V),
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a →
      DegBounded L d → 0 ≤ d → (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a →
      ∀ P : Finset (Sym2 V), P.card ≤ 504 → (∀ e ∈ P, ¬ e.IsDiag) → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (2 ^ 21) A := by
    intro a d L Z hsa hL hd hbudget P hK hloop hdiv
    have hqR : (terminalOrder 504 B 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hord
    have hbudget' : (terminalOrder 504 B 4 : ℝ) + Z.card + terminalOrder 504 B 4 * d < a := by
      have hm := mul_le_mul_of_nonneg_right hqR hd
      linarith
    obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass_kappa F hcard hthree 504 B
      (fun pW PW hKW hdivW => hB pW PW hKW hdivW)
      p G a d L Z (hsa.mono hord le_rfl) hL hd hbudget' P hK hloop hdiv
    exact ⟨A, { hA with card_le := hA.card_le.trans hsize }⟩
  have hstep : PrivateStep p F G 504 C (δ * n) (2 * δ * n) (γ * n) := by
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
  intro X hXG hX
  have hloopG : ∀ P ⊆ G.edgeFinset, ∀ e ∈ P, ¬ e.IsDiag :=
    fun P hP e he => G.not_isDiag_of_mem_edgeFinset (hP he)
  have hactG : ∀ P ⊆ G.edgeFinset, ActiveEdges F p P := fun P hP a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hP hab))
  -- 1. the physical ordinary refiner
  obtain ⟨indices, P', R', hR'G, hR'X, href', hP', hR'deg, hR'card, hcardI, hinc'⟩ :=
    exists_physical_refiner p G (fun i j : Fin 4 => ∃ k, Link F i j k) hwalk (γ * n)
      (hs.mono (by norm_num) le_rfl) lam rho Q hlam hlam64 hrho hscale hn1 hn2 hQ hpathB X hXG hX
  let E0 : PredRefiner (ℕ × Bool × Fin 3 × Fin 3) X OnePart.Even3 :=
    { lib := indices
      P := P'
      R0 := R'
      loopP := fun i hi => hloopG _ (hP' i hi).2.1
      evenP := fun i hi => (hP' i hi).2.2.1.2
      subP := fun i hi => by rw [union_comm]; exact (hP' i hi).1
      disjRX := hR'X
      refines := href' }
  have hQ0 : OnePart.Even3 (∅ : Finset (Sym2 V)) :=
    ⟨by simp, fun v => by simp [incidentLoad]⟩
  -- 2. the charge layer with physical tokens
  have hdvd0 : ∀ i ∈ E0.lib, (12 : ℤ) ∣ charge χ p (E0.P i) := fun i hi =>
    hdvd _ (hloopG _ (hP' i hi).2.1) (hactG _ (hP' i hi).2.1) (hP' i hi).2.2.1
  have habs : ∀ i ∈ E0.lib, (charge χ p (E0.P i) / 12).natAbs ≤ 56 := by
    intro i hi
    have hb := abs_charge_le p (fun e => abs_pair_pairVec_le hχ p e) (E0.P i)
    have hc : ((E0.P i).card : ℤ) ≤ 168 := by exact_mod_cast (hP' i hi).2.2.2
    have heq : charge χ p (E0.P i) = 12 * (charge χ p (E0.P i) / 12) :=
      (Int.mul_ediv_cancel' (hdvd0 i hi)).symm
    rw [heq, abs_mul] at hb
    norm_num at hb
    have hnat : ((charge χ p (E0.P i) / 12).natAbs : ℤ) ≤ 56 := by
      rw [Int.natCast_natAbs]
      omega
    exact_mod_cast hnat
  have hsum : ∑ i ∈ E0.lib, (charge χ p (E0.P i) / 12).natAbs ≤ 56 * E0.lib.card := by
    calc
      _ ≤ ∑ _i ∈ E0.lib, 56 := sum_le_sum habs
      _ = _ := by simp [mul_comm]
  have hlibR : (E0.lib.card : ℝ) ≤ 1224 * rho * n ^ 2 := hcardI
  have hBdeg : DegBounded (E0.R0 ∪ X) (6 * lamT * n) := by
    intro v
    have h := degBounded_union hR'deg hX v
    change (incidentLoad (R' ∪ X) v : ℝ) ≤ 6 * lamT * n
    change (incidentLoad (R' ∪ X) v : ℝ) ≤ _ at h
    linarith
  let ExtraC : Finset (Tok (ℕ × Bool × Fin 3 × Fin 3)) →
      (Tok (ℕ × Bool × Fin 3 × Fin 3) → Finset (Sym2 V)) → Prop :=
    fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      ∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lamT * n
  obtain ⟨S, tok, E1, hreal, hextra, hS, hE1R, hzero1, _, hsize1, hload1, hlib1⟩ :=
    token_layer E0 hQ0 χ (fun _ _ => 0) p 12 (by norm_num) hdvd0 6 ExtraC (by
      intro S hS
      have hsN : S.card ≤ 504 * E0.lib.card := by omega
      have hsR : (S.card : ℝ) ≤ 504 * (E0.lib.card : ℝ) := by exact_mod_cast hsN
      have hSbound : (S.card : ℝ) ≤ 2 ^ 22 * rho * n ^ 2 := by
        nlinarith [mul_nonneg hrho.le (sq_nonneg n)]
      exact host_charge_tokens F χ hplus hminus hpc hmc p G S _ γ lamT rho
        (hs.mono (by norm_num) le_rfl) hBdeg hγ1 hlamT hlamTγ hrho hscaleT hn1 hSbound)
  have hE1R' : E1.R0 = R' ∪ S.biUnion tok := hE1R
  have hTG : S.biUnion tok ⊆ G.edgeFinset := biUnion_subset.mpr hextra.1
  have hR1G : E1.R0 ⊆ G.edgeFinset := by rw [hE1R']; exact union_subset hR'G hTG
  have hP1G : ∀ j ∈ E1.lib, E1.P j ⊆ G.edgeFinset := fun j hj =>
    (E1.subP j hj).trans (union_subset hR1G hXG)
  have hP1sub : ∀ j ∈ E1.lib, E1.P j ⊆ X ∪ E1.R0 := fun j hj => by
    rw [union_comm]; exact E1.subP j hj
  have hP1div : ∀ j ∈ E1.lib, IsIntDiv p F (E1.P j) := fun j hj =>
    (hlat p _ (E1.loopP j hj)).mpr ⟨hactG _ (hP1G j hj), E1.evenP j hj, hzero1 j hj⟩
  have hP1card : ∀ j ∈ E1.lib, (E1.P j).card ≤ 504 := by
    intro j hj
    rcases hsize1 j hj with h | ⟨i, hi, h⟩
    · omega
    · have hP : (E0.P i).card ≤ 168 := (hP' i hi).2.2.2
      have hA := habs i hi
      have : 6 * (charge χ p (E0.P i) / 12).natAbs ≤ 6 * 56 := Nat.mul_le_mul_left 6 hA
      omega
  have href1 : RefinerAssembly.RefinesReserve (p := p) (F := F) E1.lib E1.P X E1.R0 :=
    E1.refinesReserve (by
      intro L hLX hL
      have hloop := hloopG L (hLX.trans hXG)
      exact ⟨PaddedTrivial.even3_of_isIntDiv hcard p hloop hL, ((hlat p L hloop).mp hL).2.2⟩)
  -- 3. loads, ledger, count
  set Λ0 : ℝ := 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hΛ0
  have hload : ∀ v, ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) ≤
      Λ0 + 44 * (lamT * n) := by
    intro v
    have h1 : ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) ≤
        ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) +
          44 * ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) := by exact_mod_cast hload1 v
    have h2 := hextra.2 v
    have h3 := hinc' v
    linarith
  set ρL : ℝ := 2 * rho * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) + lamT * n
    with hρL
  have hledger : DegBounded (X ∪ E1.R0) ρL := by
    have hTdeg := degree_biUnion_of_sum S tok (lamT * n) hextra.2
    have h := degBounded_union hX (degBounded_union hR'deg hTdeg)
    rw [hE1R']
    intro v
    have h' := h v
    rw [hρL]
    linarith
  have hdegree : max ρL (δ * n + C) + C * (Λ0 + 44 * (lamT * n)) ≤ 2 * δ * n := by
    have hmax : max ρL (δ * n + C) ≤ δ * n + C :=
      max_le (by rw [hρL, hCR]; linarith [hledgerB]) le_rfl
    rw [hCR] at hmax ⊢
    linarith
  have hcount : 4 * (((X ∪ E1.R0).card : ℝ) + E1.lib.card * C) ≤ (δ * n) * (γ * n) := by
    have hXc := FiniteLibrary.card_le_order_mul_degree X _ hX
    change (X.card : ℝ) ≤ n * (2 * rho * n) at hXc
    have hTc : ((S.biUnion tok).card : ℝ) ≤ 6 * S.card := by
      have := hreal.card_biUnion_le (subset_refl S)
      exact_mod_cast this
    have hSc : (S.card : ℝ) ≤ 504 * E0.lib.card := by
      have : S.card ≤ 504 * E0.lib.card := by omega
      exact_mod_cast this
    have hU : ((X ∪ E1.R0).card : ℝ) ≤ X.card + R'.card + (S.biUnion tok).card := by
      rw [hE1R']
      have h1 := card_union_le X (R' ∪ S.biUnion tok)
      have h2 := card_union_le R' (S.biUnion tok)
      have : (X ∪ (R' ∪ S.biUnion tok)).card ≤ X.card + R'.card + (S.biUnion tok).card := by
        omega
      exact_mod_cast this
    have hL1 : (E1.lib.card : ℝ) ≤ 5433 * E0.lib.card := by
      have : E1.lib.card ≤ 5433 * E0.lib.card := by omega
      exact_mod_cast this
    rw [hCR]
    have hgoal : 4 * (2 * rho + 16 * lam + 6 * 2 ^ 20 * rho + 2 ^ 23 * rho * 2 ^ 21) * n ^ 2 ≤
        δ * γ * n ^ 2 := mul_le_mul_of_nonneg_right hcountB (sq_nonneg n)
    have hrn : 0 ≤ rho * n ^ 2 := mul_nonneg hrho.le (sq_nonneg n)
    nlinarith
  exact FiniteLibrary.universal_from_finite_library p F G 504 C (δ * n) (2 * δ * n)
    (Λ0 + 44 * (lamT * n)) ρL (γ * n) hstep X E1.R0 E1.disjRX hXG hR1G hledger hdegree
    E1.lib E1.P href1 hP1sub hP1card hP1div hload hcount




/-- **`UniversalCert` for one-charge families without common neighbour classes.** For every
family with `ThreeStepLinks`, walks of length four in the allowed-pair graph, a single integral
charge `χ` (`|χ| ≤ 2`) and no torsion (`ChargeLattice F χ`), charges of `Even3` sets divisible by
`12`, the two fixed token templates of charges `±12`, and an explicit witness bound `B` for pieces
of at most `504` edges whose terminal order and size fit into `2^21`. -/
theorem universalCert_of_charge_walk_kappa (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F)
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
  exact universal_budget_charge_walk_kappa F hcard hthree hwalk χ hχ hlat hplus hminus hpc hmc B hB
    hord hsize p G (fun A hA hact h3 => hdvd p A hA hact h3) ω
    (ω * paddedAbsDelta ω / 2 ^ 48) (paddedRho ω) (paddedAbsDelta ω)
    (paddedAbsDelta ω * Fintype.card V / 2 ^ 33) (paddedAbsDelta ω / 2 ^ 33) hG hs hω1
    hlam hlam64 hrho hscale hn hn2 hδ0 hQ hlamT hlamTω hscaleT hpathB hembed hfixed htokB
    hledgerB hrootB hcountB

end PaddedCharge

#print axioms PaddedCharge.universal_budget_charge_walk_kappa
#print axioms PaddedCharge.universalCert_of_charge_walk_kappa
