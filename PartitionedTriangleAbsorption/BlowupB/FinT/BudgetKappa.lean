/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.FinT.Budget
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Terminal
public import PartitionedTriangleAbsorption.BlowupB.Kappa.Collapse

@[expose] public section

/-!
# Aristotle's componentwise universal certificate under `KappaLinks` / `FiveStepLinks`

Copies of `PaddedComponents.component_budget_walk`, `componentUniversalCert_of_even3_walk`,
`universalCert_of_even3_components` with `ThreeStepLinks F` replaced by `KappaLinks F` (its only use
is the terminal absorber, now `guarded_terminal_absorber_of_mass_kappa`), and of
`even3Inside_of_scalar` with the collapse `isIntDiv_iff` replaced by `isIntDiv_iff_five`
(`FiveStepLinks F`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.FinT

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12 PaddedGeneral PaddedNoCommon
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ}

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The component absorber budget** (trivial lattice inside the component, `Walk4` inside). -/
theorem component_budget_walk_kappa (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : PartitionedTriangleAbsorption.BlowupB.Kappa.KappaLinks F)
    (hwalk : FinT.LocalWalk F c k) (hlat : FinT.Even3Inside F c k)
    (B : ℕ) (hB : FinT.WitnessBoundK F 168 B)
    (hord : terminalOrder 168 B t ≤ 2 ^ 21) (hsize : terminalSize 168 B ≤ 2 ^ 21)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ lam rho δ Q : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (γ * Fintype.card V))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hQ : 0 < Q)
    (hW : 64 * lam * Fintype.card V ≤ (Fintype.card {v // c (p v) = k} : ℝ))
    (hpathB : 3 * (4100 * lam * (Fintype.card V : ℝ) ^ 2) / Q + 3 +
      2 * (2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)) + 2) < γ * Fintype.card V)
    (hembed : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * Fintype.card V) < γ * Fintype.card V / 2)
    (hfixed : (2 ^ 21 : ℝ) ≤ δ * Fintype.card V / 4)
    (hledgerB : 2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1)) ≤ δ * Fintype.card V)
    (hrootB : (2 ^ 21 : ℝ) * (4096 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) ≤ δ * Fintype.card V / 2)
    (hcountB : 4 * (2 * rho + 16 * lam + 1224 * rho * 2 ^ 21) ≤ δ * γ)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) (hXin : ∀ e ∈ X, CompT.InsideE p c k e) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, CompT.InsideE p c k e) ∧
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
      ∀ P : Finset (Sym2 V), P.card ≤ 168 → (∀ e ∈ P, ¬ e.IsDiag) → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (2 ^ 21) A := by
    intro a d L Z hsa hL hd hbudget P hK hloop hdiv
    have hqR : (terminalOrder 168 B t : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hord
    have hbudget' : (terminalOrder 168 B t : ℝ) + Z.card + terminalOrder 168 B t * d < a := by
      have hm := mul_le_mul_of_nonneg_right hqR hd
      linarith
    obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass_kappa F hcard hthree 168 B
      (fun pW PW hKW hdivW => hB pW PW hKW hdivW)
      p G a d L Z (hsa.mono hord le_rfl) hL hd hbudget' P hK hloop hdiv
    exact ⟨A, { hA with card_le := hA.card_le.trans hsize }⟩
  have hstep : PrivateStep p F G 168 C (δ * n) (2 * δ * n) (γ * n) := by
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
    rw [← mk_ends e, CompT.insideE_mk] at hin
    exact hwalk _ _ hin.1 hin.2
  obtain ⟨x, y, z, hpath, havoid, hdisj, hint⟩ := PaddedComponents.exists_path_system_local p G _ (γ * n)
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
  have hR'in : ∀ e ∈ R', CompT.InsideE p c k e := by
    intro e he
    obtain ⟨e0, he0, hee0⟩ := mem_biUnion.mp he
    have hin := (hRin e0 he0).1
    rw [← mk_ends e0, CompT.insideE_mk] at hin
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
  have hP'div : ∀ i ∈ indices, IsIntDiv p F (P' i) := by
    intro i hi
    refine hlat p (P' i) (hloopG _ (hP'G i hi)) (hactG _ (hP'G i hi)) (fun e he => ?_)
      (hsys.physPiece_even3 (hPsub i hi) (hpieces i hi).2.1)
    rcases mem_union.mp (hP'sub i hi he) with h | h
    · exact hXin e h
    · exact hR'in e h
  -- loads
  set Λ : ℝ := 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hΛ
  have hload : ∀ v, ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤ Λ := by
    intro v
    have h1 := hsys.sum_physPiece_incidentLoad P indices hPsub wt
      (fun e _ => Nat.le_succ _) v
    have h1' : ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤
        ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by
      exact_mod_cast h1
    have h2 := hinc v
    have h3 := hint v
    linarith
  set ρL : ℝ := 2 * rho * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hρL
  have hledger : DegBounded (X ∪ R') ρL := by
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
    have := degBounded_union hX hR'deg
    rw [hρL, show 2 * rho * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) =
      2 * rho * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) by ring]
    exact this
  have hdegree : max ρL (δ * n + C) + C * Λ ≤ 2 * δ * n := by
    have hmax : max ρL (δ * n + C) ≤ δ * n + C :=
      max_le (by rw [hρL]; linarith [hledgerB]) le_rfl
    rw [hCR] at hmax ⊢
    linarith
  have hcount : 4 * (((X ∪ R').card : ℝ) + indices.card * C) ≤ (δ * n) * (γ * n) := by
    have hXc := FiniteLibrary.card_le_order_mul_degree X _ hX
    have hRc := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    have hR'c : (R'.card : ℝ) ≤ 4 * R.card := by
      have : R'.card ≤ ∑ e ∈ R, (physPath x y z e).card := card_biUnion_le
      have h4 : ∑ e ∈ R, (physPath x y z e).card = ∑ _e ∈ R, 4 :=
        sum_congr rfl fun e he => pathEdges_card (ends_ne (hRloop e he)) (hpath e he)
      rw [h4, sum_const, smul_eq_mul] at this
      exact_mod_cast (this.trans (by rw [mul_comm]))
    have hU : ((X ∪ R').card : ℝ) ≤ X.card + R'.card := by exact_mod_cast card_union_le X R'
    change (X.card : ℝ) ≤ n * (2 * rho * n) at hXc
    change (R.card : ℝ) ≤ n * (4 * lam * n) at hRc
    rw [hCR]
    have hI : (indices.card : ℝ) * 2 ^ 21 ≤ 1224 * rho * n ^ 2 * 2 ^ 21 :=
      mul_le_mul_of_nonneg_right hcardI (by norm_num)
    have hgoal : 4 * (2 * rho + 16 * lam + 1224 * rho * 2 ^ 21) * n ^ 2 ≤ δ * γ * n ^ 2 :=
      mul_le_mul_of_nonneg_right hcountB (sq_nonneg n)
    nlinarith
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩ :=
    FiniteLibrary.universal_from_finite_library p F G 168 C (δ * n) (2 * δ * n)
      Λ ρL (γ * n) hstep X R' hR'X hXG hR'G hledger hdegree indices P' href' hP'sub hP'card
      hP'div hload hcount
  exact absorber_insideE hc p G hG k _ X hXG hXin A hAG hAX hAdec hAdeg hAL



end PartitionedTriangleAbsorption.BlowupB.FinT
