/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalComponent
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalLibraryChiYM
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalComponentChi
public import PartitionedTriangleAbsorption.BlowupB.FinT.ChargeU12
public import PartitionedTriangleAbsorption.BlowupB.CertTerminal.Host

@[expose] public section

/-!
# The component certificate for bipartite links

`component_bal_walk` is the analogue of `FinT.component_budget_charge_walk_U12` for a component whose
classes may have bipartite links: the even refiner and the physical paths are those of the charge
walk; the charge layer is replaced by the stacked vertex layers (`bal_library`); the terminal
absorber is a hypothesis of the shape of `CertTerminal.cert_terminal` (constant `Cter`). All
numerical conditions are explicit hypotheses.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

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
open PartitionedTriangleAbsorption.BlowupB.VertexSplit
open PartitionedTriangleAbsorption.BlowupB.FinT

variable {t : ℕ}

variable {V : Type} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 8000000 in
/-- **The component certificate with bipartite links and one global charge.** -/
theorem component_bal_walk_chi_ym (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hwalk : FinT.LocalWalk F c k)
    (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t)) (hloc : LocalSol F σc Bc)
    (χ : Fin t → Fin t → ℤ)
    (hsol : ∀ u, BalScalarHyp F σc Bc χ u → FinT.CountsInside c k u →
      ∃ w, FinT.LatEq F u w)
    (hkill : ∀ r ∈ Bc, ∀ τ ∈ F, r ∈ τ → ∑ i, σc r i * typeDegVec τ r i = 0)
    (hσodd : ∀ r ∈ Bc, ∀ j, (∃ l, Link F r j l) → Odd (σc r j))
    (hσ1 : ∀ r j, |σc r j| ≤ 1)
    {m g : ℕ} (TP TM : Fin t → RootedTemplate t m g)
    (M : ℕ) (hM3 : M ∣ 3)
    (hTP : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TP r) 2 M)
    (hTM : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TM r) (-2) M)
    (hloc3 : ∀ {W : Type} [Fintype W] [DecidableEq W] (q : W → Fin t) (E : Finset (Sym2 W)),
      (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F q E → (∀ e ∈ E, CompT.InsideE q c k e) →
      (∀ v, Even (incidentLoad E v)) → (∀ v, q v ∈ Bc → vcharge (σc (q v)) q v E = 0) →
      M ∣ E.card → 3 ∣ E.card)
    (hkillχ : Kills χ F) (hχ4 : ∀ i j, |χ i j| ≤ 4) (u : ℤ) (hu : 0 < u)
    (hχdvd : ∀ {W : Type} [Fintype W] [DecidableEq W] (q : W → Fin t) (E : Finset (Sym2 W)),
      (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F q E → (∀ e ∈ E, CompT.InsideE q c k e) →
      (∀ v, Even (incidentLoad E v)) → (∀ v, q v ∈ Bc → vcharge (σc (q v)) q v E = 0) →
      M ∣ E.card → u ∣ charge χ q E)
    (cχ : Fin t → ℤ)
    (hχTP : ∀ r ∈ Bc, c r = k → charge χ (TP r).L (TP r).E = cχ r)
    (hχTM : ∀ r ∈ Bc, c r = k → charge χ (TM r).L (TM r).E = -cχ r)
    {mχ : ℕ} (hmχ : mχ + 1 ≤ 12) (Tχp Tχm : TemplateM F c k mχ) (hχp : charge χ Tχp.L Tχp.E = u)
    (hχm : charge χ Tχm.L Tχm.E = -u)
    (hbχp : ∀ j, vcharge (σc (Tχp.L j)) Tχp.L j Tχp.E = 0)
    (hbχm : ∀ j, vcharge (σc (Tχm.L j)) Tχm.L j Tχm.E = 0)
    (hMχp : M ∣ Tχp.E.card) (hMχm : M ∣ Tχm.E.card)
    (hm : m + 1 ≤ 2 ^ 21)
    (Cter : ℕ) (hterm : TermHyp F (97 * (168 + g * 168)) Cter)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ lam rho δ Q θ lamT ρT : ℝ) (N Kχ : ℕ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (γ * Fintype.card V))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hQ : 0 < Q) (hθ : 0 < θ)
    (hW : 64 * lam * Fintype.card V ≤ (Fintype.card {v // c (p v) = k} : ℝ))
    (hpathB : 3 * (4100 * lam * (Fintype.card V : ℝ) ^ 2) / Q + 3 +
      2 * (2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)) + 2) < γ * Fintype.card V)
    (hNΛ : 9 * (4096 * lam * Fintype.card V + 2 * (Q + (4096 * lam * Fintype.card V + 1))) ≤ N)
    (hbud : ((m + 1 : ℕ) : ℝ) + (2 * g * N * Fintype.card V / θ + ((m + 1 : ℕ) : ℝ) * N) +
      ((m + 1 : ℕ) : ℝ) * ((2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)))) + θ + g + 2 * g * N) < γ * Fintype.card V)
    (hγ1 : γ ≤ 1) (hlamT : 0 < lamT) (hlamTω : 1024 * lamT ≤ γ) (hρT : 0 < ρT)
    (hscT : (2 ^ 32 : ℝ) * ρT ≤ lamT ^ 2) (hnT : 1 ≤ ρT * Fintype.card V)
    (hd6 : (2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)))) + (θ + g + g * N) ≤
        6 * lamT * Fintype.card V)
    (hKχB : ((8 * (168 + g * 168) : ℕ) : ℝ) * (1224 * rho * (Fintype.card V : ℝ) ^ 2) ≤ Kχ)
    (hcχ : 9 * (Kχ : ℝ) ≤ 2 ^ 22 * ρT * (Fintype.card V : ℝ) ^ 2)
    (hembedB : (2 * (97 * (168 + g * 168) : ℕ) + 5 * t : ℝ) + 9 * Cter + 8 * (δ * Fintype.card V) <
      γ * Fintype.card V / 2)
    (hdegB : max ((2 * rho * Fintype.card V + (4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)))) + (θ + g + g * N) + lamT * Fintype.card V)
        (δ * Fintype.card V + (30 * Cter : ℕ)) +
      ((30 * Cter : ℕ) : ℝ) * ((4096 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1))) + 44 * (θ + g + g * N) +
          44 * (lamT * Fintype.card V)) ≤
        2 * δ * Fintype.card V)
    (hcountB : 4 * (2 * rho * (Fintype.card V : ℝ) ^ 2 + 16 * lam * (Fintype.card V : ℝ) ^ 2 +
      g * N * Fintype.card V + 108 * Kχ +
        (1224 * rho * (Fintype.card V : ℝ) ^ 2 + 11 * N * Fintype.card V + 97 * Kχ) *
        ((30 * Cter : ℕ) : ℝ)) ≤ (δ * Fintype.card V) * (γ * Fintype.card V))
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) (hXin : ∀ e ∈ X, CompT.InsideE p c k e) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, CompT.InsideE p c k e) ∧
      HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := le_antisymm (le_of_not_gt h) hn0
    rw [heq, mul_zero] at hn1
    norm_num at hn1
  set Kp : ℕ := 97 * (168 + g * 168) with hKp
  set C30 : ℕ := 30 * Cter with hC30
  -- the private step from the terminal hypothesis
  have hstep : PrivateStep p F G Kp C30 (δ * n) (2 * δ * n) (γ * n) := by
    intro L hL hLc P hPG hmP hdiv
    let High : Finset V := univ.filter fun v => (δ * n) < (incidentLoad L v : ℝ)
    have hHigh : (High.card : ℝ) ≤ γ * n / 2 := by
      have hc := card_highLoad_le L (δ * n)
      change (High.card : ℝ) * (δ * n) ≤ 2 * L.card at hc
      have hδn : 0 < δ * n := by positivity
      nlinarith
    obtain ⟨A, hAG, hAL, -, hAdec, hAPdec, hAcard, hAv, -⟩ :=
      hterm p G (γ * n) (2 * δ * n) L High hG (hs.mono (by norm_num) le_rfl) hL (by positivity)
        (by linarith) P hPG hmP hdiv
    refine ⟨A, hAG, hAL, hAdec, hAPdec, hAcard, ?_⟩
    intro v hv
    rcases hAv v hv with hp | hz
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
  have hP'in : ∀ i ∈ indices, ∀ e ∈ P' i, CompT.InsideE p c k e := by
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
  -- 4. the vertex layers: a library of divisible pieces
  set d0 : ℝ := 2 * rho * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) with hd0def
  have hd0 : DegBounded (E0.R0 ∪ X) d0 := by
    have h := degBounded_union hR'deg hX
    intro v
    have h' := h v
    rw [hd0def]
    change (incidentLoad (R' ∪ X) v : ℝ) ≤ _
    change (incidentLoad (R' ∪ X) v : ℝ) ≤ _ at h'
    linarith
  have hKχ : E0.lib.card * (8 * (168 + g * 168)) ≤ Kχ := by
    have hl0 : (E0.lib.card : ℝ) ≤ 1224 * rho * n ^ 2 := hcardI
    have hK0 : (0 : ℝ) ≤ ((8 * (168 + g * 168) : ℕ) : ℝ) := Nat.cast_nonneg _
    have : ((E0.lib.card * (8 * (168 + g * 168)) : ℕ) : ℝ) ≤ Kχ := by
      rw [Nat.cast_mul]
      nlinarith [mul_le_mul_of_nonneg_left hl0 hK0]
    exact_mod_cast this
  obtain ⟨ι, lib, PP, R1, href1, hR1X, hR1G, hR1in, hPsub1, hPdiv1, hPcard1, hPload1, hledger1,
      hR1card, hlibcard⟩ :=
    bal_library_chi_ym p G F hcard hG c k σc Bc hloc χ hsol hkill hσodd hσ1 TP TM M hM3 hTP hTM
      (fun E => hloc3 p E) hkillχ hχ4 u hu (fun E => hχdvd p E) cχ hχTP hχTM hmχ Tχp Tχm hχp hχm hbχp
      hbχm hMχp hMχm (γ * n)
      (hs.mono hm le_rfl) X E0 hXG hXin hR'G hR'in
      (fun i hi => hsys.physPiece_even3 (hPsub i hi) (hpieces i hi).2.1) 168 (by norm_num) hP'card
      Λ0 hload0 d0 hd0 (by positivity) N hNΛ θ hθ hbud Kχ hKχ γ lamT ρT
      (hs.mono (le_trans hmχ (by norm_num)) le_rfl) hγ1 hlamT hlamTω hρT hscT hnT hd6 hcχ
  -- 5. the finite library
  have hcount : 4 * (((X ∪ R1).card : ℝ) + lib.card * C30) ≤ (δ * n) * (γ * n) := by
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
    have hU : ((X ∪ R1).card : ℝ) ≤ X.card + R1.card := by exact_mod_cast card_union_le _ _
    have hR1c : (R1.card : ℝ) ≤ R'.card + g * N * n + 108 * Kχ := hR1card
    have hl0 : (E0.lib.card : ℝ) ≤ 1224 * rho * n ^ 2 := hcardI
    have hl1 : (lib.card : ℝ) ≤ E0.lib.card + 11 * N * n + 97 * Kχ := hlibcard
    have hC0 : (0 : ℝ) ≤ (C30 : ℝ) := Nat.cast_nonneg _
    have hlibC : (lib.card : ℝ) * C30 ≤ (1224 * rho * n ^ 2 + 11 * N * n + 97 * Kχ) * C30 :=
      mul_le_mul_of_nonneg_right (by linarith) hC0
    have hmain : ((X ∪ R1).card : ℝ) ≤
        2 * rho * n ^ 2 + 16 * lam * n ^ 2 + g * N * n + 108 * Kχ := by
      nlinarith
    have := hcountB
    nlinarith
  have hdegree : max (d0 + (θ + g + g * N) + lamT * n) (δ * n + C30) +
      C30 * (Λ0 + 44 * (θ + g + g * N) + 44 * (lamT * n)) ≤ 2 * δ * n := by
    have h := hdegB
    simpa only [hd0def, hΛ0] using h
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩ :=
    FiniteLibrary.universal_from_finite_library p F G Kp C30 (δ * n) (2 * δ * n)
      (Λ0 + 44 * (θ + g + g * N) + 44 * (lamT * n)) (d0 + (θ + g + g * N) + lamT * n) (γ * n) hstep
      X R1 hR1X hXG hR1G
      hledger1 hdegree lib PP href1 hPsub1 hPcard1 hPdiv1 hPload1 hcount
  exact absorber_insideE hc p G hG k _ X hXG hXin A hAG hAX hAdec hAdeg hAL

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.component_bal_walk_chi_ym
