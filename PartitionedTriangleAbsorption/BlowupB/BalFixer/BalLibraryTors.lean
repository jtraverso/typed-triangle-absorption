/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalLibraryD
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.TorsTokens

@[expose] public section

/-!
# The balanced library with a torsion layer

`bal_library_tors`: on the even refiner `E0`, first the mod-`q` torsion layer `TorsionQ.torsion_layerQ`
for the value `(charge ψ / g0) mod q` (value-one tokens from one template, `host_tors_tokens`); its pieces
have `g0 q ∣ charge ψ`. Then `bal_library_d` (vertex layers with `ψ`-neutral tokens), whose pieces are
integrally divisible when the congruence `g0 q ∣ ψ` cuts the balanced lattice down to the type lattice.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ} {W : Type} [Fintype W] [DecidableEq W]

set_option maxHeartbeats 4000000 in
/-- **The balanced library with a torsion layer.** -/
theorem bal_library_tors (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (F : Finset (Multiset (Fin t))) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hG : ∀ a b, G.Adj a b → ∃ l, Link F (p a) (p b) l)
    (c : Fin t → Fin t) (k : Fin t) (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t))
    (hloc : LocalSol F σc Bc) (ψ : Fin t → Fin t → ℤ) (g0 : ℤ) (q : ℕ) (hq : 0 < q) (hg0 : 0 < g0)
    (hsol : ∀ u, BalScalarHyp F σc Bc (fun _ _ => 0) u →
      g0 * q ∣ ∑ i, ∑ j, ψ i j * ((if i = j then 2 else 1) * u i j) →
      FinT.CountsInside c k u → ∃ w, FinT.LatEq F u w)
    (hkill : ∀ r ∈ Bc, ∀ τ ∈ F, r ∈ τ → ∑ i, σc r i * typeDegVec τ r i = 0)
    (hσodd : ∀ r ∈ Bc, ∀ j, (∃ l, Link F r j l) → Odd (σc r j))
    (hσ1 : ∀ r j, |σc r j| ≤ 1)
    {m g : ℕ} (TP TM : Fin t → RootedTemplate t m g)
    (M : ℕ) (hM3 : M ∣ 3)
    (hTP : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TP r) 2 M)
    (hTM : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TM r) (-2) M)
    (hψTP : ∀ r ∈ Bc, c r = k → charge ψ (TP r).L (TP r).E = 0)
    (hψTM : ∀ r ∈ Bc, c r = k → charge ψ (TM r).L (TM r).E = 0)
    (hloc3 : ∀ E : Finset (Sym2 W), (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F p E →
      (∀ e ∈ E, CompT.InsideE p c k e) → (∀ v, Even (incidentLoad E v)) →
      (∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) → M ∣ E.card → 3 ∣ E.card)
    (hKm : KillsMod (g0 * q) ψ F)
    (hg0dvd : ∀ E : Finset (Sym2 W), (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F p E →
      (∀ e ∈ E, CompT.InsideE p c k e) → (∀ v, Even (incidentLoad E v)) → 3 ∣ E.card →
      g0 ∣ charge ψ p E)
    (Tq : FinT.Template F c k) (hTq3 : 3 ∣ Tq.E.card) (hTqg : g0 ∣ charge ψ Tq.L Tq.E)
    (hTqv : (charge ψ Tq.L Tq.E / g0) % (q : ℤ) = 1)
    (a : ℝ) (hs : GuardedSupply p G (fun i j => ∃ l, Link F i j l) (m + 1) a)
    {κ : Type} (X0 : Finset (Sym2 W)) (E0 : PredRefiner κ X0 OnePart.Even3)
    (hX0G : X0 ⊆ G.edgeFinset) (hX0in : ∀ e ∈ X0, CompT.InsideE p c k e)
    (hR0G : E0.R0 ⊆ G.edgeFinset) (hR0in : ∀ e ∈ E0.R0, CompT.InsideE p c k e)
    (hP0 : ∀ i ∈ E0.lib, OnePart.Even3 (E0.P i))
    (S0 : ℕ) (hS0 : 2 ≤ S0) (hsize0 : ∀ i ∈ E0.lib, (E0.P i).card ≤ S0)
    (Λ0 : ℝ) (hload0 : ∀ v, ((∑ i ∈ E0.lib, incidentLoad (E0.P i) v : ℕ) : ℝ) ≤ Λ0)
    (d0 : ℝ) (hd0 : DegBounded (E0.R0 ∪ X0) d0) (hd00 : 0 ≤ d0)
    (ωT lamT ρT : ℝ) (hsT : GuardedSupply p G (fun i j => ∃ l, Link F i j l) 6 (ωT * Fintype.card W))
    (hωT : ωT ≤ 1) (hlamT : 0 < lamT) (hlamTω : 1024 * lamT ≤ ωT) (hρT : 0 < ρT)
    (hscT : (2 ^ 32 : ℝ) * ρT ≤ lamT ^ 2) (hnT : 1 ≤ ρT * Fintype.card W)
    (hd6 : d0 ≤ 6 * lamT * Fintype.card W)
    (hcntT : ((q * E0.lib.card : ℕ) : ℝ) ≤ 2 ^ 22 * ρT * (Fintype.card W : ℝ) ^ 2)
    (N : ℕ) (hN : 9 * (q * Λ0 + 4 * q * (lamT * Fintype.card W)) ≤ N) (θ : ℝ) (hθ : 0 < θ)
    (hbud : ((m + 1 : ℕ) : ℝ) + (2 * g * N * Fintype.card W / θ + ((m + 1 : ℕ) : ℝ) * N) +
      ((m + 1 : ℕ) : ℝ) * ((d0 + lamT * Fintype.card W) + θ + g + 2 * g * N) < a) :
    ∃ (ι : Type) (lib : Finset ι) (P : ι → Finset (Sym2 W)) (R1 : Finset (Sym2 W)),
      RefinerAssembly.RefinesReserve (p := p) (F := F) lib P X0 R1 ∧ Disjoint R1 X0 ∧
      R1 ⊆ G.edgeFinset ∧ (∀ e ∈ R1, CompT.InsideE p c k e) ∧
      (∀ j ∈ lib, P j ⊆ X0 ∪ R1) ∧ (∀ j ∈ lib, IsIntDiv p F (P j)) ∧
      (∀ j ∈ lib, (P j).card ≤ (S0 + 3 * q * 6) + g * (S0 + 3 * q * 6)) ∧
      (∀ v, ((∑ j ∈ lib, incidentLoad (P j) v : ℕ) : ℝ) ≤
        (q * Λ0 + 4 * q * (lamT * Fintype.card W)) + 44 * (θ + g + g * N)) ∧
      DegBounded (X0 ∪ R1) ((d0 + lamT * Fintype.card W) + (θ + g + g * N)) ∧
      ((R1.card : ℝ) ≤ E0.R0.card + 6 * (q * E0.lib.card : ℕ) + g * N * Fintype.card W) ∧
      ((lib.card : ℝ) ≤ (2 * q * E0.lib.card : ℕ) + 11 * N * Fintype.card W) := by
  classical
  set n : ℝ := (Fintype.card W : ℝ) with hn
  have hX0loop : ∀ e ∈ X0, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeFinset (hX0G he)
  have hact : ∀ E ⊆ G.edgeFinset, ActiveEdges F p E := fun E hE a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hE hab))
  have hPG0 : ∀ i ∈ E0.lib, E0.P i ⊆ G.edgeFinset := fun i hi =>
    (E0.subP i hi).trans (union_subset hR0G hX0G)
  have hPin0 : ∀ i ∈ E0.lib, ∀ e ∈ E0.P i, CompT.InsideE p c k e := by
    intro i hi e he
    rcases mem_union.mp (E0.subP i hi he) with h | h
    · exact hR0in e h
    · exact hX0in e h
  -- 1. the torsion layer
  have hold : ∀ i ∈ E0.lib, TGood p ψ g0 (E0.P i) := fun i hi =>
    ⟨E0.loopP i hi, (hP0 i hi).2, (hP0 i hi).1,
      hg0dvd _ (E0.loopP i hi) (hact _ (hPG0 i hi)) (hPin0 i hi) (hP0 i hi).2 (hP0 i hi).1⟩
  have hQgood : ∀ L ⊆ X0, OnePart.Even3 L → TGood p ψ g0 L := by
    intro L hL h
    have hloop : ∀ e ∈ L, ¬ e.IsDiag := fun e he => hX0loop e (hL he)
    exact ⟨hloop, h.2, h.1, hg0dvd L hloop (hact L (hL.trans hX0G)) (fun e he => hX0in e (hL he))
      h.2 h.1⟩
  have hB6 : DegBounded (E0.R0 ∪ X0) (6 * lamT * n) := fun v => (hd0 v).trans hd6
  obtain ⟨S, tok, E1, hreal, ⟨hTG, hTload, hTin, hTcard⟩, hScard, hR1, hP1, hlib1, hload1⟩ :=
    TorsionQ.torsion_layerQ hq E0 (tEval p ψ g0 q hq) ⟨by simp, fun v => by simp [incidentLoad]⟩
      hold hQgood (fun A h => h.1) (fun A h => h.2.1) S0 6 hsize0
      (fun S tok => (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
        (∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lamT * n) ∧
        (∀ a ∈ S, ∀ e ∈ tok a, CompT.InsideE p c k e) ∧ (∀ a ∈ S, (tok a).card ≤ 6))
      (fun S hS => by
        have hS' : (S.card : ℝ) ≤ 2 ^ 22 * ρT * n ^ 2 := by
          have : (S.card : ℝ) ≤ ((q * E0.lib.card : ℕ) : ℝ) := by exact_mod_cast hS
          linarith
        obtain ⟨tk, h1, h2, h3, h4, h5⟩ := host_tors_tokens F c k Tq ψ g0 q hq hTq3 hTqg hTqv p G S
          (E0.R0 ∪ X0) ωT lamT ρT hsT hB6 hωT hlamT hlamTω hρT hscT hnT hS'
        exact ⟨tk, h1, h2, ⟨h3, h4, h5, h2⟩⟩)
  have hTd : DegBounded (S.biUnion tok) (lamT * n) := by
    intro w
    have := incidentLoad_biUnion_le S tok w
    have h' : (incidentLoad (S.biUnion tok) w : ℝ) ≤
        ((∑ a ∈ S, incidentLoad (tok a) w : ℕ) : ℝ) := by exact_mod_cast this
    exact h'.trans (hTload w)
  have hR1G : E1.R0 ⊆ G.edgeFinset := by
    rw [hR1]; exact union_subset hR0G (biUnion_subset.mpr hTG)
  have hR1in : ∀ e ∈ E1.R0, CompT.InsideE p c k e := by
    intro e he
    rw [hR1] at he
    rcases mem_union.mp he with h | h
    · exact hR0in e h
    · obtain ⟨a, ha, he⟩ := mem_biUnion.mp h
      exact hTin a ha e he
  have hd1 : DegBounded (E1.R0 ∪ X0) (d0 + lamT * n) := by
    intro v
    rw [hR1, show E0.R0 ∪ S.biUnion tok ∪ X0 = (E0.R0 ∪ X0) ∪ S.biUnion tok by
      ext e; simp only [mem_union]; tauto]
    exact GuardedTemplates.degree_union hd0 hTd v
  have hval0 : ∀ L : Finset (Sym2 W), (tEval p ψ g0 q hq).value L = tval p ψ g0 q L := fun _ => rfl
  -- 2. the vertex layers on the new refiner
  have hlamTn : 0 ≤ lamT * n := by positivity
  obtain ⟨ι, lib, P, R1, href, hdisj, hRG, hRin, hPsub, hdiv, hsize, hload, hdeg, hR1card, hlibcard⟩ :=
    bal_library_d p G F hcard hG c k σc Bc hloc ψ (g0 * q) hsol hkill hσodd hσ1 TP TM M hM3 hTP hTM
      hψTP hψTM hloc3 a hs X0 E1
      ⟨⟨by simp, fun v => by simp [incidentLoad]⟩, (tEval p ψ g0 q hq).empty_value⟩
      (fun L hL hdiv => ⟨PaddedTrivial.even3_of_isIntDiv hcard p (fun e he => hX0loop e (hL he)) hdiv,
        by rw [hval0]; exact tval_eq_zero_of_dvd p ψ hg0.ne' q (dvd_charge_of_isIntDiv hKm hdiv)⟩)
      hX0G hX0in hR1G hR1in (fun i hi => ⟨(hP1 i hi).1.2.2.1, (hP1 i hi).1.2.1⟩)
      (fun i hi => dvd_of_tval_eq_zero p ψ q hq (hP1 i hi).1.2.2.2 (by rw [← hval0]; exact (hP1 i hi).2.1))
      (S0 + 3 * q * 6) (by omega) (fun i hi => (hP1 i hi).2.2)
      (q * Λ0 + 4 * q * (lamT * n))
      (fun v => by
        have h := hload1 v
        have h' : ((∑ i ∈ E1.lib, incidentLoad (E1.P i) v : ℕ) : ℝ) ≤
            (q : ℝ) * ((∑ j ∈ E0.lib, incidentLoad (E0.P j) v : ℕ) : ℝ) +
              4 * q * ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) := by exact_mod_cast h
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
        nlinarith [hload0 v, hTload v])
      (d0 + lamT * n) hd1 (by positivity) N hN θ hθ hbud
  refine ⟨ι, lib, P, R1, href, hdisj, hRG, hRin, hPsub, hdiv, hsize, hload, hdeg, ?_, ?_⟩
  · have h1 : ((E1.R0).card : ℝ) ≤ E0.R0.card + 6 * (q * E0.lib.card : ℕ) := by
      rw [hR1]
      have hb : (S.biUnion tok).card ≤ 6 * S.card := by
        refine card_biUnion_le.trans ?_
        calc ∑ a ∈ S, (tok a).card ≤ ∑ _a ∈ S, 6 := sum_le_sum fun a ha => hTcard a ha
          _ = 6 * S.card := by rw [sum_const, smul_eq_mul, mul_comm]
      have : (E0.R0 ∪ S.biUnion tok).card ≤ E0.R0.card + 6 * (q * E0.lib.card) :=
        (card_union_le _ _).trans (by omega)
      exact_mod_cast this
    linarith
  · have h1 : (E1.lib.card : ℝ) ≤ (2 * q * E0.lib.card : ℕ) := by exact_mod_cast hlib1
    linarith

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_library_tors
