/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalLibrary
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.VertexLayersY
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalSupplyY
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalLibraryChiY
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.ChiTokensM
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.ChiTokens

@[expose] public section

/-!
# The balanced library with one global charge

`bal_library_chi`: the stacked vertex layers with charge-neutral rooted tokens (`vertex_layers_x`,
`bal_supply_x`), then one charge layer for a global class-pair charge `χ` with balanced tokens
(`token_layer_struct`, `host_chi_tokens`). The pieces are integrally divisible
(`isIntDiv_of_bal` with the charge `χ`).
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
/-- **The balanced library with one global charge and charged vertex templates.** -/
theorem bal_library_chi_ym (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (F : Finset (Multiset (Fin t))) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hG : ∀ a b, G.Adj a b → ∃ l, Link F (p a) (p b) l)
    (c : Fin t → Fin t) (k : Fin t) (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t))
    (hloc : LocalSol F σc Bc) (χ : Fin t → Fin t → ℤ)
    (hsol : ∀ u, BalScalarHyp F σc Bc χ u → FinT.CountsInside c k u →
      ∃ w, FinT.LatEq F u w)
    (hkill : ∀ r ∈ Bc, ∀ τ ∈ F, r ∈ τ → ∑ i, σc r i * typeDegVec τ r i = 0)
    (hσodd : ∀ r ∈ Bc, ∀ j, (∃ l, Link F r j l) → Odd (σc r j))
    (hσ1 : ∀ r j, |σc r j| ≤ 1)
    {m g : ℕ} (TP TM : Fin t → RootedTemplate t m g)
    (M : ℕ) (hM3 : M ∣ 3)
    (hTP : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TP r) 2 M)
    (hTM : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TM r) (-2) M)
    (hloc3 : ∀ E : Finset (Sym2 W), (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F p E →
      (∀ e ∈ E, CompT.InsideE p c k e) → (∀ v, Even (incidentLoad E v)) →
      (∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) → M ∣ E.card → 3 ∣ E.card)
    (hkillχ : Kills χ F) (hχ4 : ∀ i j, |χ i j| ≤ 4) (u : ℤ) (hu : 0 < u)
    (hχdvd : ∀ E : Finset (Sym2 W), (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F p E →
      (∀ e ∈ E, CompT.InsideE p c k e) → (∀ v, Even (incidentLoad E v)) →
      (∀ v, p v ∈ Bc → vcharge (σc (p v)) p v E = 0) → M ∣ E.card → u ∣ charge χ p E)
    (cχ : Fin t → ℤ)
    (hχTP : ∀ r ∈ Bc, c r = k → charge χ (TP r).L (TP r).E = cχ r)
    (hχTM : ∀ r ∈ Bc, c r = k → charge χ (TM r).L (TM r).E = -cχ r)
    {mχ : ℕ} (hmχ : mχ + 1 ≤ 12) (Tχp Tχm : TemplateM F c k mχ) (hχp : charge χ Tχp.L Tχp.E = u)
    (hχm : charge χ Tχm.L Tχm.E = -u)
    (hbχp : ∀ j, vcharge (σc (Tχp.L j)) Tχp.L j Tχp.E = 0)
    (hbχm : ∀ j, vcharge (σc (Tχm.L j)) Tχm.L j Tχm.E = 0)
    (hMχp : M ∣ Tχp.E.card) (hMχm : M ∣ Tχm.E.card)
    (a : ℝ) (hs : GuardedSupply p G (fun i j => ∃ l, Link F i j l) (m + 1) a)
    {κ : Type} (X0 : Finset (Sym2 W)) (E0 : PredRefiner κ X0 OnePart.Even3)
    (hX0G : X0 ⊆ G.edgeFinset) (hX0in : ∀ e ∈ X0, CompT.InsideE p c k e)
    (hR0G : E0.R0 ⊆ G.edgeFinset) (hR0in : ∀ e ∈ E0.R0, CompT.InsideE p c k e)
    (hP0 : ∀ i ∈ E0.lib, OnePart.Even3 (E0.P i))
    (S0 : ℕ) (hS0 : 2 ≤ S0) (hsize0 : ∀ i ∈ E0.lib, (E0.P i).card ≤ S0)
    (Λ0 : ℝ) (hload0 : ∀ v, ((∑ i ∈ E0.lib, incidentLoad (E0.P i) v : ℕ) : ℝ) ≤ Λ0)
    (d0 : ℝ) (hd0 : DegBounded (E0.R0 ∪ X0) d0) (hd00 : 0 ≤ d0)
    (N : ℕ) (hN : 9 * Λ0 ≤ N) (θ : ℝ) (hθ : 0 < θ)
    (hbud : ((m + 1 : ℕ) : ℝ) + (2 * g * N * Fintype.card W / θ + ((m + 1 : ℕ) : ℝ) * N) +
      ((m + 1 : ℕ) : ℝ) * (d0 + θ + g + 2 * g * N) < a)
    (Kχ : ℕ) (hKχ : E0.lib.card * (8 * (S0 + g * S0)) ≤ Kχ)
    (ωχ lamT ρT : ℝ) (hsχ : GuardedSupply p G (fun i j => ∃ l, Link F i j l) (mχ + 1) (ωχ * Fintype.card W))
    (hωχ : ωχ ≤ 1) (hlamT : 0 < lamT) (hlamTω : 1024 * lamT ≤ ωχ) (hρT : 0 < ρT)
    (hscT : (2 ^ 32 : ℝ) * ρT ≤ lamT ^ 2) (hnT : 1 ≤ ρT * Fintype.card W)
    (hd6 : d0 + (θ + g + g * N) ≤ 6 * lamT * Fintype.card W)
    (hcχ : 9 * (Kχ : ℝ) ≤ 2 ^ 22 * ρT * (Fintype.card W : ℝ) ^ 2) :
    ∃ (ι : Type) (lib : Finset ι) (P : ι → Finset (Sym2 W)) (R1 : Finset (Sym2 W)),
      RefinerAssembly.RefinesReserve (p := p) (F := F) lib P X0 R1 ∧ Disjoint R1 X0 ∧
      R1 ⊆ G.edgeFinset ∧ (∀ e ∈ R1, CompT.InsideE p c k e) ∧
      (∀ j ∈ lib, P j ⊆ X0 ∪ R1) ∧ (∀ j ∈ lib, IsIntDiv p F (P j)) ∧
      (∀ j ∈ lib, (P j).card ≤ 97 * (S0 + g * S0)) ∧
      (∀ v, ((∑ j ∈ lib, incidentLoad (P j) v : ℕ) : ℝ) ≤
        Λ0 + 44 * (θ + g + g * N) + 44 * (lamT * Fintype.card W)) ∧
      DegBounded (X0 ∪ R1) (d0 + (θ + g + g * N) + lamT * Fintype.card W) ∧
      ((R1.card : ℝ) ≤ E0.R0.card + g * N * Fintype.card W + 108 * Kχ) ∧
      ((lib.card : ℝ) ≤ E0.lib.card + 11 * N * Fintype.card W + 97 * Kχ) := by
  classical
  set n : ℝ := (Fintype.card W : ℝ)
  -- the vertices of the bipartite classes of the component
  set xs0 : List W := (univ.filter fun v => c (p v) = k ∧ p v ∈ Bc).toList with hxs0
  have hxs0nd : xs0.Nodup := Finset.nodup_toList _
  have hmem : ∀ y, y ∈ xs0 ↔ c (p y) = k ∧ p y ∈ Bc := by
    intro y; rw [hxs0, Finset.mem_toList]; simp
  have hlen : (xs0.length : ℝ) ≤ n := by
    show (xs0.length : ℝ) ≤ (Fintype.card W : ℝ)
    exact_mod_cast hxs0nd.length_le_card
  set σ : W → Fin t → ℤ := fun y => σc (p y)
  have hX0loop : ∀ e ∈ X0, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeFinset (hX0G he)
  have hPG : ∀ i ∈ E0.lib, E0.P i ⊆ G.edgeFinset := fun i hi =>
    (E0.subP i hi).trans (union_subset hR0G hX0G)
  have hact : ∀ E ⊆ G.edgeFinset, ActiveEdges F p E := fun E hE a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hE hab))
  -- hypotheses of the stacked layers
  have hsup := bal_supply_y p G (fun i j => ∃ l, Link F i j l) a hs c k σc TP TM xs0 M
    (fun x hx => hTP (p x) ((hmem x).mp hx).2 ((hmem x).mp hx).1)
    (fun x hx => hTM (p x) ((hmem x).mp hx).2 ((hmem x).mp hx).1) χ cχ
    (fun x hx => hχTP (p x) ((hmem x).mp hx).2 ((hmem x).mp hx).1)
    (fun x hx => hχTM (p x) ((hmem x).mp hx).2 ((hmem x).mp hx).1) X0 E0.R0 d0 hd0 hd00 N θ hθ
    hbud
  have hdvd : ∀ i ∈ E0.lib, ∀ y ∈ xs0, (2 : ℤ) ∣ vcharge (σ y) p y (E0.P i) := by
    intro i hi y hy
    apply two_dvd_vcharge _ p y _ (E0.loopP i hi)
    · intro j hj
      obtain ⟨b, hb, hpb⟩ := exists_of_degVec_ne_zero hj
      obtain ⟨l, hl⟩ := hact _ (hPG i hi) y b hb
      exact hσodd (p y) ((hmem y).mp hy).2 j ⟨l, hpb ▸ hl⟩
    · exact (hP0 i hi).2 y
  have hvabs : ∀ i ∈ E0.lib, ∀ y, |vcharge (σ y) p y (E0.P i)| ≤ (incidentLoad (E0.P i) y : ℤ) :=
    fun i hi y => abs_vcharge_le _ (hσ1 (p y)) p y _ (E0.loopP i hi)
  have hNy : ∀ y ∈ xs0, 9 * ∑ i ∈ E0.lib, (vcharge (σ y) p y (E0.P i) / 2).natAbs ≤ N := by
    intro y _
    set Sy := ∑ i ∈ E0.lib, (vcharge (σ y) p y (E0.P i) / 2).natAbs with hSy
    set Ly := ∑ i ∈ E0.lib, incidentLoad (E0.P i) y with hLy
    have h1 : Sy ≤ Ly := sum_le_sum fun i hi => natAbs_half_le _ _ (hvabs i hi y)
    have h1' : (Sy : ℝ) ≤ (Ly : ℝ) := by exact_mod_cast h1
    have h2 : (Ly : ℝ) ≤ Λ0 := hload0 y
    have h3 : ((9 * Sy : ℕ) : ℝ) ≤ N := by
      rw [Nat.cast_mul]
      have : ((9 : ℕ) : ℝ) = 9 := by norm_num
      rw [this]
      linarith
    exact_mod_cast h3
  have hpot : ∀ i ∈ E0.lib, (E0.P i).card +
      g * ∑ y ∈ xs0.toFinset, (vcharge (σ y) p y (E0.P i) / 2).natAbs ≤ S0 + g * S0 := by
    intro i hi
    have h2 : 2 * ∑ y ∈ xs0.toFinset, (vcharge (σ y) p y (E0.P i) / 2).natAbs ≤
        2 * (E0.P i).card := by
      rw [mul_sum]
      calc ∑ y ∈ xs0.toFinset, 2 * (vcharge (σ y) p y (E0.P i) / 2).natAbs
          ≤ ∑ y ∈ xs0.toFinset, incidentLoad (E0.P i) y := sum_le_sum fun y hy =>
            two_natAbs_half_le _ (hdvd i hi y (List.mem_toFinset.mp hy)) _ (hvabs i hi y)
        _ ≤ ∑ y, incidentLoad (E0.P i) y := sum_le_sum_of_subset (subset_univ _)
        _ ≤ 2 * (E0.P i).card := PrivateFamily.sum_incidentLoad_le _
    have h3 := hsize0 i hi
    have : ∑ y ∈ xs0.toFinset, (vcharge (σ y) p y (E0.P i) / 2).natAbs ≤ S0 := by omega
    nlinarith
  -- the stacked layers
  obtain ⟨ι, E1, U, hGood, -, hR1, hz, hsz, h3, hχK1, hl, hlib⟩ :=
    vertex_layers_y hX0loop σ p g N (S0 + g * S0) M (by nlinarith [hS0]) E0.R0
      (fun w => ∑ i ∈ E0.lib, incidentLoad (E0.P i) w) (BalGood p G c k E0.R0 X0 θ g N xs0) xs0
      χ p (fun x => cχ (p x)) E0.lib.card hsup xs0 hxs0nd (fun _ h => h) [] (by simp) (by simp) E0
      ⟨by simp, fun v => by simp [incidentLoad]⟩ ∅ E0.lib.card
      (balGood_nil p G c k E0.R0 X0 θ hθ.le g N xs0) (by rw [union_empty])
      (by simp) hdvd hNy hpot (fun w => by simp) (fun i hi => dvd_trans hM3 (hP0 i hi).1)
      ((sum_le_card_nsmul _ _ 1 fun i _ => by split_ifs <;> simp).trans (by simp))
      le_rfl
  obtain ⟨hUG, hUdis, hUin, hDnd, -, hUload, hUcard⟩ := hGood
  have hR1G : E1.R0 ⊆ G.edgeFinset := by rw [hR1]; exact union_subset hR0G hUG
  have hR1in : ∀ e ∈ E1.R0, CompT.InsideE p c k e := by
    intro e he
    rw [hR1] at he
    rcases mem_union.mp he with h | h
    · exact hR0in e h
    · exact hUin e h
  have hP1sub : ∀ j ∈ E1.lib, E1.P j ⊆ X0 ∪ E1.R0 := fun j hj => by
    rw [union_comm]; exact E1.subP j hj
  have hP1G : ∀ j ∈ E1.lib, E1.P j ⊆ G.edgeFinset := fun j hj =>
    (hP1sub j hj).trans (union_subset hX0G hR1G)
  have hP1in : ∀ j ∈ E1.lib, ∀ e ∈ E1.P j, CompT.InsideE p c k e := by
    intro j hj e he
    rcases mem_union.mp (hP1sub j hj he) with h | h
    · exact hX0in e h
    · exact hR1in e h
  have hUd : ∀ w, (incidentLoad U w : ℝ) ≤ θ + g + g * N := by
    intro w
    have h := hUload w
    split_ifs at h <;> nlinarith [show (0 : ℝ) ≤ g * N by positivity]
  -- signed degrees of the pieces after the vertex layers
  have hbal1 : ∀ j ∈ E1.lib, ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v (E1.P j) = 0 := by
    intro j hj v hv
    by_cases hvk : c (p v) = k
    · exact hz j hj v (Or.inr ((hmem v).mpr ⟨hvk, hv⟩))
    · have h0 : incidentLoad (E1.P j) v = 0 := by
        unfold incidentLoad
        rw [card_eq_zero, filter_eq_empty_iff]
        intro e he hve
        have hin := hP1in j hj e he
        induction e using Sym2.ind with
        | _ a b =>
          rw [CompT.insideE_mk] at hin
          rcases Sym2.mem_iff.mp hve with rfl | rfl
          · exact hvk hin.1
          · exact hvk hin.2
      have := abs_vcharge_le _ (hσ1 (p v)) p v _ (E1.loopP j hj)
      rw [h0] at this
      simpa using this
  -- the charge layer: the charge-token count from the active pieces
  have hχK1' : ∑ j ∈ E1.lib, (charge χ p (E1.P j) / u).natAbs ≤ Kχ := by
    have h1 : ∀ j ∈ E1.lib, (charge χ p (E1.P j) / u).natAbs ≤
        (if charge χ p (E1.P j) = 0 then 0 else 1) * (8 * (S0 + g * S0)) := by
      intro j hj
      split_ifs with h0
      · simp [h0]
      · have hab := abs_charge_le p (fun e => abs_pair_pairVec_le hχ4 p e) (E1.P j)
        have h1 : |charge χ p (E1.P j) / u| ≤ |charge χ p (E1.P j)| := Int.abs_ediv_le_abs _ _
        have h2 : ((charge χ p (E1.P j) / u).natAbs : ℤ) = |charge χ p (E1.P j) / u| :=
          Int.natCast_natAbs _
        have hc : ((E1.P j).card : ℤ) ≤ S0 + g * S0 := by exact_mod_cast hsz j hj
        have : ((charge χ p (E1.P j) / u).natAbs : ℤ) ≤ 1 * (8 * (S0 + g * S0)) := by
          rw [h2]; push_cast; nlinarith
        exact_mod_cast this
    calc ∑ j ∈ E1.lib, (charge χ p (E1.P j) / u).natAbs
        ≤ ∑ j ∈ E1.lib, (if charge χ p (E1.P j) = 0 then 0 else 1) * (8 * (S0 + g * S0)) :=
          sum_le_sum h1
      _ = (∑ j ∈ E1.lib, (if charge χ p (E1.P j) = 0 then 0 else 1)) * (8 * (S0 + g * S0)) := by
          rw [sum_mul]
      _ ≤ E0.lib.card * (8 * (S0 + g * S0)) := Nat.mul_le_mul_right _ hχK1
      _ ≤ Kχ := hKχ
  have hdvdχ : ∀ j ∈ E1.lib, u ∣ charge χ p (E1.P j) := fun j hj =>
    hχdvd _ (E1.loopP j hj) (hact _ (hP1G j hj)) (hP1in j hj) (E1.evenP j hj) (hbal1 j hj) (h3 j hj)
  have hB6 : DegBounded (E1.R0 ∪ X0) (6 * lamT * Fintype.card W) := by
    intro v
    have h1 : incidentLoad (E1.R0 ∪ X0) v ≤ incidentLoad (E0.R0 ∪ X0) v + incidentLoad U v := by
      rw [hR1]
      unfold incidentLoad
      rw [show E0.R0 ∪ U ∪ X0 = (E0.R0 ∪ X0) ∪ U by ext e; simp only [mem_union]; tauto,
        filter_union]
      exact card_union_le _ _
    have h1' : (incidentLoad (E1.R0 ∪ X0) v : ℝ) ≤
        (incidentLoad (E0.R0 ∪ X0) v : ℝ) + (incidentLoad U v : ℝ) := by exact_mod_cast h1
    have h2 := hd0 v
    have h3' := hUd v
    change (incidentLoad (E1.R0 ∪ X0) v : ℝ) ≤ 6 * lamT * Fintype.card W
    change (incidentLoad (E0.R0 ∪ X0) v : ℝ) ≤ d0 at h2
    linarith
  obtain ⟨S, tok, E2, hreal, ⟨hTG, hTload, hTin, hTbal, hTM⟩, hScard, hR2, hzero2, -, -, hload2,
      hlib2, hstruct2⟩ :=
    token_layer_struct E1 ⟨⟨by simp, fun v => by simp [incidentLoad]⟩, fun y _ => by
        simp [vcharge, degVec]⟩ χ (fun _ _ => 0) p u hu.ne' hdvdχ (mχ + 1)
      (fun S tok => (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
        (∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lamT * Fintype.card W) ∧
        (∀ τ ∈ S, ∀ e ∈ tok τ, CompT.InsideE p c k e) ∧
        (∀ τ ∈ S, ∀ y, vcharge (σc (p y)) p y (tok τ) = 0) ∧ (∀ τ ∈ S, M ∣ (tok τ).card))
      (fun S hS => by
        have hS' : (S.card : ℝ) ≤ 2 ^ 22 * ρT * (Fintype.card W : ℝ) ^ 2 := by
          have h1 : S.card ≤ 9 * Kχ := hS.trans (Nat.mul_le_mul_left 9 hχK1')
          have h1' : (S.card : ℝ) ≤ 9 * (Kχ : ℝ) := by exact_mod_cast h1
          linarith
        have hB12 : DegBounded (E1.R0 ∪ X0) (12 * lamT * Fintype.card W) := by
          intro v
          have h0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
          have := hB6 v
          have : 6 * lamT * (Fintype.card W : ℝ) ≤ 12 * lamT * Fintype.card W := by
            have := hlamT.le; nlinarith
          linarith
        obtain ⟨tk, h1, h2, h3, h4, h5, h6⟩ := host_chi_tokens_m mχ hmχ F χ c k Tχp Tχm u hχp hχm σc
          hbχp hbχm M hMχp hMχm p G S (E1.R0 ∪ X0) ωχ lamT ρT hsχ hB12 hωχ hlamT
          hlamTω hρT hscT hnT hS'
        exact ⟨tk, h1, h2, h3, h4, h5, h6⟩)
  have hR2' : E2.R0 = E1.R0 ∪ S.biUnion tok := hR2
  have hTG' : S.biUnion tok ⊆ G.edgeFinset := biUnion_subset.mpr hTG
  have hR2G : E2.R0 ⊆ G.edgeFinset := by rw [hR2']; exact union_subset hR1G hTG'
  have hR2in : ∀ e ∈ E2.R0, CompT.InsideE p c k e := by
    intro e he
    rw [hR2'] at he
    rcases mem_union.mp he with h | h
    · exact hR1in e h
    · obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp h
      exact hTin τ hτ e he
  have hP2sub : ∀ j ∈ E2.lib, E2.P j ⊆ X0 ∪ E2.R0 := fun j hj => by
    rw [union_comm]; exact E2.subP j hj
  have hP2G : ∀ j ∈ E2.lib, E2.P j ⊆ G.edgeFinset := fun j hj =>
    (hP2sub j hj).trans (union_subset hX0G hR2G)
  have hP2in : ∀ j ∈ E2.lib, ∀ e ∈ E2.P j, CompT.InsideE p c k e := by
    intro j hj e he
    rcases mem_union.mp (hP2sub j hj he) with h | h
    · exact hX0in e h
    · exact hR2in e h
  have hOA : ∀ i ∈ E1.lib, E1.P i ⊆ E1.R0 ∪ X0 := fun i hi => E1.subP i hi
  -- the new pieces: balance, size divisibility, size
  have hshape2 : ∀ j ∈ E2.lib,
      (∀ v, p v ∈ Bc → vcharge (σc (p v)) p v (E2.P j) = 0) ∧ M ∣ (E2.P j).card ∧
      (E2.P j).card ≤ 97 * (S0 + g * S0) := by
    intro j hj
    obtain ⟨S1, hS1, h⟩ := hstruct2 j hj
    have hdis : (S1 : Set (Tok ι)).PairwiseDisjoint tok := hreal.disj.subset hS1
    have hT : M ∣ (S1.biUnion tok).card := by
      rw [card_biUnion hdis]
      exact dvd_sum fun τ hτ => hTM τ (hS1 hτ)
    have hB : (2 : ℕ) ≤ S0 + g * S0 := le_trans hS0 (Nat.le_add_right _ _)
    rcases h with ⟨hP, -, hcd⟩ | ⟨i, hi, -, hP, hcd⟩
    · refine ⟨fun v hv => ?_, by rw [hP]; exact hT, by omega⟩
      rw [hP]
      exact (vcharge_shape (σc (p v)) p v hreal hS1 (fun τ hτ => hTbal τ (hS1 hτ) v)
        (O := ∅) (empty_subset _) (by simp)).1
    · refine ⟨fun v hv => ?_, ?_, ?_⟩
      · rw [hP, (vcharge_shape (σc (p v)) p v hreal hS1 (fun τ hτ => hTbal τ (hS1 hτ) v)
          (hOA i hi) (E1.loopP i hi)).2]
        exact hbal1 i hi v hv
      · rw [hP, card_union_of_disjoint ((hreal.avoid_biUnion hS1).mono_right (hOA i hi)).symm]
        exact dvd_add (h3 i hi) hT
      · have hsi := hsz i hi
        have hab := abs_charge_le p (fun e => abs_pair_pairVec_le hχ4 p e) (E1.P i)
        have hna : (charge χ p (E1.P i) / u).natAbs ≤ 8 * (E1.P i).card := by
          have h1 : |charge χ p (E1.P i) / u| ≤ |charge χ p (E1.P i)| := Int.abs_ediv_le_abs _ _
          have h2 : ((charge χ p (E1.P i) / u).natAbs : ℤ) = |charge χ p (E1.P i) / u| :=
            Int.natCast_natAbs _
          have : ((charge χ p (E1.P i) / u).natAbs : ℤ) ≤ 8 * (E1.P i).card := by
            rw [h2]; linarith
          exact_mod_cast this
        have : (E2.P j).card ≤ (E1.P i).card + (mχ + 1) * (8 * (E1.P i).card) :=
          hcd.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (mχ + 1) hna) _)
        have h12 : (mχ + 1) * (8 * (E1.P i).card) ≤ 12 * (8 * (E1.P i).card) :=
          Nat.mul_le_mul_right _ hmχ
        omega
  refine ⟨JIdx ι, E2.lib, E2.P, E2.R0, ?_, E2.disjRX, hR2G, hR2in, hP2sub, ?_,
    fun j hj => (hshape2 j hj).2.2, ?_, ?_, ?_, ?_⟩
  · -- refines every divisible leftover
    apply E2.refinesReserve
    intro L hL hdiv
    have hloop : ∀ e ∈ L, ¬ e.IsDiag := fun e he => hX0loop e (hL he)
    refine ⟨⟨PaddedTrivial.even3_of_isIntDiv hcard p hloop hdiv, fun y hy => ?_⟩,
      charge_eq_zero_of_isIntDiv hkillχ hdiv⟩
    exact vcharge_eq_zero_of_isIntDiv (σ y) y (hkill (p y) ((hmem y).mp hy).2) hdiv
  · -- the pieces are divisible
    intro j hj
    obtain ⟨hbalP, hMP, -⟩ := hshape2 j hj
    exact isIntDiv_of_bal c k hloc hsol (E2.loopP j hj) (hact _ (hP2G j hj)) (hP2in j hj)
      (E2.evenP j hj)
      (hloc3 _ (E2.loopP j hj) (hact _ (hP2G j hj)) (hP2in j hj) (E2.evenP j hj) hbalP hMP)
      hbalP (hzero2 j hj)
  · intro v
    have h := hl v
    have h' : ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) ≤
        ((∑ i ∈ E0.lib, incidentLoad (E0.P i) v : ℕ) : ℝ) + 44 * (incidentLoad U v : ℝ) := by
      exact_mod_cast h
    have h2 : ((∑ j ∈ E2.lib, incidentLoad (E2.P j) v : ℕ) : ℝ) ≤
        ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) +
          44 * ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) := by exact_mod_cast hload2 v
    linarith [hload0 v, hUd v, hTload v]
  · intro v
    rw [hR2', hR1]
    have hXR : X0 ∪ (E0.R0 ∪ U ∪ S.biUnion tok) = ((E0.R0 ∪ X0) ∪ U) ∪ S.biUnion tok := by
      ext e; simp only [mem_union]; tauto
    rw [hXR]
    have hTd : DegBounded (S.biUnion tok) (lamT * Fintype.card W) := by
      intro w
      have := incidentLoad_biUnion_le S tok w
      have h' : (incidentLoad (S.biUnion tok) w : ℝ) ≤
          ((∑ τ ∈ S, incidentLoad (tok τ) w : ℕ) : ℝ) := by exact_mod_cast this
      exact h'.trans (hTload w)
    have h := GuardedTemplates.degree_union (GuardedTemplates.degree_union hd0 (fun w => hUd w)) hTd
    exact h v
  · rw [hR2', hR1]
    have h1 : ((E0.R0 ∪ U ∪ S.biUnion tok).card : ℝ) ≤
        E0.R0.card + U.card + (S.biUnion tok).card := by
      have := card_union_le (E0.R0 ∪ U) (S.biUnion tok)
      have := card_union_le E0.R0 U
      have : (E0.R0 ∪ U ∪ S.biUnion tok).card ≤ E0.R0.card + U.card + (S.biUnion tok).card := by
        omega
      exact_mod_cast this
    have h2 : (U.card : ℝ) ≤ g * N * n := by
      have hr : ((xs0.reverse ++ []).length : ℝ) ≤ n := by simpa using hlen
      exact hUcard.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    have h3' : ((S.biUnion tok).card : ℝ) ≤ 108 * Kχ := by
      have h1 := hreal.card_biUnion_le (le_refl S)
      have h2 : S.card ≤ 9 * Kχ := hScard.trans (Nat.mul_le_mul_left 9 hχK1')
      have h12 : (mχ + 1) * S.card ≤ 12 * S.card := Nat.mul_le_mul_right _ hmχ
      have : (S.biUnion tok).card ≤ 108 * Kχ := by omega
      exact_mod_cast this
    linarith
  · have h1 : (E1.lib.card : ℝ) ≤ E0.lib.card + 11 * N * xs0.length := by exact_mod_cast hlib
    have h2 : (11 * N * xs0.length : ℝ) ≤ 11 * N * n :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    have h3' : (E2.lib.card : ℝ) ≤ E1.lib.card + 97 * Kχ := by
      have : E2.lib.card ≤ E1.lib.card + 97 * Kχ :=
        hlib2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 97 hχK1') _)
      exact_mod_cast this
    linarith

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_library_chi_ym
