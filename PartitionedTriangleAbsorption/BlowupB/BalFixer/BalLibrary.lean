/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalInside
public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Lattice

@[expose] public section

/-!
# From an even refiner to a library of divisible pieces (bipartite links)

`bal_library` takes a physical refiner `E0` of a reserve `X0` inside one component, with pieces of
even degrees and `3 ∣ |P|`, and runs the stacked vertex layers (`vertex_layers`) at every vertex of
the bipartite classes of the component, with rooted tokens from the host (`bal_supply`). The new
pieces are integrally divisible (`isIntDiv_of_bal`) and refine every divisible leftover. The output
carries the bounds used by the finite-library assembly: piece sizes, vertex loads, the ledger degree,
the remainder size and the library size.
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

theorem degVec_nonneg' (p : W → Fin t) (E : Finset (Sym2 W)) (x : W) (i : Fin t) :
    0 ≤ degVec p E x i := by
  simp only [degVec, Finset.sum_apply]
  exact sum_nonneg fun e _ => degContrib_nonneg p x e i

theorem abs_vcharge_le (σ : Fin t → ℤ) (hσ : ∀ i, |σ i| ≤ 1) (p : W → Fin t) (x : W)
    (E : Finset (Sym2 W)) (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    |vcharge σ p x E| ≤ (incidentLoad E x : ℤ) := by
  unfold vcharge
  calc |∑ i, σ i * degVec p E x i| ≤ ∑ i, |σ i * degVec p E x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, degVec p E x i := sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (degVec_nonneg' p E x i)]
        have h0 := degVec_nonneg' p E x i
        nlinarith [hσ i, abs_nonneg (σ i)]
    _ = (incidentLoad E x : ℤ) := sum_degVec p E hloop x

theorem natAbs_half_le (v : ℤ) (L : ℕ) (h : |v| ≤ (L : ℤ)) : (v / 2).natAbs ≤ L := by
  have h1 : |v / 2| ≤ |v| := Int.abs_ediv_le_abs v 2
  have h2 : ((v / 2).natAbs : ℤ) = |v / 2| := Int.natCast_natAbs _
  have : ((v / 2).natAbs : ℤ) ≤ L := by rw [h2]; linarith
  exact_mod_cast this

theorem two_natAbs_half_le (v : ℤ) (hv : (2 : ℤ) ∣ v) (L : ℕ) (h : |v| ≤ (L : ℤ)) :
    2 * (v / 2).natAbs ≤ L := by
  obtain ⟨q, rfl⟩ := hv
  rw [Int.mul_ediv_cancel_left q (by norm_num)]
  rw [abs_mul] at h
  norm_num at h
  have h2 : (q.natAbs : ℤ) = |q| := Int.natCast_natAbs q
  have : ((2 * q.natAbs : ℕ) : ℤ) ≤ L := by push_cast; linarith
  exact_mod_cast this

/-- **The balanced library.** -/
theorem bal_library (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (F : Finset (Multiset (Fin t))) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hG : ∀ a b, G.Adj a b → ∃ l, Link F (p a) (p b) l)
    (c : Fin t → Fin t) (k : Fin t) (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t))
    (hloc : LocalSol F σc Bc)
    (hsol : ∀ u, BalScalarHyp F σc Bc (fun _ _ => 0) u → FinT.CountsInside c k u →
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
      ((m + 1 : ℕ) : ℝ) * (d0 + θ + g + 2 * g * N) < a) :
    ∃ (ι : Type) (lib : Finset ι) (P : ι → Finset (Sym2 W)) (R1 : Finset (Sym2 W)),
      RefinerAssembly.RefinesReserve (p := p) (F := F) lib P X0 R1 ∧ Disjoint R1 X0 ∧
      R1 ⊆ G.edgeFinset ∧ (∀ e ∈ R1, CompT.InsideE p c k e) ∧
      (∀ j ∈ lib, P j ⊆ X0 ∪ R1) ∧ (∀ j ∈ lib, IsIntDiv p F (P j)) ∧
      (∀ j ∈ lib, (P j).card ≤ S0 + g * S0) ∧
      (∀ v, ((∑ j ∈ lib, incidentLoad (P j) v : ℕ) : ℝ) ≤ Λ0 + 44 * (θ + g + g * N)) ∧
      DegBounded (X0 ∪ R1) (d0 + (θ + g + g * N)) ∧
      ((R1.card : ℝ) ≤ E0.R0.card + g * N * Fintype.card W) ∧
      ((lib.card : ℝ) ≤ E0.lib.card + 11 * N * Fintype.card W) := by
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
  have hsup := bal_supply p G (fun i j => ∃ l, Link F i j l) a hs c k σc TP TM xs0 M
    (fun x hx => hTP (p x) ((hmem x).mp hx).2 ((hmem x).mp hx).1)
    (fun x hx => hTM (p x) ((hmem x).mp hx).2 ((hmem x).mp hx).1) X0 E0.R0 d0 hd0 hd00 N θ hθ
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
  obtain ⟨ι, E1, U, hGood, -, hR1, hz, hsz, h3, hl, hlib⟩ :=
    vertex_layers hX0loop σ p g N (S0 + g * S0) M (by nlinarith [hS0]) E0.R0
      (fun w => ∑ i ∈ E0.lib, incidentLoad (E0.P i) w) (BalGood p G c k E0.R0 X0 θ g N xs0) xs0
      hsup xs0 hxs0nd (fun _ h => h) [] (by simp) (by simp) E0
      ⟨by simp, fun v => by simp [incidentLoad]⟩ ∅ E0.lib.card
      (balGood_nil p G c k E0.R0 X0 θ hθ.le g N xs0) (by rw [union_empty])
      (by simp) hdvd hNy hpot (fun w => by simp) (fun i hi => dvd_trans hM3 (hP0 i hi).1) le_rfl
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
  refine ⟨ι, E1.lib, E1.P, E1.R0, ?_, E1.disjRX, hR1G, hR1in, hP1sub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- refines every divisible leftover
    apply E1.refinesReserve
    intro L hL hdiv
    have hloop : ∀ e ∈ L, ¬ e.IsDiag := fun e he => hX0loop e (hL he)
    refine ⟨PaddedTrivial.even3_of_isIntDiv hcard p hloop hdiv, fun y hy => ?_⟩
    exact vcharge_eq_zero_of_isIntDiv (σ y) y
      (hkill (p y) ((hmem y).mp hy).2) hdiv
  · -- the pieces are divisible
    intro j hj
    have hbalP : ∀ v, p v ∈ Bc → vcharge (σc (p v)) p v (E1.P j) = 0 := by
      intro v hv
      by_cases hvk : c (p v) = k
      · exact hz j hj v (Or.inr ((hmem v).mpr ⟨hvk, hv⟩))
      · -- no edge of the piece meets `v`
        have h0 : incidentLoad (E1.P j) v = 0 := by
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
    exact isIntDiv_of_bal c k hloc hsol (E1.loopP j hj) (hact _ (hP1G j hj)) (hP1in j hj)
      (E1.evenP j hj)
      (hloc3 _ (E1.loopP j hj) (hact _ (hP1G j hj)) (hP1in j hj) (E1.evenP j hj) hbalP (h3 j hj))
      hbalP (by simp [charge, pair])
  · exact hsz
  · intro v
    have h := hl v
    have h' : ((∑ j ∈ E1.lib, incidentLoad (E1.P j) v : ℕ) : ℝ) ≤
        ((∑ i ∈ E0.lib, incidentLoad (E0.P i) v : ℕ) : ℝ) + 44 * (incidentLoad U v : ℝ) := by
      exact_mod_cast h
    linarith [hload0 v, hUd v]
  · intro v
    rw [hR1]
    have hXR : X0 ∪ (E0.R0 ∪ U) = (E0.R0 ∪ X0) ∪ U := by
      ext e; simp only [mem_union]; tauto
    rw [hXR]
    have h := GuardedTemplates.degree_union hd0 (fun w => hUd w)
    exact h v
  · rw [hR1]
    have h1 : ((E0.R0 ∪ U).card : ℝ) ≤ E0.R0.card + U.card := by
      exact_mod_cast card_union_le _ _
    have h2 : (U.card : ℝ) ≤ g * N * n := by
      have hr : ((xs0.reverse ++ []).length : ℝ) ≤ n := by simpa using hlen
      exact hUcard.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    linarith
  · have h1 : (E1.lib.card : ℝ) ≤ E0.lib.card + 11 * N * xs0.length := by exact_mod_cast hlib
    have h2 : (11 * N * xs0.length : ℝ) ≤ 11 * N * n :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    linarith

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_library
