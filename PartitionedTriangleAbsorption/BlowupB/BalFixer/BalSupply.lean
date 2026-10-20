/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.TokenFacts
public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.ComponentsT

@[expose] public section

/-!
# The physical token supply of the stacked vertex layers

`BalGood` is the invariant on the tokens `U` accumulated after the layers at the roots `D`:
inside the host and the component, disjoint from `R ∪ X0`, vertex loads `≤ θ + g` (plus `gN` at the
treated roots), and `|U| ≤ g N |D|`.

`bal_supply` proves the supply hypothesis `hsup` of `vertex_layers` from rooted templates of charge
`±2` at their root (`BalTemplate`): the tokens of a layer avoid `R ∪ U ∪ X0` and the vertices of
load `> θ`. A guarded supply with margin `a` suffices when
`(m+1) + (2gNn/θ + (m+1)N) + (m+1)(d_{R ∪ X0} + θ + g + 2gN) < a`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t m g : ℕ} {W : Type*} [Fintype W] [DecidableEq W]

/-- A rooted template of root class `r`, signed degree `s` at the root, balanced elsewhere. -/
structure BalTemplate (Allowed : Fin t → Fin t → Prop) (c : Fin t → Fin t) (k : Fin t)
    (σc : Fin t → Fin t → ℤ) (r : Fin t) (T : RootedTemplate t m g) (s : ℤ) (M : ℕ) : Prop where
  root : T.L 0 = r
  proper : ∀ i j, s(i, j) ∈ T.E → Allowed (T.L i) (T.L j)
  inside : ∀ j, c (T.L j) = k
  charge : charge (chiV (σc r)) (relab T.L 0) T.E = s
  bal : ∀ j, j ≠ 0 → vcharge (σc (T.L j)) T.L j T.E = 0
  cardM : M ∣ T.E.card

/-- The invariant of the accumulated tokens. -/
def BalGood (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj] (c : Fin t → Fin t)
    (k : Fin t) (R X0 : Finset (Sym2 W)) (θ : ℝ) (g N : ℕ) (xs0 : List W) (D : List W)
    (U : Finset (Sym2 W)) : Prop :=
  U ⊆ G.edgeFinset ∧ Disjoint U (R ∪ X0) ∧ (∀ e ∈ U, CompT.InsideE p c k e) ∧
    D.Nodup ∧ (∀ y ∈ D, y ∈ xs0) ∧
    (∀ w, (incidentLoad U w : ℝ) ≤ θ + g + (if w ∈ D then (g * N : ℝ) else 0)) ∧
    (U.card : ℝ) ≤ g * N * D.length

theorem balGood_nil (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj] (c : Fin t → Fin t)
    (k : Fin t) (R X0 : Finset (Sym2 W)) (θ : ℝ) (hθ : 0 ≤ θ) (g N : ℕ) (xs0 : List W) :
    BalGood p G c k R X0 θ g N xs0 [] ∅ := by
  refine ⟨empty_subset _, disjoint_empty_left _, by simp, List.nodup_nil, by simp, ?_, by simp⟩
  intro w
  simp only [incidentLoad, filter_empty, card_empty, Nat.cast_zero, List.not_mem_nil, if_false,
    add_zero]
  linarith

/-- **The supply hypothesis of the stacked layers.** -/
theorem bal_supply (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (a : ℝ) (hs : GuardedSupply p G Allowed (m + 1) a)
    (c : Fin t → Fin t) (k : Fin t) (σc : Fin t → Fin t → ℤ) (TP TM : Fin t → RootedTemplate t m g)
    (xs0 : List W) (M : ℕ)
    (hTP : ∀ x ∈ xs0, BalTemplate Allowed c k σc (p x) (TP (p x)) 2 M)
    (hTM : ∀ x ∈ xs0, BalTemplate Allowed c k σc (p x) (TM (p x)) (-2) M)
    (X0 R : Finset (Sym2 W)) (dRX : ℝ) (hRX : DegBounded (R ∪ X0) dRX) (hdRX : 0 ≤ dRX)
    (N : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (hbud : ((m + 1 : ℕ) : ℝ) + (2 * g * N * Fintype.card W / θ + ((m + 1 : ℕ) : ℝ) * N) +
      ((m + 1 : ℕ) : ℝ) * (dRX + θ + g + 2 * g * N) < a) :
    ∀ x ∈ xs0, ∀ (ι : Type) (D : List W) (U : Finset (Sym2 W)), x ∉ D →
      BalGood p G c k R X0 θ g N xs0 D U →
      ∀ S : Finset (Tok ι), S.card ≤ N →
      ∃ tokE, TokReal (chiV (σc (p x))) (fun _ _ => 0) (relab p x) 2 g (R ∪ U ∪ X0) S tokE ∧
        BalGood p G c k R X0 θ g N xs0 (x :: D) (U ∪ S.biUnion tokE) ∧
        (∀ τ ∈ S, ∀ y ∈ xs0, y ≠ x → vcharge (σc (p y)) p y (tokE τ) = 0) ∧
        ∀ τ ∈ S, M ∣ (tokE τ).card := by
  classical
  intro x hx ι D U hxD hG S hS
  obtain ⟨hUG, hUdis, hUin, hDnd, hDsub, hUload, hUcard⟩ := hG
  set n : ℝ := (Fintype.card W : ℝ)
  set r := p x
  have hP := hTP x hx
  have hM := hTM x hx
  -- vertices of high load
  let High : Finset W := univ.filter fun w => θ < (incidentLoad U w : ℝ)
  have hDlen : (D.length : ℝ) ≤ n := by
    show (D.length : ℝ) ≤ (Fintype.card W : ℝ)
    exact_mod_cast hDnd.length_le_card
  have hHigh : (High.card : ℝ) ≤ 2 * g * N * n / θ := by
    have hc := PrivateFamily.card_highLoad_le U θ
    change (High.card : ℝ) * θ ≤ 2 * U.card at hc
    rw [le_div_iff₀ hθ]
    have : (U.card : ℝ) ≤ g * N * n :=
      hUcard.trans (mul_le_mul_of_nonneg_left hDlen (by positivity))
    linarith
  -- the avoided edges
  have hBeq : R ∪ U ∪ X0 = (R ∪ X0) ∪ U := by
    ext e; simp only [mem_union]; tauto
  have hUd : DegBounded U (θ + g + g * N) := by
    intro w
    have h := hUload w
    change (incidentLoad U w : ℝ) ≤ θ + g + g * N
    split_ifs at h <;> linarith [show (0 : ℝ) ≤ g * N by positivity]
  have hB : DegBounded (R ∪ U ∪ X0) (dRX + (θ + g + g * N)) := by
    rw [hBeq]; exact degree_union hRX hUd
  have hSN : (S.card : ℝ) ≤ N := by exact_mod_cast hS
  obtain ⟨f, hf⟩ := rooted_copies p G Allowed (TP r) (TM r) hP.proper hM.proper x
    hP.root.symm hM.root.symm a (dRX + (θ + g + g * N)) hs (R ∪ U ∪ X0) High hB
    (by positivity) S (by
      have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
      have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hSN hm0, mul_le_mul_of_nonneg_left hSN hg0,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSN hg0) hm0])
  set tokE := mappedTok (TP r) (TM r) f with htokE
  have hreal := tokReal_of_rootedCopies (σc r) p G _ High x (TP r) (TM r) S f hf
    hP.charge hM.charge
  have hbal : ∀ τ : Tok ι, ∀ j, j ≠ 0 →
      vcharge (σc ((tmpl (TP r) (TM r) τ).L j)) (tmpl (TP r) (TM r) τ).L j
        (tmpl (TP r) (TM r) τ).E = 0 := by
    intro τ; unfold tmpl; split_ifs
    · exact hP.bal
    · exact hM.bal
  have hinsideT : ∀ τ : Tok ι, ∀ j, c ((tmpl (TP r) (TM r) τ).L j) = k := by
    intro τ; unfold tmpl; split_ifs
    · exact hP.inside
    · exact hM.inside
  have hnewU : Disjoint U (S.biUnion tokE) := by
    have h := hreal.avoid_biUnion (le_refl S)
    exact (h.mono_right (subset_union_left.trans subset_union_left |>.trans
      (by intro e he; simp only [mem_union] at he ⊢; tauto))).symm
  refine ⟨tokE, hreal, ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨hxD, hDnd⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact union_subset hUG (biUnion_subset.mpr hf.subgraph)
  · rw [disjoint_union_left]
    refine ⟨hUdis, ?_⟩
    have h := hreal.avoid_biUnion (le_refl S)
    exact h.mono_right (by intro e he; simp only [mem_union] at he ⊢; tauto)
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hUin e he
    · obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp he
      obtain ⟨e', -, rfl⟩ := mem_image.mp he
      induction e' using Sym2.ind with
      | _ i j =>
        rw [Sym2.map_mk, CompT.insideE_mk, hf.labels τ hτ i, hf.labels τ hτ j]
        exact ⟨hinsideT τ i, hinsideT τ j⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hDsub y hy
  · intro w
    rw [incidentLoad_union_of_disjoint hnewU, incidentLoad_biUnion_eq S tokE hf.disjoint w]
    push_cast
    have hU := hUload w
    by_cases hwx : w = x
    · subst hwx
      have hroot := sum_load_mappedTok_root_le (TP r) (TM r) S f w
      rw [← htokE] at hroot
      have hroot' : (∑ τ ∈ S, (incidentLoad (tokE τ) w : ℝ)) ≤ g * N := by
        have h1 : ∑ τ ∈ S, incidentLoad (tokE τ) w ≤ g * N := hroot.trans (Nat.mul_le_mul_left g hS)
        exact_mod_cast h1
      simp only [hxD, if_false, add_zero] at hU
      simp only [List.mem_cons_self, if_true]
      linarith
    · have hmono : (if w ∈ D then (g * N : ℝ) else 0) ≤ if w ∈ x :: D then (g * N : ℝ) else 0 := by
        by_cases hwD : w ∈ D
        · simp [hwD]
        · simp only [hwD, if_false]
          split_ifs <;> positivity
      by_cases hwH : w ∈ High
      · have hz : ∑ τ ∈ S, incidentLoad (tokE τ) w = 0 :=
          sum_eq_zero fun τ hτ => by
            rw [htokE]
            exact load_mappedTok_of_mem_Z p G _ High x (TP r) (TM r) S f hf w hwH hwx τ hτ
        have hz' : (∑ τ ∈ S, (incidentLoad (tokE τ) w : ℝ)) = 0 := by exact_mod_cast hz
        rw [hz']
        linarith
      · have hlow : (incidentLoad U w : ℝ) ≤ θ :=
          le_of_not_gt fun h => hwH (mem_filter.mpr ⟨mem_univ _, h⟩)
        have h6 := sum_load_mappedTok_le p G _ High x (TP r) (TM r) S f hf w hwx
        rw [← htokE] at h6
        have h6' : (∑ τ ∈ S, (incidentLoad (tokE τ) w : ℝ)) ≤ g := by exact_mod_cast h6
        have : (0 : ℝ) ≤ if w ∈ x :: D then (g * N : ℝ) else 0 := by split_ifs <;> positivity
        linarith
  · have h1 : (U ∪ S.biUnion tokE).card ≤ U.card + (S.biUnion tokE).card := card_union_le _ _
    have h2 := hreal.card_biUnion_le (le_refl S)
    have h1' : ((U ∪ S.biUnion tokE).card : ℝ) ≤ U.card + g * S.card := by
      have : ((U ∪ S.biUnion tokE).card : ℝ) ≤ ((U.card + g * S.card : ℕ) : ℝ) := by
        exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
      push_cast at this
      exact this
    simp only [List.length_cons]
    push_cast
    nlinarith
  · intro τ hτ y _ hyx
    exact vcharge_mappedTok_eq_zero σc p G _ High x (TP r) (TM r) S f hf hbal τ hτ y hyx
  · intro τ hτ
    rw [htokE]
    unfold mappedTok mappedM
    rw [card_image_of_injective _ (Sym2.map.injective (hf.injective τ hτ))]
    unfold tmpl
    split_ifs
    · exact hP.cardM
    · exact hM.cardM

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.bal_supply
