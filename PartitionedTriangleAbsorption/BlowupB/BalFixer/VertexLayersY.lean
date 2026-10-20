/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.VertexLayersX

@[expose] public section

/-!
# The stacked vertex layers with charged tokens

`vertex_layers_y` is `vertex_layers` when the tokens of the layer at `x` have charge `± cχ x` (by sign).
A token-only piece has as many plus as minus tokens (zero signed degree at `x`), hence charge `0`.
Invariant: the number of active pieces (nonzero charge, or a nonzero signed degree at a pending vertex)
does not grow; a piece with no charge and no pending signed degree receives no tokens.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {W : Type*} [DecidableEq W]

/-- **The stacked vertex layers, with charged tokens.** -/
theorem vertex_layers_y {X0 : Finset (Sym2 W)} (hX0 : ∀ e ∈ X0, ¬ e.IsDiag)
    (σ : W → Fin t → ℤ) (p : W → Fin t) (g N B M : ℕ) (hB : 2 * g ≤ B)
    (R : Finset (Sym2 W)) (base : W → ℕ) (Good : List W → Finset (Sym2 W) → Prop) (xs0 : List W)
    {tχ : ℕ} (χ : Fin tχ → Fin tχ → ℤ) (qχ : W → Fin tχ) (cχ : W → ℤ) (Kχ : ℕ)
    (hsup : ∀ x ∈ xs0, ∀ (ι : Type) (D : List W) (U : Finset (Sym2 W)), x ∉ D → Good D U →
      ∀ S : Finset (Tok ι), S.card ≤ N →
      ∃ tokE, TokReal (chiV (σ x)) (fun _ _ => 0) (relab p x) 2 g (R ∪ U ∪ X0) S tokE ∧
        Good (x :: D) (U ∪ S.biUnion tokE) ∧
        (∀ τ ∈ S, ∀ y ∈ xs0, y ≠ x → vcharge (σ y) p y (tokE τ) = 0) ∧
        (∀ τ ∈ S, M ∣ (tokE τ).card) ∧
        ∀ τ ∈ S, charge χ qχ (tokE τ) = if τ.sign then cχ x else -cχ x) :
    ∀ (xs : List W), xs.Nodup → (∀ x ∈ xs, x ∈ xs0) →
    ∀ (ds : List W), (∀ y ∈ ds, y ∈ xs0) → (∀ y ∈ ds, y ∉ xs) →
    ∀ {κ : Type} {Q : Finset (Sym2 W) → Prop} (E : PredRefiner κ X0 Q), Q ∅ →
    ∀ (U : Finset (Sym2 W)) (L0 : ℕ), Good ds U → E.R0 = R ∪ U →
    (∀ i ∈ E.lib, ∀ y ∈ ds, vcharge (σ y) p y (E.P i) = 0) →
    (∀ i ∈ E.lib, ∀ y ∈ xs, (2 : ℤ) ∣ vcharge (σ y) p y (E.P i)) →
    (∀ y ∈ xs, 9 * ∑ i ∈ E.lib, (vcharge (σ y) p y (E.P i) / 2).natAbs ≤ N) →
    (∀ i ∈ E.lib, (E.P i).card +
      g * ∑ y ∈ xs.toFinset, (vcharge (σ y) p y (E.P i) / 2).natAbs ≤ B) →
    (∀ w, ∑ i ∈ E.lib, incidentLoad (E.P i) w ≤ base w + 44 * incidentLoad U w) →
    (∀ i ∈ E.lib, M ∣ (E.P i).card) →
    ∑ i ∈ E.lib, (if charge χ qχ (E.P i) = 0 ∧ ∀ y ∈ xs, vcharge (σ y) p y (E.P i) = 0
      then 0 else 1) ≤ Kχ →
    E.lib.card ≤ L0 →
    ∃ (ι : Type) (E' : PredRefiner ι X0 (fun L => Q L ∧ ∀ y ∈ xs, vcharge (σ y) p y L = 0))
      (U' : Finset (Sym2 W)),
      Good (xs.reverse ++ ds) U' ∧ U ⊆ U' ∧ E'.R0 = R ∪ U' ∧
      (∀ j ∈ E'.lib, ∀ y, (y ∈ ds ∨ y ∈ xs) → vcharge (σ y) p y (E'.P j) = 0) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ B) ∧ (∀ j ∈ E'.lib, M ∣ (E'.P j).card) ∧
      ∑ j ∈ E'.lib, (if charge χ qχ (E'.P j) = 0 then 0 else 1) ≤ Kχ ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤ base w + 44 * incidentLoad U' w) ∧
      E'.lib.card ≤ L0 + 11 * N * xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro _ _ ds _ _ κ Q E _ U L0 hG hR0 hds _ _ hpot hload h3P hχK hlib
    refine ⟨κ, E.mono (fun L _ h => h.1), U, by simpa using hG, le_rfl, hR0, ?_, ?_, h3P,
      le_trans (sum_le_sum fun i _ => by
        show (if charge χ qχ (E.P i) = 0 then 0 else 1) ≤ _
        by_cases h : charge χ qχ (E.P i) = 0 <;> simp [h]) hχK, hload, ?_⟩
    · intro j hj y hy
      rcases hy with hy | hy
      · exact hds j hj y hy
      · simp at hy
    · intro j hj
      have := hpot j hj
      simp only [List.toFinset_nil, sum_empty, mul_zero, add_zero] at this
      exact this
    · show E.lib.card ≤ L0 + 11 * N * 0
      simpa using hlib
  | cons x xs ih =>
    intro hnd hxs0 ds hds0 hdsx κ Q E hQ0 U L0 hG hR0 hds hdvd hN hpot hload h3P hχK hlib
    have hx0 : x ∈ xs0 := hxs0 x List.mem_cons_self
    have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    -- the layer at `x`
    obtain ⟨S, tokE, E1, hreal, ⟨hgood, hother, htok3, htokχ⟩, hcard, hR1, hzero1, -, hload1, hlib1,
      hstruct1⟩ :=
      vertex_layer E hQ0 hX0 (σ x) p x (fun i hi => hdvd i hi x List.mem_cons_self) g
        (fun S tokE => Good (x :: ds) (U ∪ S.biUnion tokE) ∧
          (∀ τ ∈ S, ∀ y ∈ xs0, y ≠ x → vcharge (σ y) p y (tokE τ) = 0) ∧
          (∀ τ ∈ S, M ∣ (tokE τ).card) ∧
          ∀ τ ∈ S, charge χ qχ (tokE τ) = if τ.sign then cχ x else -cχ x)
        (fun S hS => by
          obtain ⟨tokE, h1, h2, h3, h4, h5⟩ := hsup x hx0 κ ds U
            (fun h => hdsx x h List.mem_cons_self) hG S
            (hS.trans (hN x List.mem_cons_self))
          exact ⟨tokE, by rw [hR0]; exact h1, h2, h3, h4, h5⟩)
    -- the shape of the new pieces, with the signed degrees at the other vertices
    have hOA : ∀ i ∈ E.lib, E.P i ⊆ E.R0 ∪ X0 := fun i hi => E.subP i hi
    have hshape : ∀ j ∈ E1.lib, ∀ y ∈ xs0, y ≠ x →
        (vcharge (σ y) p y (E1.P j) = 0 ∧ (E1.P j).card ≤ 2 * g) ∨
        ∃ i ∈ E.lib, j = Sum.inl i ∧ vcharge (σ y) p y (E1.P j) = vcharge (σ y) p y (E.P i) ∧
          (E1.P j).card ≤ (E.P i).card + g * (vcharge (σ x) p x (E.P i) / 2).natAbs := by
      intro j hj y hy hyx
      obtain ⟨S1, hS1, h⟩ := hstruct1 j hj
      have htok : ∀ τ ∈ S1, vcharge (σ y) p y (tokE τ) = 0 :=
        fun τ hτ => hother τ (hS1 hτ) y hy hyx
      rcases h with ⟨hP, -, hcd⟩ | ⟨i, hi, hji, hP, hcd⟩
      · left
        refine ⟨?_, hcd⟩
        rw [hP]
        exact (vcharge_shape (σ y) p y hreal hS1 htok (O := ∅) (empty_subset _)
          (by simp)).1
      · right
        refine ⟨i, hi, hji, ?_, hcd⟩
        rw [hP]
        exact (vcharge_shape (σ y) p y hreal hS1 htok (hOA i hi) (E.loopP i hi)).2
    -- the next layers
    have hQ1 : Q ∅ ∧ vcharge (σ x) p x ∅ = 0 := ⟨hQ0, vcharge_empty _ _ _⟩
    have hR1' : E1.R0 = R ∪ (U ∪ S.biUnion tokE) := by rw [hR1, hR0, union_assoc]
    have hds1 : ∀ j ∈ E1.lib, ∀ y ∈ x :: ds, vcharge (σ y) p y (E1.P j) = 0 := by
      intro j hj y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hzero1 j hj
      · have hyx : y ≠ x := fun h => hdsx y hy (h ▸ List.mem_cons_self)
        rcases hshape j hj y (hds0 y hy) hyx with ⟨h, -⟩ | ⟨i, hi, -, h, -⟩
        · exact h
        · rw [h]; exact hds i hi y hy
    have hdvd1 : ∀ j ∈ E1.lib, ∀ y ∈ xs, (2 : ℤ) ∣ vcharge (σ y) p y (E1.P j) := by
      intro j hj y hy
      have hyx : y ≠ x := fun h => hxnot (h ▸ hy)
      rcases hshape j hj y (hxs0 y (List.mem_cons_of_mem _ hy)) hyx with ⟨h, -⟩ |
          ⟨i, hi, -, h, -⟩
      · rw [h]; exact dvd_zero _
      · rw [h]; exact hdvd i hi y (List.mem_cons_of_mem _ hy)
    have hsum1 : ∀ y ∈ xs, ∑ j ∈ E1.lib, (vcharge (σ y) p y (E1.P j) / 2).natAbs ≤
        ∑ i ∈ E.lib, (vcharge (σ y) p y (E.P i) / 2).natAbs := by
      intro y hy
      have hyx : y ≠ x := fun h => hxnot (h ▸ hy)
      apply sum_le_of_inl E1.lib E.lib _ _
      intro j hj
      rcases hshape j hj y (hxs0 y (List.mem_cons_of_mem _ hy)) hyx with ⟨h, -⟩ |
          ⟨i, hi, hji, h, -⟩
      · left; rw [h]; rfl
      · right; exact ⟨i, hi, hji, by rw [h]⟩
    have hN1 : ∀ y ∈ xs, 9 * ∑ j ∈ E1.lib, (vcharge (σ y) p y (E1.P j) / 2).natAbs ≤ N :=
      fun y hy => (Nat.mul_le_mul_left 9 (hsum1 y hy)).trans
        (hN y (List.mem_cons_of_mem _ hy))
    have hpot1 : ∀ j ∈ E1.lib, (E1.P j).card +
        g * ∑ y ∈ xs.toFinset, (vcharge (σ y) p y (E1.P j) / 2).natAbs ≤ B := by
      intro j hj
      obtain ⟨S1, hS1, h⟩ := hstruct1 j hj
      have htok : ∀ y ∈ xs, ∀ τ ∈ S1, vcharge (σ y) p y (tokE τ) = 0 := by
        intro y hy τ hτ
        exact hother τ (hS1 hτ) y (hxs0 y (List.mem_cons_of_mem _ hy)) (fun h => hxnot (h ▸ hy))
      rcases h with ⟨hP, -, hcd⟩ | ⟨i, hi, -, hP, hcd⟩
      · have hz : ∀ y ∈ xs.toFinset, (vcharge (σ y) p y (E1.P j) / 2).natAbs = 0 := by
          intro y hy
          rw [hP, (vcharge_shape (σ y) p y hreal hS1 (htok y (List.mem_toFinset.mp hy))
            (O := ∅) (empty_subset _) (by simp)).1]
          rfl
        rw [sum_eq_zero hz, mul_zero, add_zero]
        exact hcd.trans hB
      · have hsplit : ∑ y ∈ xs.toFinset, (vcharge (σ y) p y (E1.P j) / 2).natAbs =
            ∑ y ∈ xs.toFinset, (vcharge (σ y) p y (E.P i) / 2).natAbs := by
          refine sum_congr rfl fun y hy => ?_
          rw [hP, (vcharge_shape (σ y) p y hreal hS1 (htok y (List.mem_toFinset.mp hy))
            (hOA i hi) (E.loopP i hi)).2]
        have hpi := hpot i hi
        rw [List.toFinset_cons, sum_insert (fun h => hxnot (List.mem_toFinset.mp h))] at hpi
        rw [hsplit]
        nlinarith [hcd]
    have hload1' : ∀ w, ∑ j ∈ E1.lib, incidentLoad (E1.P j) w ≤
        base w + 44 * incidentLoad (U ∪ S.biUnion tokE) w := by
      intro w
      have hdisU : Disjoint U (S.biUnion tokE) := by
        have h := hreal.avoid_biUnion (le_refl S)
        rw [hR0] at h
        exact (h.mono_right (subset_union_right.trans subset_union_left)).symm
      rw [incidentLoad_union_of_disjoint hdisU,
        incidentLoad_biUnion_eq S tokE hreal.disj w]
      have := hload1 w
      have := hload w
      nlinarith
    have h3E1 : ∀ j ∈ E1.lib, M ∣ (E1.P j).card := by
      intro j hj
      obtain ⟨S1, hS1, h⟩ := hstruct1 j hj
      have hdis : (S1 : Set (Tok κ)).PairwiseDisjoint tokE := hreal.disj.subset hS1
      have hT : M ∣ (S1.biUnion tokE).card := by
        rw [card_biUnion hdis]
        exact dvd_sum fun τ hτ => htok3 τ (hS1 hτ)
      rcases h with ⟨hP, -, -⟩ | ⟨i, hi, -, hP, -⟩
      · rw [hP]; exact hT
      · rw [hP, card_union_of_disjoint ((hreal.avoid_biUnion hS1).mono_right (hOA i hi)).symm]
        exact dvd_add (h3P i hi) hT
    have hχ1 : ∑ j ∈ E1.lib, (if charge χ qχ (E1.P j) = 0 ∧
        ∀ y ∈ xs, vcharge (σ y) p y (E1.P j) = 0 then 0 else 1) ≤ Kχ := by
      refine le_trans ?_ hχK
      apply sum_le_of_inl E1.lib E.lib _ _
      intro j hj
      obtain ⟨S1, hS1, h⟩ := hstruct1 j hj
      have hdis : (S1 : Set (Tok κ)).PairwiseDisjoint tokE := hreal.disj.subset hS1
      have htl : ∀ τ ∈ S1, ∀ e ∈ tokE τ, ¬ e.IsDiag := fun τ hτ => hreal.loop τ (hS1 hτ)
      have hbl : ∀ e ∈ S1.biUnion tokE, ¬ e.IsDiag := by
        intro e he
        obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp he
        exact htl τ hτ e he
      have hsgn : ∀ a : ℤ, ∑ τ ∈ S1, (if τ.sign then a else -a) =
          a * ∑ τ ∈ S1, (if τ.sign then (1 : ℤ) else -1) := by
        intro a
        rw [mul_sum]
        exact sum_congr rfl fun τ _ => by split_ifs <;> ring
      have hpend : ∀ y ∈ xs, ∀ τ ∈ S1, vcharge (σ y) p y (tokE τ) = 0 := fun y hy τ hτ =>
        hother τ (hS1 hτ) y (hxs0 y (List.mem_cons_of_mem _ hy)) (fun h => hxnot (h ▸ hy))
      rcases h with ⟨hP, hnot, -⟩ | ⟨i, hi, hji, hP, hcd⟩
      · -- a token-only piece: zero charge and zero pending signed degrees
        left
        have hx0 : vcharge (σ x) p x (E1.P j) = 0 := hzero1 j hj
        rw [hP, ← vcharge_eq_charge _ _ _ _ hbl, charge_biUnion _ _ S1 tokE hdis] at hx0
        have hx1 : ∑ τ ∈ S1, (if τ.sign then (2 : ℤ) else -2) = 0 := by
          rw [← hx0]; exact sum_congr rfl fun τ hτ => (hreal.chg τ (hS1 hτ)).symm
        have hs0 : ∑ τ ∈ S1, (if τ.sign then (1 : ℤ) else -1) = 0 := by
          rw [hsgn 2] at hx1; linarith
        have hc : charge χ qχ (E1.P j) = 0 := by
          rw [hP, charge_biUnion _ _ S1 tokE hdis,
            sum_congr rfl fun τ hτ => htokχ τ (hS1 hτ), hsgn, hs0, mul_zero]
        have hv : ∀ y ∈ xs, vcharge (σ y) p y (E1.P j) = 0 := fun y hy => by
          rw [hP]
          exact (vcharge_shape (σ y) p y hreal hS1 (hpend y hy) (O := ∅) (empty_subset _)
            (by simp)).1
        rw [if_pos ⟨hc, hv⟩]
      · by_cases hf : charge χ qχ (E1.P j) = 0 ∧ ∀ y ∈ xs, vcharge (σ y) p y (E1.P j) = 0
        · left; rw [if_pos hf]
        right
        refine ⟨i, hi, hji, ?_⟩
        rw [if_neg hf]
        by_cases hact : charge χ qχ (E.P i) = 0 ∧ ∀ y ∈ x :: xs, vcharge (σ y) p y (E.P i) = 0
        · -- an inactive piece receives no tokens, so it stays inactive
          exfalso
          have hbx : (vcharge (σ x) p x (E.P i) / 2).natAbs = 0 := by
            rw [hact.2 x List.mem_cons_self]; rfl
          have hdisT : Disjoint (E.P i) (S1.biUnion tokE) :=
            ((hreal.avoid_biUnion hS1).mono_right (hOA i hi)).symm
          have hcard : (E1.P j).card = (E.P i).card + (S1.biUnion tokE).card := by
            rw [hP, card_union_of_disjoint hdisT]
          rw [hbx, mul_zero, add_zero] at hcd
          have hT0 : S1.biUnion tokE = ∅ := by
            apply card_eq_zero.mp; omega
          have hPeq : E1.P j = E.P i := by rw [hP, hT0, union_empty]
          refine hf ⟨by rw [hPeq]; exact hact.1, fun y hy => ?_⟩
          rw [hPeq]; exact hact.2 y (List.mem_cons_of_mem _ hy)
        · rw [if_neg hact]
    have hlib1' : E1.lib.card ≤ L0 + 11 * N := by
      have h9 := hN x List.mem_cons_self
      omega
    obtain ⟨ι, E2, U2, hG2, hU2, hR2, hz2, hsz2, h3E2, hχ2, hl2, hlib2⟩ :=
      ih hnd' (fun y hy => hxs0 y (List.mem_cons_of_mem _ hy)) (x :: ds)
        (fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx0
          · exact hds0 y hy)
        (fun y hy hyxs => by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hxnot hyxs
          · exact hdsx y hy (List.mem_cons_of_mem _ hyxs))
        E1 hQ1 (U ∪ S.biUnion tokE) (L0 + 11 * N) hgood hR1' hds1 hdvd1 hN1 hpot1
        hload1' h3E1 hχ1 hlib1'
    refine ⟨ι, E2.mono (fun L _ ⟨hq, hv⟩ => ⟨⟨hq, hv x List.mem_cons_self⟩,
        fun y hy => hv y (List.mem_cons_of_mem _ hy)⟩),
      U2, by simpa [List.reverse_cons] using hG2,
      subset_union_left.trans hU2, hR2, ?_, hsz2, h3E2, hχ2, hl2, ?_⟩
    · intro j hj y hy
      rcases hy with hy | hy
      · exact hz2 j hj y (Or.inl (List.mem_cons_of_mem _ hy))
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hz2 j hj y (Or.inl List.mem_cons_self)
        · exact hz2 j hj y (Or.inr hy)
    · show E2.lib.card ≤ L0 + 11 * N * (x :: xs).length
      calc E2.lib.card ≤ L0 + 11 * N + 11 * N * xs.length := hlib2
        _ = L0 + 11 * N * (x :: xs).length := by simp only [List.length_cons]; ring

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.vertex_layers_y
