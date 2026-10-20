/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.VertexLayer

@[expose] public section

/-!
# Stacking the vertex layers

`vertex_layers` applies `vertex_layer` once for every vertex of a list `xs` (the vertices of the
bipartite classes), starting from a refiner `E`. The token supply is an abstract hypothesis `hsup`:
for every vertex `x` of the full list `xs0`, given the tokens `U` accumulated so far (with a predicate
`Good k U` after `k` layers), it realizes any `≤ N` token identities by tokens rooted at `x` that avoid
`R ∪ U ∪ X0`, keep `Good`, and have zero signed degree at every other vertex of `xs0`.

Invariants carried through the layers (`ds` = the vertices already treated):
* zero signed degree at the treated vertices;
* even signed degree and `9 ∑ |b_y / 2| ≤ N` at the pending vertices;
* the potential `|P| + g ∑_{pending y} |b_y(P) / 2| ≤ B` (so piece sizes stay `≤ B`);
* vertex loads of the pieces `≤ base + 44 · load(U)`;
* `|lib| ≤ L0 + 11 N k`;
* `M ∣ |P|` for every piece, when every token has `M ∣ |T|` (`M = 3` keeps `3 ∣ |E|`; `M = 1` is void).
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {W : Type*} [DecidableEq W]

theorem incidentLoad_union_of_disjoint {A B : Finset (Sym2 W)} (h : Disjoint A B) (w : W) :
    incidentLoad (A ∪ B) w = incidentLoad A w + incidentLoad B w := by
  unfold incidentLoad
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

theorem incidentLoad_biUnion_eq {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 W))
    (h : (s : Set ι).PairwiseDisjoint E) (w : W) :
    incidentLoad (s.biUnion E) w = ∑ i ∈ s, incidentLoad (E i) w := by
  unfold incidentLoad
  rw [filter_biUnion, card_biUnion]
  intro i hi j hj hij
  exact disjoint_filter_filter (h hi hj hij)

/-- Sums over the new library are bounded by sums over the old one, when every new index carries
zero or the value of its old index. -/
theorem sum_le_of_inl {κ β : Type*} (s : Finset (κ ⊕ β)) (T : Finset κ) (f : κ ⊕ β → ℕ)
    (g : κ → ℕ) (h : ∀ j ∈ s, f j = 0 ∨ ∃ i ∈ T, j = Sum.inl i ∧ f j = g i) :
    ∑ j ∈ s, f j ≤ ∑ i ∈ T, g i := by
  classical
  let F' : κ ⊕ β → ℕ := fun j => Sum.elim g (fun _ => 0) j
  have h1 : ∑ j ∈ s, f j = ∑ j ∈ s.filter (fun j => f j ≠ 0), f j := by
    rw [sum_filter_ne_zero]
  have h2 : ∑ j ∈ s.filter (fun j => f j ≠ 0), f j =
      ∑ j ∈ s.filter (fun j => f j ≠ 0), F' j := by
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨hjs, hj0⟩ := mem_filter.mp hj
    rcases h j hjs with h0 | ⟨i, -, rfl, hfi⟩
    · exact absurd h0 hj0
    · simp [F', hfi]
  have h3 : s.filter (fun j => f j ≠ 0) ⊆ T.map Function.Embedding.inl := by
    intro j hj
    obtain ⟨hjs, hj0⟩ := mem_filter.mp hj
    rcases h j hjs with h0 | ⟨i, hi, rfl, -⟩
    · exact absurd h0 hj0
    · exact mem_map_of_mem _ hi
  rw [h1, h2]
  refine (sum_le_sum_of_subset h3).trans (le_of_eq ?_)
  rw [sum_map]
  rfl

theorem vcharge_empty (σ : Fin t → ℤ) (p : W → Fin t) (x : W) :
    vcharge σ p x (∅ : Finset (Sym2 W)) = 0 := by
  simp [vcharge, degVec]

/-- Signed degree of a new piece: zero when it is made of tokens with zero signed degree, and that
of the old piece otherwise. -/
theorem vcharge_shape {κ : Type*} (σ : Fin t → ℤ) (p : W → Fin t) (y : W)
    {S : Finset (Tok κ)} {tokE : Tok κ → Finset (Sym2 W)} {A : Finset (Sym2 W)}
    {t' : ℕ} {χ0 χ1 : Fin t' → Fin t' → ℤ} {p0 : W → Fin t'} {u : ℤ} {g : ℕ}
    (hreal : TokReal χ0 χ1 p0 u g A S tokE) {S1 : Finset (Tok κ)} (hS1 : S1 ⊆ S)
    (htok : ∀ τ ∈ S1, vcharge σ p y (tokE τ) = 0) {O : Finset (Sym2 W)} (hOA : O ⊆ A)
    (hOloop : ∀ e ∈ O, ¬ e.IsDiag) :
    vcharge σ p y (S1.biUnion tokE) = 0 ∧ vcharge σ p y (O ∪ S1.biUnion tokE) = vcharge σ p y O := by
  have htl : ∀ τ ∈ S1, ∀ e ∈ tokE τ, ¬ e.IsDiag := fun τ hτ => hreal.loop τ (hS1 hτ)
  have hbl : ∀ e ∈ S1.biUnion tokE, ¬ e.IsDiag := by
    intro e he
    obtain ⟨τ, hτ, he⟩ := mem_biUnion.mp he
    exact htl τ hτ e he
  have hdis : (S1 : Set (Tok κ)).PairwiseDisjoint tokE := hreal.disj.subset hS1
  have hB : vcharge σ p y (S1.biUnion tokE) = 0 := by
    rw [← vcharge_eq_charge σ p y _ hbl, charge_biUnion _ _ S1 tokE hdis]
    refine sum_eq_zero fun τ hτ => ?_
    rw [vcharge_eq_charge σ p y _ (htl τ hτ)]
    exact htok τ hτ
  refine ⟨hB, ?_⟩
  have hdisO : Disjoint O (S1.biUnion tokE) := ((hreal.avoid_biUnion hS1).mono_right hOA).symm
  have hul : ∀ e ∈ O ∪ S1.biUnion tokE, ¬ e.IsDiag := by
    intro e he
    rcases mem_union.mp he with h | h
    · exact hOloop e h
    · exact hbl e h
  rw [← vcharge_eq_charge σ p y _ hul, charge_union _ _ hdisO, vcharge_eq_charge σ p y _ hOloop,
    vcharge_eq_charge σ p y _ hbl, hB, add_zero]

/-- **The stacked vertex layers.** -/
theorem vertex_layers {X0 : Finset (Sym2 W)} (hX0 : ∀ e ∈ X0, ¬ e.IsDiag)
    (σ : W → Fin t → ℤ) (p : W → Fin t) (g N B M : ℕ) (hB : 2 * g ≤ B)
    (R : Finset (Sym2 W)) (base : W → ℕ) (Good : List W → Finset (Sym2 W) → Prop) (xs0 : List W)
    (hsup : ∀ x ∈ xs0, ∀ (ι : Type) (D : List W) (U : Finset (Sym2 W)), x ∉ D → Good D U →
      ∀ S : Finset (Tok ι), S.card ≤ N →
      ∃ tokE, TokReal (chiV (σ x)) (fun _ _ => 0) (relab p x) 2 g (R ∪ U ∪ X0) S tokE ∧
        Good (x :: D) (U ∪ S.biUnion tokE) ∧
        (∀ τ ∈ S, ∀ y ∈ xs0, y ≠ x → vcharge (σ y) p y (tokE τ) = 0) ∧
        ∀ τ ∈ S, M ∣ (tokE τ).card) :
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
    E.lib.card ≤ L0 →
    ∃ (ι : Type) (E' : PredRefiner ι X0 (fun L => Q L ∧ ∀ y ∈ xs, vcharge (σ y) p y L = 0))
      (U' : Finset (Sym2 W)),
      Good (xs.reverse ++ ds) U' ∧ U ⊆ U' ∧ E'.R0 = R ∪ U' ∧
      (∀ j ∈ E'.lib, ∀ y, (y ∈ ds ∨ y ∈ xs) → vcharge (σ y) p y (E'.P j) = 0) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ B) ∧ (∀ j ∈ E'.lib, M ∣ (E'.P j).card) ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤ base w + 44 * incidentLoad U' w) ∧
      E'.lib.card ≤ L0 + 11 * N * xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro _ _ ds _ _ κ Q E _ U L0 hG hR0 hds _ _ hpot hload h3P hlib
    refine ⟨κ, E.mono (fun L _ h => h.1), U, by simpa using hG, le_rfl, hR0, ?_, ?_, h3P, hload,
      ?_⟩
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
    intro hnd hxs0 ds hds0 hdsx κ Q E hQ0 U L0 hG hR0 hds hdvd hN hpot hload h3P hlib
    have hx0 : x ∈ xs0 := hxs0 x List.mem_cons_self
    have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    -- the layer at `x`
    obtain ⟨S, tokE, E1, hreal, ⟨hgood, hother, htok3⟩, hcard, hR1, hzero1, -, hload1, hlib1,
      hstruct1⟩ :=
      vertex_layer E hQ0 hX0 (σ x) p x (fun i hi => hdvd i hi x List.mem_cons_self) g
        (fun S tokE => Good (x :: ds) (U ∪ S.biUnion tokE) ∧
          (∀ τ ∈ S, ∀ y ∈ xs0, y ≠ x → vcharge (σ y) p y (tokE τ) = 0) ∧
          ∀ τ ∈ S, M ∣ (tokE τ).card)
        (fun S hS => by
          obtain ⟨tokE, h1, h2, h3, h4⟩ := hsup x hx0 κ ds U
            (fun h => hdsx x h List.mem_cons_self) hG S
            (hS.trans (hN x List.mem_cons_self))
          exact ⟨tokE, by rw [hR0]; exact h1, h2, h3, h4⟩)
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
    have hlib1' : E1.lib.card ≤ L0 + 11 * N := by
      have h9 := hN x List.mem_cons_self
      omega
    obtain ⟨ι, E2, U2, hG2, hU2, hR2, hz2, hsz2, h3E2, hl2, hlib2⟩ :=
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
        hload1' h3E1 hlib1'
    refine ⟨ι, E2.mono (fun L _ ⟨hq, hv⟩ => ⟨⟨hq, hv x List.mem_cons_self⟩,
        fun y hy => hv y (List.mem_cons_of_mem _ hy)⟩),
      U2, by simpa [List.reverse_cons] using hG2,
      subset_union_left.trans hU2, hR2, ?_, hsz2, h3E2, hl2, ?_⟩
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

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.vertex_layers
