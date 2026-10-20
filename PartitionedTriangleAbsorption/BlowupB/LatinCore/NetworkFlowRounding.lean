/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.OrientedCycleVector
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingCycle
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingDescent
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.FlowRoundingNoLeaf
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Archimedean

@[expose] public section

/-! Integral box rounding for the oriented incidence of a finite simple
graph. All cycle and descent witnesses are produced inside the proof. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding

open SimpleGraph SimpleGraph.Walk Matrix
open scoped BigOperators
open OrientedCycleVector FlowRoundingDescent

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

noncomputable def fractionalGraph (f : G.edgeSet → ℝ) : SimpleGraph V where
  Adj u v := ∃ h : G.Adj u v, f ⟨s(u,v), h⟩ ∉ Set.range (Int.cast : ℤ → ℝ)
  symm := ⟨by
    intro u v h
    obtain ⟨huv, hf⟩ := h
    refine ⟨huv.symm, ?_⟩
    have he : (⟨s(v,u), huv.symm⟩ : G.edgeSet) = ⟨s(u,v), huv⟩ :=
      Subtype.ext Sym2.eq_swap
    simpa only [he] using hf⟩
  loopless := ⟨by intro v h; exact G.irrefl h.choose⟩

theorem fractionalGraph_le (f : G.edgeSet → ℝ) : fractionalGraph G f ≤ G :=
  fun _ _ h => h.choose

noncomputable instance fractionalGraphDecidable (f : G.edgeSet → ℝ) :
    DecidableRel (fractionalGraph G f).Adj := Classical.decRel _

include ho in
theorem fractional_adj (f : G.edgeSet → ℝ) (e : G.edgeSet)
    (hf : f e ∉ Set.range (Int.cast : ℤ → ℝ)) :
    (fractionalGraph G f).Adj (o e).fst (o e).snd := by
  refine ⟨(o e).adj, ?_⟩
  have he : (⟨s((o e).fst, (o e).snd), (o e).adj⟩ : G.edgeSet) = e :=
    Subtype.ext (ho e)
  simpa only [he] using hf

private theorem term_integral {E : Type*} [Fintype E] [DecidableEq E]
    (a : E → ℤ) (f : E → ℝ) (e : E) (ha : a e = 1 ∨ a e = -1)
    (hother : ∀ j ∈ Finset.univ.erase e,
      (a j : ℝ) * f j ∈ Set.range (Int.cast : ℤ → ℝ))
    (htotal : (∑ j, (a j : ℝ) * f j) ∈ Set.range (Int.cast : ℤ → ℝ)) :
    f e ∈ Set.range (Int.cast : ℤ → ℝ) := by
  have ht := FlowRoundingNoLeaf.integral_of_unique_fractional_candidate
    Finset.univ (fun _ : E => (1 : ℤ)) (fun j => (a j : ℝ) * f j)
    e (Finset.mem_univ e) (Or.inl rfl) hother (by simpa using htotal)
  rcases ha with hp | hn
  · simpa [hp] using ht
  · obtain ⟨z, hz⟩ := ht
    refine ⟨-z, ?_⟩
    simp only [hn, Int.cast_neg, Int.cast_one, neg_one_mul] at hz
    push_cast
    linarith

include ho in
theorem fractional_no_leaf (f : G.edgeSet → ℝ)
    (hint : ∀ v, (incidence G o).mulVecLin f v ∈ Set.range (Int.cast : ℤ → ℝ)) :
    ∀ v, (fractionalGraph G f).degree v ≠ 1 := by
  classical
  intro v hdeg
  obtain ⟨w, hw, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  obtain ⟨hvw, hnon⟩ := hw
  let e₀ : G.edgeSet := ⟨s(v,w), hvw⟩
  let a : G.edgeSet → ℤ := fun e =>
    (if v = (o e).snd then 1 else 0) - (if v = (o e).fst then 1 else 0)
  have ha : a e₀ = 1 ∨ a e₀ = -1 := by
    have hd := SimpleGraph.dart_edge_eq_mk'_iff'.mp (ho e₀)
    rcases hd with ⟨hf, ht⟩ | ⟨hf, ht⟩ <;>
      simp [a, hf, ht, hvw.ne, Ne.symm hvw.ne]
  apply hnon
  apply term_integral a f e₀ ha
  · intro j hj
    have hje : j ≠ e₀ := (Finset.mem_erase.mp hj).1
    by_cases hf : f j ∈ Set.range (Int.cast : ℤ → ℝ)
    · obtain ⟨z, hz⟩ := hf
      exact ⟨a j * z, by simp [hz]⟩
    · have hadj := fractional_adj G o ho f j hf
      have hfst : v ≠ (o j).fst := by
        intro hv
        have hother : (o j).snd = w := huniq _ (by simpa [hv] using hadj)
        apply hje
        apply Subtype.ext
        calc j.val = (o j).edge := (ho j).symm
          _ = s(v,w) := by simp [Dart.edge, ← hv, hother]
      have hsnd : v ≠ (o j).snd := by
        intro hv
        have hother : (o j).fst = w := huniq _ (by simpa [hv] using hadj.symm)
        apply hje
        apply Subtype.ext
        calc j.val = (o j).edge := (ho j).symm
          _ = s(v,w) := by simp [Dart.edge, ← hv, hother, Sym2.eq_swap]
      exact ⟨0, by simp [a, hfst, hsnd]⟩
  · simpa [incidence, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, a] using hint v

include ho in
theorem fractional_direction (f : G.edgeSet → ℝ)
    (hint : ∀ v, (incidence G o).mulVecLin f v ∈ Set.range (Int.cast : ℤ → ℝ))
    (hne : (fractional f).Nonempty) :
    ∃ (s : Finset G.edgeSet) (d : G.edgeSet → ℝ), s.Nonempty ∧ s ⊆ fractional f ∧
      (∀ e ∈ s, d e = 1 ∨ d e = -1) ∧ (∀ e ∉ s, d e = 0) ∧
      (incidence G o).mulVecLin d = 0 := by
  classical
  obtain ⟨e, he⟩ := hne
  have hex : ∃ a b, (fractionalGraph G f).Adj a b :=
    ⟨(o e).fst, (o e).snd, fractional_adj G o ho f e ((mem_fractional f e).mp he)⟩
  obtain ⟨v, p, hp⟩ := FlowRoundingCycle.exists_cycle_of_no_leaf
    (fractionalGraph G f) hex (fractional_no_leaf G o ho f hint)
  let q : G.Walk v v := p.mapLe (fractionalGraph_le G f)
  have hq : q.IsCycle := hp.mapLe _
  let s : Finset G.edgeSet := Finset.univ.filter fun e => e.val ∈ q.edges
  have hs : s.Nonempty := by
    have hqn : q.edges ≠ [] := fun hh => hq.not_nil (Walk.edges_eq_nil.mp hh)
    cases hh : q.edges with
    | nil => exact (hqn hh).elim
    | cons e es =>
      have hm : e ∈ q.edges := by rw [hh]; simp
      exact ⟨⟨e, q.edges_subset_edgeSet hm⟩, by simp [s, hm]⟩
  refine ⟨s, chain G o q, hs, ?_, ?_, ?_, closed_chain_kernel G o ho q⟩
  · intro j hj
    have hm : j.val ∈ q.edges := (Finset.mem_filter.mp hj).2
    have hm' : j.val ∈ p.edges := by
      simpa only [q, Walk.edges_mapLe_eq_edges] using hm
    have hadj : (fractionalGraph G f).Adj (o j).fst (o j).snd :=
      p.adj_of_mem_edges (by simpa only [← ho j, Dart.edge] using hm')
    obtain ⟨hjG, hjf⟩ := hadj
    have hje : (⟨s((o j).fst, (o j).snd), hjG⟩ : G.edgeSet) = j :=
      Subtype.ext (ho j)
    apply (mem_fractional f j).mpr
    simpa only [hje] using hjf
  · intro j hj
    exact chain_sign G o q hq.isTrail j (Finset.mem_filter.mp hj).2
  · intro j hj
    apply chain_zero_of_not_mem G o q j
    intro hm
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)

include ho in
/-- Integer box rounding, with the oriented incidence unchanged exactly.
There is no cycle-existence or rounding hypothesis in this theorem. -/
theorem round_box (f : G.edgeSet → ℝ) (lower upper : G.edgeSet → ℤ)
    (hbox : ∀ e, (lower e : ℝ) ≤ f e ∧ f e ≤ (upper e : ℝ))
    (hint : ∀ v, (incidence G o).mulVecLin f v ∈ Set.range (Int.cast : ℤ → ℝ)) :
    ∃ z : G.edgeSet → ℤ,
      (incidence G o).mulVecLin (fun e => (z e : ℝ)) = (incidence G o).mulVecLin f ∧
      ∀ e, lower e ≤ z e ∧ z e ≤ upper e := by
  classical
  obtain ⟨g, hg, hgb, hred⟩ := reduced_representative (incidence G o).mulVecLin f lower upper hbox
  have hgint : ∀ e, g e ∈ Set.range (Int.cast : ℤ → ℝ) := by
    intro e
    by_contra he
    have hne : (fractional g).Nonempty := ⟨e, (mem_fractional g e).mpr he⟩
    have hdiv : ∀ v, (incidence G o).mulVecLin g v ∈ Set.range (Int.cast : ℤ → ℝ) := by
      intro v
      rw [hg]
      exact hint v
    obtain ⟨s, d, hs, hsub, hsign, hzero, hk⟩ := fractional_direction G o ho g hdiv hne
    exact hred s d hs hsub hsign hzero hk
  choose z hz using hgint
  refine ⟨z, ?_, ?_⟩
  · have hzg : (fun e => (z e : ℝ)) = g := funext hz
    rw [hzg]
    exact hg
  · intro e
    have hb := hgb e
    rw [← hz e] at hb
    exact ⟨Int.cast_le.mp hb.1, Int.cast_le.mp hb.2⟩

include ho in
/-- Floor/ceiling rounding with strict entrywise error less than one. -/
theorem round (f : G.edgeSet → ℝ)
    (hint : ∀ v, (incidence G o).mulVecLin f v ∈ Set.range (Int.cast : ℤ → ℝ)) :
    ∃ z : G.edgeSet → ℤ,
      (incidence G o).mulVecLin (fun e => (z e : ℝ)) = (incidence G o).mulVecLin f ∧
      (∀ e, ⌊f e⌋ ≤ z e ∧ z e ≤ ⌈f e⌉) ∧
      ∀ e, |(z e : ℝ) - f e| < 1 := by
  obtain ⟨z, hz, hb⟩ := round_box G o ho f (fun e => ⌊f e⌋) (fun e => ⌈f e⌉)
    (fun e => ⟨Int.floor_le _, Int.le_ceil _⟩) hint
  refine ⟨z, hz, hb, ?_⟩
  intro e
  have hlo : (⌊f e⌋ : ℝ) ≤ (z e : ℝ) := Int.cast_le.mpr (hb e).1
  have hhi : (z e : ℝ) ≤ (⌈f e⌉ : ℝ) := Int.cast_le.mpr (hb e).2
  apply abs_lt.mpr
  constructor <;> linarith [Int.lt_floor_add_one (f e), Int.ceil_lt_add_one (f e)]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding.fractional_direction
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding.round_box
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding.round
