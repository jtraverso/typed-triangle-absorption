/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Expander.PermutationExpander
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RealTensorFilling
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.NetworkFlowRounding

@[expose] public section

/-!
# Expanders as flow networks (§§4–5 of the dense producer)

* `cutSize_ge_edgeBoundary`: the ordered-pair cut count `cutSize G S` of the scalar flow
  library dominates the number of physical boundary edges `edgeBoundary G S` of the proved
  expanders (each crossing edge is counted once).
* `connected_of_expands`: positive cut expansion forces connectedness.
* `exists_good_expander`: for every `n ≥ 1` a simple graph on `Fin n` with maximum degree `≤ 8`,
  `Expands G (1/20)` and `G.Connected`.
* `integer_flow`: every zero-sum integer demand `|g| ≤ M` on such a graph is the divergence of an
  integer flow (for any orientation) with `|z_e| < M / h + 1`.
* `split`: an integer `F` with `|F| ≤ k n` splits into `n` integer parts of size `≤ k + 1`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Matrix OrientedCycleVector

section Adapter

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each crossing physical edge is counted once by the ordered-pair cut count. -/
theorem cutSize_ge_edgeBoundary (S : Finset V) :
    ((Expander.edgeBoundary G S).card : ℝ) ≤ ExpandingFlowInverse.cutSize G S := by
  classical
  let P : Finset (V × V) := (Sᶜ ×ˢ S).filter (fun p => G.Adj p.1 p.2)
  have hsub : Expander.edgeBoundary G S ⊆ P.image (fun p => s(p.1, p.2)) := by
    intro e he
    simp only [Expander.edgeBoundary, mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, x, hx, y, hy, rfl⟩ := he
    refine mem_image.mpr ⟨(y, x), ?_, Sym2.eq_swap⟩
    simp only [P, mem_filter, mem_product, mem_compl]
    exact ⟨⟨hy, hx⟩, ((SimpleGraph.mem_edgeSet G).mp he).symm⟩
  have hcard : (Expander.edgeBoundary G S).card ≤ P.card :=
    (card_le_card hsub).trans card_image_le
  have hP : (P.card : ℝ) = ExpandingFlowInverse.cutSize G S := by
    unfold ExpandingFlowInverse.cutSize
    simp only [P]
    rw [Finset.card_filter, Finset.sum_product]
    push_cast
    rfl
  rw [← hP]
  exact_mod_cast hcard

/-- Positive expansion implies connectedness. -/
theorem connected_of_expands [Nonempty V] (h : ℝ) (hh : 0 < h)
    (hexp : ExpandingFlowInverse.Expands G h) : G.Connected := by
  classical
  refine ⟨fun u v => ?_⟩
  by_contra huv
  let S : Finset V := univ.filter (fun w => G.Reachable u w)
  have huS : u ∈ S := by simp [S]
  have hvS : v ∉ S := by simpa [S] using huv
  have hcut : ExpandingFlowInverse.cutSize G S = 0 := by
    unfold ExpandingFlowInverse.cutSize
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    rw [if_neg]
    intro hxy
    simp only [S, mem_compl, mem_filter, mem_univ, true_and] at hx hy
    exact hx (hy.trans (SimpleGraph.Adj.reachable hxy.symm))
  have h1 : (1 : ℝ) ≤ min (S.card : ℝ) (Sᶜ.card : ℝ) := by
    have a1 : 1 ≤ S.card := card_pos.mpr ⟨u, huS⟩
    have a2 : 1 ≤ Sᶜ.card := card_pos.mpr ⟨v, by simpa using hvS⟩
    exact le_min (by exact_mod_cast a1) (by exact_mod_cast a2)
  have := hexp S
  rw [hcut] at this
  nlinarith

end Adapter

/-- **The expanders used by the dense producer.** -/
theorem exists_good_expander (n : ℕ) [NeZero n] :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      (∀ v, G.degree v ≤ 8) ∧ ExpandingFlowInverse.Expands G (1 / 20) ∧ G.Connected := by
  obtain ⟨G, hdec, hdeg, hexp⟩ := Expander.exists_expander_fin n
  have hE : ExpandingFlowInverse.Expands G (1 / 20) := by
    intro S
    have h1 := hexp S
    have h2 := cutSize_ge_edgeBoundary G S
    push_cast at h1
    linarith
  exact ⟨G, hdec, hdeg, hE, connected_of_expands G (1 / 20) (by norm_num) hE⟩

section Flow

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

/-- The integer oriented incidence: `+1` at the head, `-1` at the tail. -/
def incZ (v : V) (e : G.edgeSet) : ℤ :=
  (if v = (o e).snd then 1 else 0) - (if v = (o e).fst then 1 else 0)

theorem incidence_eq_incZ (v : V) (e : G.edgeSet) :
    incidence G o v e = (incZ G o v e : ℝ) := by
  classical
  unfold incidence incZ
  push_cast
  congr 1 <;> split_ifs <;> simp

include ho in
/-- **Bounded integer flows on an expander.** -/
theorem integer_flow (h : ℝ) (hh : 0 < h) (hexp : ExpandingFlowInverse.Expands G h)
    (g : V → ℤ) (hg : ∑ v, g v = 0) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ v, |(g v : ℝ)| ≤ M) :
    ∃ z : G.edgeSet → ℤ, (∀ v, ∑ e, incZ G o v e * z e = g v) ∧
      ∀ e, |(z e : ℝ)| < M / h + 1 := by
  classical
  have hgr : ∑ v, (g v : ℝ) = 0 := by exact_mod_cast hg
  obtain ⟨f, hf, hfb⟩ := ExpandingFlowInverse.bounded_preimage G o ho h hh hexp
    (fun v => (g v : ℝ)) hgr M hM0 hM
  have hint : ∀ v, (incidence G o).mulVecLin f v ∈ Set.range (Int.cast : ℤ → ℝ) := by
    intro v; rw [hf]; exact ⟨g v, rfl⟩
  obtain ⟨z, hz, -, herr⟩ := NetworkFlowRounding.round G o ho f hint
  refine ⟨z, fun v => ?_, fun e => ?_⟩
  · have h1 := congrFun hz v
    rw [hf] at h1
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, incidence_eq_incZ] at h1
    exact_mod_cast h1
  · have h1 := abs_lt.mp (herr e)
    have h2 := abs_le.mp (hfb e)
    rw [abs_lt]; constructor <;> linarith

end Flow

section Split

/-- Split an integer into `n` integer parts, as equal as possible. -/
def split (n : ℕ) (F : ℤ) (a : Fin n) : ℤ :=
  F / (n : ℤ) + if (a.val : ℤ) < F % (n : ℤ) then 1 else 0

theorem card_fin_val_lt (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun a : Fin n => a.val < r)).card = r := by
  have : (univ.filter (fun a : Fin n => a.val < r)).map Fin.valEmbedding = range r := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map, this, card_range]

theorem sum_split (n : ℕ) [NeZero n] (F : ℤ) : ∑ a : Fin n, split n F a = F := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr0 : 0 ≤ F % (n : ℤ) := Int.emod_nonneg _ hn.ne'
  have hrn : F % (n : ℤ) < n := Int.emod_lt_of_pos _ hn
  obtain ⟨r, hr⟩ : ∃ r : ℕ, F % (n : ℤ) = r :=
    ⟨(F % (n : ℤ)).toNat, (Int.toNat_of_nonneg hr0).symm⟩
  have hrn' : r ≤ n := by omega
  unfold split
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hr]
  have hcount : ∑ a : Fin n, (if ((a.val : ℕ) : ℤ) < (r : ℤ) then (1 : ℤ) else 0) = r := by
    rw [Finset.sum_boole]
    have : (univ.filter (fun a : Fin n => ((a.val : ℕ) : ℤ) < (r : ℤ))) =
        (univ.filter (fun a : Fin n => a.val < r)) := by
      ext a; simp
    rw [this, card_fin_val_lt n r hrn']
  rw [hcount, nsmul_eq_mul]
  have := Int.mul_ediv_add_emod F n
  rw [hr] at this
  linarith

theorem abs_split_le (n : ℕ) [NeZero n] (F : ℤ) (k : ℕ) (hF : |F| ≤ k * n) (a : Fin n) :
    |split n F a| ≤ k + 1 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨h1, h2⟩ := abs_le.mp hF
  have hq1 : F / (n : ℤ) ≤ k := by
    rw [Int.ediv_le_iff_le_mul hn]; nlinarith
  have hq2 : -(k : ℤ) ≤ F / (n : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hn]; nlinarith
  unfold split
  rw [abs_le]
  constructor <;> split_ifs <;> omega

end Split

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
