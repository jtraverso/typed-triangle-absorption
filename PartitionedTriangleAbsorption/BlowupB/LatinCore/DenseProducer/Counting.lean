/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.Faces

@[expose] public section

/-!
# Counting lemmas for the face catalogue

* indicator sums over injective families (`sum_ind_le_one`, `sum_ind_pair_le`);
* the degree bounds `∑_e [y = (o e).snd] ≤ deg y`, `∑_e [y = (o e).fst] ≤ deg y`;
* the number of faces of each family through a given arc (`tri_count`, `mB_count`, `mC_count`,
  `rect_count`), measured as `∑ |value|`;
* out- and in-profiles of a demand `χ_L` and the equality of the three class totals of a balanced
  `L ⊆ Qc n`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Positivization Cycles

section Ind

variable {X ι : Type} [DecidableEq X] [Fintype ι]

theorem sum_ind_le_one (g : ι → X) (hg : Function.Injective g) (α : X) :
    ∑ i, (if α = g i then (1 : ℤ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (univ.filter (fun i => α = g i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact hg (ha.symm.trans hb)
  exact_mod_cast this

theorem sum_ind_le_of_key {Y : Type} [DecidableEq Y] (g : ι → X) (hg : Function.Injective g)
    (key : X → Y) (κ : Y) (hk : ∀ i, key (g i) = κ) (α : X) :
    ∑ i, (if α = g i then (1 : ℤ) else 0) ≤ if key α = κ then 1 else 0 := by
  by_cases h : key α = κ
  · rw [if_pos h]; exact sum_ind_le_one g hg α
  · rw [if_neg h]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hα; apply h; rw [hα, hk]

theorem sum_ind_pair_le {E Y : Type} [Fintype E] [DecidableEq Y] (g : E → ι → X)
    (hg : ∀ e, Function.Injective (g e)) (key : X → Y) (κ : E → Y)
    (hk : ∀ e i, key (g e i) = κ e) (α : X) :
    ∑ q : E × ι, (if α = g q.1 q.2 then (1 : ℤ) else 0) ≤
      ∑ e, if key α = κ e then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun e _ => sum_ind_le_of_key (g e) (hg e) key (κ e) (hk e) α

end Ind

variable {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (o : G.edgeSet → G.Dart) (ho : ∀ e, (o e).edge = e.val)

section Degree

include ho in
theorem sum_snd_le_degree (y : Fin n) :
    ∑ e, (if y = (o e).snd then (1 : ℤ) else 0) ≤ G.degree y := by
  rw [Finset.sum_boole]
  have : (univ.filter (fun e => y = (o e).snd)).card ≤ (G.neighborFinset y).card := by
    refine card_le_card_of_injOn (fun e => (o e).fst) ?_ ?_
    · intro e he
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he
      simp only [mem_coe, SimpleGraph.mem_neighborFinset]
      rw [he]; exact (o e).adj.symm
    · intro e he e' he' hee
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he he'
      simp only at hee
      apply Subtype.ext
      rw [← ho e, ← ho e']
      simp only [SimpleGraph.Dart.edge]
      have : (o e).toProd = (o e').toProd := Prod.ext hee (he.symm.trans he')
      rw [this]
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  exact_mod_cast this

include ho in
theorem sum_fst_le_degree (y : Fin n) :
    ∑ e, (if y = (o e).fst then (1 : ℤ) else 0) ≤ G.degree y := by
  rw [Finset.sum_boole]
  have : (univ.filter (fun e => y = (o e).fst)).card ≤ (G.neighborFinset y).card := by
    refine card_le_card_of_injOn (fun e => (o e).snd) ?_ ?_
    · intro e he
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he
      simp only [mem_coe, SimpleGraph.mem_neighborFinset]
      rw [he]; exact (o e).adj
    · intro e he e' he' hee
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he he'
      simp only at hee
      apply Subtype.ext
      rw [← ho e, ← ho e']
      simp only [SimpleGraph.Dart.edge]
      have : (o e).toProd = (o e').toProd := Prod.ext (he.symm.trans he') hee
      rw [this]
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  exact_mod_cast this

theorem abs_incZ_le (x : Fin n) (e : G.edgeSet) :
    |incZ G o x e| ≤ (if x = (o e).snd then 1 else 0) + (if x = (o e).fst then 1 else 0) := by
  unfold incZ
  split_ifs <;> simp

include ho in
theorem sum_abs_incZ_le (d : ℕ) (hdeg : ∀ v, G.degree v ≤ d) (x : Fin n) :
    ∑ e, |incZ G o x e| ≤ 2 * d := by
  calc ∑ e, |incZ G o x e| ≤ ∑ e, ((if x = (o e).snd then (1 : ℤ) else 0) +
        (if x = (o e).fst then 1 else 0)) := Finset.sum_le_sum fun e _ => abs_incZ_le G o x e
    _ = ∑ e, (if x = (o e).snd then (1 : ℤ) else 0) + ∑ e, (if x = (o e).fst then 1 else 0) :=
        Finset.sum_add_distrib
    _ ≤ G.degree x + G.degree x :=
        add_le_add (sum_snd_le_degree G o ho x) (sum_fst_le_degree G o ho x)
    _ ≤ 2 * d := by have := hdeg x; omega

end Degree

section FaceCounts

theorem abs_ind_add3 (p1 p2 p3 : Vc n × Vc n) (α : Vc n × Vc n) :
    |(ind p1 + ind p2 + ind p3) α| ≤
      (if α = p1 then 1 else 0) + (if α = p2 then 1 else 0) + (if α = p3 then 1 else 0) := by
  simp only [Pi.add_apply, ind]
  split_ifs <;> simp

theorem abs_ind_add4 (p1 p2 q1 q2 : Vc n × Vc n) (α : Vc n × Vc n) :
    |(ind p1 + ind p2 - ind q1 - ind q2) α| ≤
      (if α = p1 then 1 else 0) + (if α = p2 then 1 else 0) + (if α = q1 then 1 else 0) +
        (if α = q2 then 1 else 0) := by
  simp only [Pi.add_apply, Pi.sub_apply, ind]
  split_ifs <;> norm_num

/-- Each arc lies in at most three Latin triangles (in fact one). -/
theorem tri_count (α : Vc n × Vc n) :
    ∑ p : Fin n × Fin n, |tri p.1 p.2 (p.1 + p.2) α| ≤ 3 := by
  have h1 := sum_ind_le_one (fun p : Fin n × Fin n => (vA p.1, vB p.2))
    (by intro p q h; simp only [Prod.mk.injEq, vA_inj, vB_inj] at h; exact Prod.ext h.1 h.2) α
  have h2 := sum_ind_le_one (fun p : Fin n × Fin n => (vB p.2, vC (p.1 + p.2)))
    (by
      intro p q h
      simp only [Prod.mk.injEq, vB_inj, vC_inj] at h
      have : p.1 = q.1 := by have := h.2; rw [h.1] at this; exact add_right_cancel this
      exact Prod.ext this h.1) α
  have h3 := sum_ind_le_one (fun p : Fin n × Fin n => (vC (p.1 + p.2), vA p.1))
    (by
      intro p q h
      simp only [Prod.mk.injEq, vA_inj, vC_inj] at h
      have : p.2 = q.2 := by have := h.1; rw [h.2] at this; exact add_left_cancel this
      exact Prod.ext h.2 this) α
  calc _ ≤ ∑ p : Fin n × Fin n, ((if α = (vA p.1, vB p.2) then (1 : ℤ) else 0) +
          (if α = (vB p.2, vC (p.1 + p.2)) then 1 else 0) +
          (if α = (vC (p.1 + p.2), vA p.1) then 1 else 0)) :=
        Finset.sum_le_sum fun p _ => abs_ind_add3 _ _ _ α
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 3 := by linarith

include ho in
/-- Each arc lies in at most `4d` faces `mB`. -/
theorem mB_count (d : ℕ) (hdeg : ∀ v, G.degree v ≤ d) (α : Vc n × Vc n) :
    ∑ q : G.edgeSet × Fin n, |mB G o q.1 q.2 α| ≤ 4 * d := by
  have hs : ∀ y, ∑ e, (if y = (o e).snd then (1 : ℤ) else 0) ≤ d :=
    fun y => (sum_snd_le_degree G o ho y).trans (by exact_mod_cast hdeg y)
  have hf : ∀ y, ∑ e, (if y = (o e).fst then (1 : ℤ) else 0) ≤ d :=
    fun y => (sum_fst_le_degree G o ho y).trans (by exact_mod_cast hdeg y)
  have h1 := sum_ind_pair_le (fun e a => ((vA a, vB (o e).snd) : Vc n × Vc n))
    (fun e a b h => by simpa [vA_inj] using h) (fun α => α.2.2) (fun e => (o e).snd)
    (fun e a => rfl) α
  have h2 := sum_ind_pair_le (fun e a => ((vB (o e).snd, vC (a + (o e).fst)) : Vc n × Vc n))
    (fun e a b h => by simpa [vC_inj] using h) (fun α => α.1.2) (fun e => (o e).snd)
    (fun e a => rfl) α
  have h3 := sum_ind_pair_le (fun e a => ((vA a, vB (o e).fst) : Vc n × Vc n))
    (fun e a b h => by simpa [vA_inj] using h) (fun α => α.2.2) (fun e => (o e).fst)
    (fun e a => rfl) α
  have h4 := sum_ind_pair_le (fun e a => ((vB (o e).fst, vC (a + (o e).fst)) : Vc n × Vc n))
    (fun e a b h => by simpa [vC_inj] using h) (fun α => α.1.2) (fun e => (o e).fst)
    (fun e a => rfl) α
  have := hs α.2.2; have := hs α.1.2; have := hf α.2.2; have := hf α.1.2
  refine (Finset.sum_le_sum fun q _ => abs_ind_add4 _ _ _ _ α).trans ?_
  simp only [Finset.sum_add_distrib]
  push_cast
  linarith

include ho in
/-- Each arc lies in at most `4d` faces `mC`. -/
theorem mC_count (d : ℕ) (hdeg : ∀ v, G.degree v ≤ d) (α : Vc n × Vc n) :
    ∑ q : G.edgeSet × Fin n, |mC G o q.1 q.2 α| ≤ 4 * d := by
  have hs : ∀ y, ∑ e, (if y = (o e).snd then (1 : ℤ) else 0) ≤ d :=
    fun y => (sum_snd_le_degree G o ho y).trans (by exact_mod_cast hdeg y)
  have hf : ∀ y, ∑ e, (if y = (o e).fst then (1 : ℤ) else 0) ≤ d :=
    fun y => (sum_fst_le_degree G o ho y).trans (by exact_mod_cast hdeg y)
  have h1 := sum_ind_pair_le (fun e a => ((vB ((o e).fst - a), vC (o e).snd) : Vc n × Vc n))
    (fun e a b h => by simpa [vB_inj] using h) (fun α => α.2.2) (fun e => (o e).snd)
    (fun e a => rfl) α
  have h2 := sum_ind_pair_le (fun e a => ((vC (o e).snd, vA a) : Vc n × Vc n))
    (fun e a b h => by simpa [vA_inj] using h) (fun α => α.1.2) (fun e => (o e).snd)
    (fun e a => rfl) α
  have h3 := sum_ind_pair_le (fun e a => ((vB ((o e).fst - a), vC (o e).fst) : Vc n × Vc n))
    (fun e a b h => by simpa [vB_inj] using h) (fun α => α.2.2) (fun e => (o e).fst)
    (fun e a => rfl) α
  have h4 := sum_ind_pair_le (fun e a => ((vC (o e).fst, vA a) : Vc n × Vc n))
    (fun e a b h => by simpa [vA_inj] using h) (fun α => α.1.2) (fun e => (o e).fst)
    (fun e a => rfl) α
  have := hs α.2.2; have := hs α.1.2; have := hf α.2.2; have := hf α.1.2
  refine (Finset.sum_le_sum fun q _ => abs_ind_add4 _ _ _ _ α).trans ?_
  simp only [Finset.sum_add_distrib]
  push_cast
  linarith

include ho in
/-- Each arc lies in at most `(2d)^2` rectangles. -/
theorem rect_count (d : ℕ) (hdeg : ∀ v, G.degree v ≤ d) (α : Vc n × Vc n) :
    ∑ r : ZMod 3 × G.edgeSet × G.edgeSet, |rect G o r.1 r.2.1 r.2.2 α| ≤ (2 * d) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single α.1.1]
  · rw [Fintype.sum_prod_type]
    unfold rect
    by_cases h : α.2.1 = α.1.1 + 1
    · simp only [h, and_self, if_true, abs_mul]
      rw [← Finset.sum_mul_sum]
      have h1 := sum_abs_incZ_le G o ho d hdeg α.1.2
      have h2 := sum_abs_incZ_le G o ho d hdeg α.2.2
      rw [sq]
      push_cast
      exact mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    · simp [h]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro r _
    simp [rect, Ne.symm hi]
  · simp

end FaceCounts

section Profiles

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The indicator function of an arc set. -/
def chiF (L : Finset (W × W)) : W × W → ℤ := fun α => if α ∈ L then 1 else 0

theorem outF_chiF (L : Finset (W × W)) (w : W) : outF (chiF L) w = outDeg L w := by
  unfold outF chiF outDeg
  rw [Finset.sum_boole]
  push_cast
  congr 1
  apply Finset.card_bij (fun y _ => (w, y))
  · intro y hy; simp only [mem_filter, mem_univ, true_and] at hy; simp [hy]
  · intro y _ y' _ h; simpa using h
  · intro α hα
    simp only [mem_filter] at hα
    refine ⟨α.2, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; rw [← hα.2]; exact hα.1
    · rw [← hα.2]

theorem inF_chiF (L : Finset (W × W)) (w : W) : inF (chiF L) w = inDeg L w := by
  unfold inF chiF inDeg
  rw [Finset.sum_boole]
  push_cast
  congr 1
  apply Finset.card_bij (fun x _ => (x, w))
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx; simp [hx]
  · intro x _ x' _ h; simpa using h
  · intro α hα
    simp only [mem_filter] at hα
    refine ⟨α.1, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; rw [← hα.2]; exact hα.1
    · rw [← hα.2]

theorem chiF_circ (L : Finset (W × W)) (hL : Balanced L) : IsCircF (chiF L) := by
  intro w; rw [inF_chiF, outF_chiF, hL w]

end Profiles

section Totals

variable (L : Finset (Vc n × Vc n))

omit [NeZero n] in
theorem sum_outDeg_class (i : ZMod 3) :
    ∑ x : Fin n, outDeg L (i, x) = (L.filter (fun α => α.1.1 = i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun α => α.1.2) (t := univ)
    (fun _ _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro x _
  unfold outDeg
  congr 1
  ext α
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]⟩, by rw [h2]⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, Prod.ext h2 h3⟩

omit [NeZero n] in
theorem sum_inDeg_class (i : ZMod 3) :
    ∑ x : Fin n, inDeg L (i, x) = (L.filter (fun α => α.2.1 = i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun α => α.2.2) (t := univ)
    (fun _ _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro x _
  unfold inDeg
  congr 1
  ext α
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]⟩, by rw [h2]⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, Prod.ext h2 h3⟩

theorem class_total_step (hLQ : L ⊆ Qc n) (hbal : Balanced L) (i : ZMod 3) :
    ∑ x : Fin n, outDeg L (i + 1, x) = ∑ x : Fin n, outDeg L (i, x) := by
  have h1 : ∑ x : Fin n, outDeg L (i + 1, x) = ∑ x : Fin n, inDeg L (i + 1, x) :=
    Finset.sum_congr rfl fun x _ => (hbal _).symm
  rw [h1, sum_inDeg_class, sum_outDeg_class]
  congr 1
  apply Finset.filter_congr
  intro α hα
  have := (mem_Qc n α).mp (hLQ hα)
  rw [this]
  constructor
  · intro h; exact add_right_cancel h
  · intro h; rw [h]

theorem class_totals (hLQ : L ⊆ Qc n) (hbal : Balanced L) :
    ∑ x : Fin n, outDeg L (vB x) = ∑ x : Fin n, outDeg L (vA x) ∧
      ∑ x : Fin n, outDeg L (vC x) = ∑ x : Fin n, outDeg L (vA x) := by
  have h01 := class_total_step L hLQ hbal 0
  have h12 := class_total_step L hLQ hbal 1
  simp only [vA, vB, vC]
  have e1 : (0 : ZMod 3) + 1 = 1 := by decide
  have e2 : (1 : ZMod 3) + 1 = 2 := by decide
  rw [e1] at h01; rw [e2] at h12
  exact ⟨h01, h12.trans h01⟩

theorem outDeg_le_n (hLQ : L ⊆ Qc n) (w : Vc n) : outDeg L w ≤ n := by
  unfold outDeg
  calc (L.filter (fun α => α.1 = w)).card ≤ (univ : Finset (Fin n)).card := by
        refine card_le_card_of_injOn (fun α => α.2.2) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
        intro α hα β hβ h
        simp only [coe_filter, Set.mem_setOf_eq] at hα hβ
        have hα2 := (mem_Qc n α).mp (hLQ hα.1)
        have hβ2 := (mem_Qc n β).mp (hLQ hβ.1)
        apply Prod.ext
        · rw [hα.2, hβ.2]
        · apply Prod.ext
          · rw [hα2, hβ2, hα.2, hβ.2]
          · exact h
    _ = n := by simp

end Totals

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
