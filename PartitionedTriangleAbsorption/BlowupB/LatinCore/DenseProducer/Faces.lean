/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.ExpanderFlow
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.ExactCover

@[expose] public section

/-!
# The fixed face catalogue on the padded blow-up (§§5–6)

The padded vertex set is `Vc n = ZMod 3 × Fin n` (colour class, position); `Qc n` is the complete
cyclically tripartite digraph on it.  Arc functions `Vc n × Vc n → ℤ` with values in `{-1,0,1}`
are turned into positivization faces by `faceOf`.

The four face families (all chosen before the demand):

* `tri a b c`: the triangle `(0,a) → (1,b) → (2,c) → (0,a)` (used with `c = a + b`, the Latin
  triangles);
* `mB e a`: the difference of the triangles `(a, s, a+f)` and `(a, f, a+f)` where `f → s` is the
  reference orientation of the expander edge `e` (moves the `B`-corner along `e`);
* `mC e a`: the difference of the triangles `(a, f-a, s)` and `(a, f-a, f)` (moves the
  `C`-corner along `e`);
* `rect i e e'`: the signed rectangle of block `i → i+1` given by the tensor product of the
  incidence columns of `e` and `e'`.

Every face is a circulation supported in `Qc n` with at most four arcs, and we record the vertex
out-profile of each family.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Positivization Cycles

section Generic

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Out-flow of an arc function at a vertex. -/
def outF (f : W × W → ℤ) (w : W) : ℤ := ∑ y, f (w, y)

/-- In-flow of an arc function at a vertex. -/
def inF (f : W × W → ℤ) (w : W) : ℤ := ∑ x, f (x, w)

/-- Arc functions that are signed circulations. -/
def IsCircF (f : W × W → ℤ) : Prop := ∀ w, inF f w = outF f w

/-- Values in `{-1, 0, 1}`. -/
def IsUnitF (f : W × W → ℤ) : Prop := ∀ α, f α = -1 ∨ f α = 0 ∨ f α = 1

/-- Indicator of a single arc. -/
def ind (α : W × W) : W × W → ℤ := fun β => if β = α then 1 else 0

theorem outF_add (f g : W × W → ℤ) (w : W) : outF (f + g) w = outF f w + outF g w := by
  simp [outF, Finset.sum_add_distrib]

theorem inF_add (f g : W × W → ℤ) (w : W) : inF (f + g) w = inF f w + inF g w := by
  simp [inF, Finset.sum_add_distrib]

theorem outF_sub (f g : W × W → ℤ) (w : W) : outF (f - g) w = outF f w - outF g w := by
  simp [outF, Finset.sum_sub_distrib]

theorem inF_sub (f g : W × W → ℤ) (w : W) : inF (f - g) w = inF f w - inF g w := by
  simp [inF, Finset.sum_sub_distrib]

theorem outF_sum {ι : Type} (s : Finset ι) (c : ι → ℤ) (f : ι → W × W → ℤ) (w : W) :
    outF (∑ i ∈ s, c i • f i) w = ∑ i ∈ s, c i * outF (f i) w := by
  simp only [outF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

theorem inF_sum {ι : Type} (s : Finset ι) (c : ι → ℤ) (f : ι → W × W → ℤ) (w : W) :
    inF (∑ i ∈ s, c i • f i) w = ∑ i ∈ s, c i * inF (f i) w := by
  simp only [inF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

theorem outF_ind (α : W × W) (w : W) : outF (ind α) w = if α.1 = w then 1 else 0 := by
  unfold outF ind
  by_cases h : α.1 = w
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single α.2]
    · simp
    · intro y _ hy; rw [if_neg]; intro h'; exact hy (by rw [← h'])
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h'; exact h (by rw [← h'])

theorem inF_ind (α : W × W) (w : W) : inF (ind α) w = if α.2 = w then 1 else 0 := by
  unfold inF ind
  by_cases h : α.2 = w
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single α.1]
    · simp
    · intro y _ hy; rw [if_neg]; intro h'; exact hy (by rw [← h'])
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h'; exact h (by rw [← h'])

/-- The positivization face of a `{-1,0,1}`-valued arc function. -/
def faceOf (f : W × W → ℤ) : Face W :=
  ⟨univ.filter (fun α => f α ≠ 0), fun α => decide (0 < f α)⟩

theorem faceOf_val (f : W × W → ℤ) (hf : IsUnitF f) (α : W × W) :
    (faceOf f).val α = f α := by
  unfold Face.val faceOf oriSign
  simp only [mem_filter, mem_univ, true_and]
  rcases hf α with h | h | h <;> simp [h]

theorem faceOf_isCirc (f : W × W → ℤ) (hf : IsUnitF f) (hc : IsCircF f) :
    (faceOf f).IsCirc := by
  intro w
  have key : ∀ (p : W × W → Prop) [DecidablePred p],
      ∑ e ∈ (faceOf f).supp, oriSign ((faceOf f).ori e) * (if p e then 1 else 0) =
        ∑ e, f e * (if p e then 1 else 0) := by
    intro p _
    rw [← Finset.sum_subset (subset_univ (faceOf f).supp)]
    · apply Finset.sum_congr rfl
      intro e he
      have := faceOf_val f hf e
      unfold Face.val at this
      rw [if_pos he] at this
      rw [this]
    · intro e _ he
      simp only [faceOf, mem_filter, mem_univ, true_and, not_not] at he
      simp [he]
  rw [key (fun e => e.2 = w), key (fun e => e.1 = w)]
  have h1 : ∑ e : W × W, f e * (if e.2 = w then 1 else 0) = inF f w := by
    rw [Fintype.sum_prod_type]
    unfold inF
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single w]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  have h2 : ∑ e : W × W, f e * (if e.1 = w then 1 else 0) = outF f w := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
    · simp [outF]
    · intro x _ hx; simp [hx]
    · simp
  rw [h1, h2, hc w]

theorem faceOf_supp_subset (f : W × W → ℤ) (S : Finset (W × W)) (hS : ∀ α, f α ≠ 0 → α ∈ S) :
    (faceOf f).supp ⊆ S := by
  intro α hα
  simp only [faceOf, mem_filter, mem_univ, true_and] at hα
  exact hS α hα

theorem faceOf_supp_nonempty (f : W × W → ℤ) (α : W × W) (hα : f α ≠ 0) :
    (faceOf f).supp.Nonempty :=
  ⟨α, by simp [faceOf, hα]⟩

theorem mem_faceOf_supp (f : W × W → ℤ) (α : W × W) : α ∈ (faceOf f).supp ↔ f α ≠ 0 := by
  simp [faceOf]

theorem ne_of_fst_ne {α β : W × W} (h : α.1 ≠ β.1) : α ≠ β := fun h' => h (by rw [h'])

theorem ne_of_snd_ne {α β : W × W} (h : α.2 ≠ β.2) : α ≠ β := fun h' => h (by rw [h'])

theorem unit_three (p1 p2 p3 : W × W) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) :
    IsUnitF (ind p1 + ind p2 + ind p3) := by
  intro β
  simp only [Pi.add_apply, ind]
  by_cases h1 : β = p1 <;> by_cases h2 : β = p2 <;> by_cases h3 : β = p3 <;> simp_all

theorem unit_four (p1 p2 q1 q2 : W × W) (h1 : p1 ≠ p2) (h2 : p1 ≠ q1) (h3 : p1 ≠ q2)
    (h4 : p2 ≠ q1) (h5 : p2 ≠ q2) (h6 : q1 ≠ q2) :
    IsUnitF (ind p1 + ind p2 - ind q1 - ind q2) := by
  intro β
  simp only [Pi.add_apply, Pi.sub_apply, ind]
  by_cases k1 : β = p1 <;> by_cases k2 : β = p2 <;> by_cases k3 : β = q1 <;>
    by_cases k4 : β = q2 <;> simp_all

end Generic

/-! ### The padded blow-up -/

variable (n : ℕ) [NeZero n]

/-- Padded vertex set: colour class and position. -/
abbrev Vc := ZMod 3 × Fin n

/-- The complete cyclically tripartite digraph on `Vc n`. -/
def Qc : Finset (Vc n × Vc n) := univ.filter (fun α => α.2.1 = α.1.1 + 1)

theorem mem_Qc (α : Vc n × Vc n) : α ∈ Qc n ↔ α.2.1 = α.1.1 + 1 := by simp [Qc]

theorem Qc_isCyc : IsCyc (fun v : Vc n => v.1) (Qc n) := fun α hα => (mem_Qc n α).mp hα

variable {n}

/-- Vertices of the three classes. -/
def vA (x : Fin n) : Vc n := (0, x)
def vB (x : Fin n) : Vc n := (1, x)
def vC (x : Fin n) : Vc n := (2, x)

omit [NeZero n] in
theorem vA_ne_vB (x y : Fin n) : vA x ≠ vB y := by
  intro h; have h1 := congrArg Prod.fst h; simp only [vA, vB] at h1; exact absurd h1 (by decide)
omit [NeZero n] in
theorem vB_ne_vC (x y : Fin n) : vB x ≠ vC y := by
  intro h; have h1 := congrArg Prod.fst h; simp only [vB, vC] at h1; exact absurd h1 (by decide)
omit [NeZero n] in
theorem vC_ne_vA (x y : Fin n) : vC x ≠ vA y := by
  intro h; have h1 := congrArg Prod.fst h; simp only [vA, vC] at h1; exact absurd h1 (by decide)
omit [NeZero n] in
theorem vB_ne_vA (x y : Fin n) : vB x ≠ vA y := (vA_ne_vB y x).symm
omit [NeZero n] in
theorem vC_ne_vB (x y : Fin n) : vC x ≠ vB y := (vB_ne_vC y x).symm
omit [NeZero n] in
theorem vA_ne_vC (x y : Fin n) : vA x ≠ vC y := (vC_ne_vA y x).symm
theorem vA_inj {x y : Fin n} : vA x = vA y ↔ x = y := by simp [vA]
theorem vB_inj {x y : Fin n} : vB x = vB y ↔ x = y := by simp [vB]
theorem vC_inj {x y : Fin n} : vC x = vC y ↔ x = y := by simp [vC]

/-- The triangle `(0,a) → (1,b) → (2,c) → (0,a)`. -/
def tri (a b c : Fin n) : Vc n × Vc n → ℤ :=
  ind (vA a, vB b) + ind (vB b, vC c) + ind (vC c, vA a)

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (o : G.edgeSet → G.Dart)

/-- Move of the `B`-corner along the reference orientation `f → s` of `e`. -/
def mB (e : G.edgeSet) (a : Fin n) : Vc n × Vc n → ℤ :=
  ind (vA a, vB (o e).snd) + ind (vB (o e).snd, vC (a + (o e).fst)) -
    ind (vA a, vB (o e).fst) - ind (vB (o e).fst, vC (a + (o e).fst))

/-- Move of the `C`-corner along the reference orientation `f → s` of `e`. -/
def mC (e : G.edgeSet) (a : Fin n) : Vc n × Vc n → ℤ :=
  ind (vB ((o e).fst - a), vC (o e).snd) + ind (vC (o e).snd, vA a) -
    ind (vB ((o e).fst - a), vC (o e).fst) - ind (vC (o e).fst, vA a)

/-- The signed rectangle of block `i → i + 1` attached to the edges `e, e'`. -/
def rect (i : ZMod 3) (e e' : G.edgeSet) : Vc n × Vc n → ℤ := fun α =>
  if α.1.1 = i ∧ α.2.1 = i + 1 then incZ G o α.1.2 e * incZ G o α.2.2 e' else 0

/-! ### Values in `{-1,0,1}` -/

theorem tri_apply (a b c : Fin n) (α : Vc n × Vc n) :
    tri a b c α = (if α = (vA a, vB b) then 1 else 0) + (if α = (vB b, vC c) then 1 else 0) +
      (if α = (vC c, vA a) then 1 else 0) := rfl

theorem tri_unit (a b c : Fin n) : IsUnitF (tri a b c) :=
  unit_three _ _ _ (ne_of_fst_ne (vA_ne_vB _ _)) (ne_of_fst_ne (vA_ne_vC _ _))
    (ne_of_fst_ne (vB_ne_vC _ _))

variable {G o}

theorem dart_fst_ne_snd (d : G.Dart) : d.fst ≠ d.snd := d.adj.ne

variable (G o)

theorem mB_apply (e : G.edgeSet) (a : Fin n) (α : Vc n × Vc n) :
    mB G o e a α = (if α = (vA a, vB (o e).snd) then 1 else 0) +
      (if α = (vB (o e).snd, vC (a + (o e).fst)) then 1 else 0) -
      (if α = (vA a, vB (o e).fst) then 1 else 0) -
      (if α = (vB (o e).fst, vC (a + (o e).fst)) then 1 else 0) := rfl

theorem mC_apply (e : G.edgeSet) (a : Fin n) (α : Vc n × Vc n) :
    mC G o e a α = (if α = (vB ((o e).fst - a), vC (o e).snd) then 1 else 0) +
      (if α = (vC (o e).snd, vA a) then 1 else 0) -
      (if α = (vB ((o e).fst - a), vC (o e).fst) then 1 else 0) -
      (if α = (vC (o e).fst, vA a) then 1 else 0) := rfl

theorem mB_unit (e : G.edgeSet) (a : Fin n) : IsUnitF (mB G o e a) := by
  have hfs := dart_fst_ne_snd (o e)
  exact unit_four _ _ _ _ (ne_of_fst_ne (vA_ne_vB _ _))
    (ne_of_snd_ne (fun h => hfs (vB_inj.mp h).symm)) (ne_of_fst_ne (vA_ne_vB _ _))
    (ne_of_fst_ne (vB_ne_vA _ _)) (ne_of_fst_ne (fun h => hfs (vB_inj.mp h).symm))
    (ne_of_fst_ne (vA_ne_vB _ _))

theorem mC_unit (e : G.edgeSet) (a : Fin n) : IsUnitF (mC G o e a) := by
  have hfs := dart_fst_ne_snd (o e)
  exact unit_four _ _ _ _ (ne_of_fst_ne (vB_ne_vC _ _))
    (ne_of_snd_ne (fun h => hfs (vC_inj.mp h).symm)) (ne_of_fst_ne (vB_ne_vC _ _))
    (ne_of_fst_ne (vC_ne_vB _ _)) (ne_of_fst_ne (fun h => hfs (vC_inj.mp h).symm))
    (ne_of_fst_ne (vB_ne_vC _ _))

theorem incZ_unit (v : Fin n) (e : G.edgeSet) :
    incZ G o v e = -1 ∨ incZ G o v e = 0 ∨ incZ G o v e = 1 := by
  have hfs := dart_fst_ne_snd (o e)
  unfold incZ
  split_ifs with h1 h2 <;> simp_all

theorem rect_unit (i : ZMod 3) (e e' : G.edgeSet) : IsUnitF (rect G o i e e') := by
  intro α
  unfold rect
  split_ifs
  · rcases incZ_unit G o α.1.2 e with h | h | h <;>
      rcases incZ_unit G o α.2.2 e' with h' | h' | h' <;> simp [h, h']
  · simp

/-! ### Circulation -/

theorem tri_circ (a b c : Fin n) : IsCircF (tri a b c) := by
  intro w
  simp only [tri, inF_add, outF_add, inF_ind, outF_ind]
  ring

theorem mB_circ (e : G.edgeSet) (a : Fin n) : IsCircF (mB G o e a) := by
  intro w
  simp only [mB, inF_add, outF_add, inF_sub, outF_sub, inF_ind, outF_ind]
  ring

theorem mC_circ (e : G.edgeSet) (a : Fin n) : IsCircF (mC G o e a) := by
  intro w
  simp only [mC, inF_add, outF_add, inF_sub, outF_sub, inF_ind, outF_ind]
  ring

theorem sum_incZ (e : G.edgeSet) : ∑ v, incZ G o v e = 0 := by
  unfold incZ
  rw [Finset.sum_sub_distrib]
  simp

theorem rect_inF (i : ZMod 3) (e e' : G.edgeSet) (w : Vc n) : inF (rect G o i e e') w = 0 := by
  unfold inF rect
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · by_cases hw : w.1 = i + 1
    · simp only [hw, and_true, if_true]
      rw [← Finset.sum_mul, sum_incZ, zero_mul]
    · simp [hw]
  · intro j _ hj; simp [hj]
  · simp

theorem rect_outF (i : ZMod 3) (e e' : G.edgeSet) (w : Vc n) : outF (rect G o i e e') w = 0 := by
  unfold outF rect
  rw [Fintype.sum_prod_type]
  by_cases hw : w.1 = i
  · rw [Finset.sum_eq_single (i + 1)]
    · simp only [hw, true_and, if_true]
      rw [← Finset.mul_sum, sum_incZ, mul_zero]
    · intro j _ hj; simp [hj]
    · simp
  · simp [hw]

theorem rect_circ (i : ZMod 3) (e e' : G.edgeSet) : IsCircF (rect G o i e e') := by
  intro w; rw [rect_inF, rect_outF]

/-! ### Support in `Qc n` and size -/

theorem tri_supp (a b c : Fin n) (α : Vc n × Vc n) (h : tri a b c α ≠ 0) :
    α ∈ ({(vA a, vB b), (vB b, vC c), (vC c, vA a)} : Finset (Vc n × Vc n)) := by
  rw [tri_apply] at h
  simp only [mem_insert, mem_singleton]
  by_contra hc
  push_neg at hc
  simp [hc.1, hc.2.1, hc.2.2] at h

theorem mB_supp (e : G.edgeSet) (a : Fin n) (α : Vc n × Vc n) (h : mB G o e a α ≠ 0) :
    α ∈ ({(vA a, vB (o e).snd), (vB (o e).snd, vC (a + (o e).fst)), (vA a, vB (o e).fst),
      (vB (o e).fst, vC (a + (o e).fst))} : Finset (Vc n × Vc n)) := by
  rw [mB_apply] at h
  simp only [mem_insert, mem_singleton]
  by_contra hc
  push_neg at hc
  simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] at h

theorem mC_supp (e : G.edgeSet) (a : Fin n) (α : Vc n × Vc n) (h : mC G o e a α ≠ 0) :
    α ∈ ({(vB ((o e).fst - a), vC (o e).snd), (vC (o e).snd, vA a),
      (vB ((o e).fst - a), vC (o e).fst), (vC (o e).fst, vA a)} : Finset (Vc n × Vc n)) := by
  rw [mC_apply] at h
  simp only [mem_insert, mem_singleton]
  by_contra hc
  push_neg at hc
  simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] at h

theorem incZ_ne_zero {v : Fin n} {e : G.edgeSet} (h : incZ G o v e ≠ 0) :
    v = (o e).snd ∨ v = (o e).fst := by
  unfold incZ at h
  by_contra hc
  push_neg at hc
  simp [hc.1, hc.2] at h

theorem rect_supp (i : ZMod 3) (e e' : G.edgeSet) (α : Vc n × Vc n) (h : rect G o i e e' α ≠ 0) :
    α ∈ ({((i, (o e).snd), (i + 1, (o e').snd)), ((i, (o e).snd), (i + 1, (o e').fst)),
      ((i, (o e).fst), (i + 1, (o e').snd)), ((i, (o e).fst), (i + 1, (o e').fst))} :
        Finset (Vc n × Vc n)) := by
  unfold rect at h
  split_ifs at h with hi
  · obtain ⟨⟨i1, x⟩, ⟨i2, y⟩⟩ := α
    simp only at hi h
    obtain ⟨rfl, rfl⟩ := hi
    have hx := incZ_ne_zero G o (left_ne_zero_of_mul h)
    have hy := incZ_ne_zero G o (right_ne_zero_of_mul h)
    simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
  · exact absurd rfl h

theorem mem_Qc_A_B (x y : Fin n) : (vA x, vB y) ∈ Qc n := by
  rw [mem_Qc]; simp [vA, vB]
theorem mem_Qc_B_C (x y : Fin n) : (vB x, vC y) ∈ Qc n := by
  rw [mem_Qc]; simp [vB, vC]; decide
theorem mem_Qc_C_A (x y : Fin n) : (vC x, vA y) ∈ Qc n := by
  rw [mem_Qc]; simp [vC, vA]; decide

theorem card_le_four {α : Type} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
    (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))

theorem card_le_three {α : Type} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
