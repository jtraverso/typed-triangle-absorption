/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

@[expose] public section

/-!
# An obstruction: `CompleteInverseCert` fails when a class is an isolated monochromatic class

Call a class `i` *isolated monochromatic* for `F` if `{i,i,i} ∈ F` and every type of `F` that
meets `i` is `{i,i,i}`. Then `CompleteInverseCert F` is **false**: its hypotheses allow a host
with four classes of exactly four vertices (`n = 16`, `γ = 1/4`, so `γ n = 4`), and in a `K₄`
the zero-row edge function

`r(ab) = r(cd) = 1`, `r(ac) = r(bd) = -1`, `r(ad) = r(bc) = 0`

is orthogonal to the boundary of each of the four triangles of `K₄`, while `∑ r² = 4 > 0`. Its
class totals vanish, so `SpanCompat` holds with zero coefficients, but no triangle chain
supported on `F`-copies has boundary `r` (every copy meeting class `i` lies inside class `i`).

So for the 57 disconnected `ThreeStepLinks` classes of the census that have an isolated
monochromatic class, the reduction `PaddedGeneral.keevashPaddedSpec_of_certs` can not be used
as stated; one needs a certificate restricted to larger classes
(see `PROOF_CHARGE_COMPONENTS_20261013.md`).
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedGeneral

/-- Class `i` is isolated monochromatic: `{i,i,i} ∈ F` and every type meeting `i` is `{i,i,i}`. -/
def IsolatedMono (F : Finset (Multiset (Fin 4))) (i : Fin 4) : Prop :=
  ({i, i, i} : Multiset (Fin 4)) ∈ F ∧ ∀ τ ∈ F, 0 < τ.count i → τ = {i, i, i}

instance (F : Finset (Multiset (Fin 4))) (i : Fin 4) : Decidable (IsolatedMono F i) := by
  unfold IsolatedMono; infer_instance

/-- The zero-row function on `K₄`. -/
def obsM : Fin 4 → Fin 4 → ℤ := ![![0, 1, -1, 0], ![1, 0, 0, -1], ![-1, 0, 0, 1], ![0, -1, 1, 0]]

theorem obsM_symm : ∀ x y, obsM x y = obsM y x := by decide

theorem obsM_diag : ∀ x, obsM x x = 0 := by decide

theorem obsM_triangle : ∀ x y w, x ≠ y → x ≠ w → y ≠ w → obsM x y + obsM x w + obsM y w = 0 := by
  decide

theorem obsM_values : ∀ x y, obsM x y = -1 ∨ obsM x y = 0 ∨ obsM x y = 1 := by decide

theorem obsM_sum : ∑ x : Fin 4, ∑ y : Fin 4, obsM x y = 0 := by decide

/-- The obstructing demand, inside class `i` of `Fin 4 × Fin 4`. -/
def obsDemand (i : Fin 4) : Sym2 (Fin 4 × Fin 4) → ℝ :=
  Sym2.lift ⟨fun u v => if u.1 = i ∧ v.1 = i then (obsM u.2 v.2 : ℝ) else 0, by
    intro u v
    dsimp only
    by_cases h : u.1 = i ∧ v.1 = i
    · have h' : v.1 = i ∧ u.1 = i := ⟨h.2, h.1⟩
      simp only [h, and_self, ite_true, obsM_symm u.2 v.2]
    · have h' : ¬ (v.1 = i ∧ u.1 = i) := fun h' => h ⟨h'.2, h'.1⟩
      simp only [h, h', ite_false]⟩

theorem obsDemand_mk (i : Fin 4) (u v : Fin 4 × Fin 4) :
    obsDemand i s(u, v) = if u.1 = i ∧ v.1 = i then (obsM u.2 v.2 : ℝ) else 0 := rfl

theorem classVertices_card_prod (j : Fin 4) :
    (classVertices (Prod.fst : Fin 4 × Fin 4 → Fin 4) j).card = 4 := by
  unfold classVertices
  revert j
  decide

theorem triEdges_three' {V : Type*} [DecidableEq V] {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
      Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]

/-- The pairing of `obsDemand` with the edges of any `F`-copy vanishes. -/
theorem obsDemand_copy_sum {F : Finset (Multiset (Fin 4))} {i : Fin 4} (hF : IsolatedMono F i)
    (T : Finset (Fin 4 × Fin 4))
    (hT : IsCopy (Prod.fst : Fin 4 × Fin 4 → Fin 4) F
      (activeCompleteGraph (Prod.fst : Fin 4 × Fin 4 → Fin 4) F) T) :
    ∑ e ∈ triEdges T, obsDemand i e = 0 := by
  have hcard : T.card = 3 := hT.1.card_eq
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hcard
  rw [triEdges_three' huv huw hvw]
  have h1 : s(u, v) ∉ ({s(u, w), s(v, w)} : Finset (Sym2 (Fin 4 × Fin 4))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    intro h
    rcases h with (⟨_, h⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)
    · exact hvw h
    · exact huw h
    · exact huv h
    · exact huw h
  have h2 : s(u, w) ∉ ({s(v, w)} : Finset (Sym2 (Fin 4 × Fin 4))) := by
    simp only [Finset.mem_singleton, Sym2.eq_iff]
    intro h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩
    · exact huv h
    · exact huw h
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton,
    obsDemand_mk, obsDemand_mk, obsDemand_mk]
  by_cases hmeet : u.1 = i ∨ v.1 = i ∨ w.1 = i
  · have hcount : 0 < ((({u, v, w} : Finset (Fin 4 × Fin 4)).val.map Prod.fst).count i) := by
      rw [Multiset.count_pos, Multiset.mem_map]
      rcases hmeet with h | h | h
      · exact ⟨u, by simp, h⟩
      · exact ⟨v, by simp, h⟩
      · exact ⟨w, by simp, h⟩
    have htype := hF.2 _ hT.2 hcount
    have hall : ∀ x ∈ ({u, v, w} : Finset (Fin 4 × Fin 4)), x.1 = i := by
      intro x hx
      have hm : x.1 ∈ (({u, v, w} : Finset (Fin 4 × Fin 4)).val.map Prod.fst) :=
        Multiset.mem_map.mpr ⟨x, hx, rfl⟩
      rw [htype] at hm
      simpa using hm
    have hu := hall u (by simp)
    have hv := hall v (by simp)
    have hw := hall w (by simp)
    have hne : ∀ x y : Fin 4 × Fin 4, x.1 = i → y.1 = i → x ≠ y → x.2 ≠ y.2 := by
      intro x y hx hy hxy h
      exact hxy (Prod.ext (hx.trans hy.symm) h)
    simp only [hu, hv, hw, and_self, ite_true]
    have := obsM_triangle u.2 v.2 w.2 (hne u v hu hv huv) (hne u w hu hw huw)
      (hne v w hv hw hvw)
    rw [← add_assoc]
    exact_mod_cast this
  · push Not at hmeet
    simp [hmeet.1, hmeet.2.1, hmeet.2.2]

theorem obsDemand_supported {F : Finset (Multiset (Fin 4))} {i : Fin 4} (hF : IsolatedMono F i) :
    Sym2DemandSupported (Prod.fst : Fin 4 × Fin 4 → Fin 4) F (obsDemand i) := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [obsDemand_mk]
    split_ifs with h
    · by_contra hne
      apply he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨?_, i, ?_⟩
      · intro huv
        subst huv
        exact hne (by rw [obsM_diag]; simp)
      · rw [h.1, h.2]; exact hF.1
    · rfl

theorem obsDemand_bound (i : Fin 4) (e : Sym2 (Fin 4 × Fin 4)) : |obsDemand i e| ≤ 1 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [obsDemand_mk]
    split_ifs
    · rcases obsM_values u.2 v.2 with h | h | h <;> rw [h] <;> norm_num
    · norm_num

theorem obsDemand_span (F : Finset (Multiset (Fin 4))) (i : Fin 4) :
    SpanCompat (Prod.fst : Fin 4 × Fin 4 → Fin 4) F (obsDemand i) := by
  refine ⟨fun _ => 0, ?_⟩
  simp only [zero_smul, Finset.sum_const_zero]
  funext j k
  simp only [classTotal, classRow, classVertices, Finset.sum_filter, Pi.zero_apply,
    Fintype.sum_prod_type, obsDemand_mk]
  by_cases hjk : j = i ∧ k = i
  · obtain ⟨hj, hk⟩ := hjk
    rw [hj, hk]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [hx])]
    simp only [ite_true]
    rw [Finset.sum_congr rfl (fun x1 _ => Fintype.sum_eq_single i (fun x2 hx2 => by simp [hx2]))]
    simp only [ite_true, and_self]
    exact_mod_cast obsM_sum
  · apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro x1 _
    split_ifs with h1
    · apply Finset.sum_eq_zero; intro x2 _; apply Finset.sum_eq_zero; intro x3 _
      split_ifs with h2 h3
      · exact absurd ⟨h1.symm.trans h3.1, h2.symm.trans h3.2⟩ hjk
      · rfl
      · rfl
    · rfl

/-- **Obstruction.** If some class is isolated monochromatic, `CompleteInverseCert F` is false. -/
theorem not_completeInverseCert_of_isolatedMono (F : Finset (Multiset (Fin 4))) (i : Fin 4)
    (hF : IsolatedMono F i) : ¬ CompleteInverseCert F := by
  intro hI
  have hcardV : (Fintype.card (Fin 4 × Fin 4) : ℝ) = 16 := by
    simp [Fintype.card_prod]
  have hcs : ∀ j, classSize (Prod.fst : Fin 4 × Fin 4 → Fin 4) j = 4 := by
    intro j
    unfold classSize
    rw [classVertices_card_prod]; norm_num
  obtain ⟨z, hzs, hzr, -⟩ := hI (Fin 4 × Fin 4) Prod.fst (obsDemand i) 1 (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hcardV]; norm_num)
    (by intro j; rw [hcs, hcardV]; norm_num) (obsDemand_supported hF)
    (obsDemand_bound i) (obsDemand_span F i)
  set r := obsDemand i
  have hswap : (∑ e : Sym2 (Fin 4 × Fin 4), r e * boundary z e) =
      ∑ T : Finset (Fin 4 × Fin 4), z T * ∑ e ∈ triEdges T, r e := by
    simp only [boundary, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => e ∈ triEdges T)]
    have hf : Finset.univ.filter (fun e => e ∈ triEdges T) = triEdges T := by
      ext e; simp
    rw [hf]
    have h0 : ∑ e ∈ Finset.univ.filter (fun e => e ∉ triEdges T),
        r e * (z T * (if e ∈ triEdges T then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp only [(Finset.mem_filter.mp he).2, ite_false]; ring
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro e he
    simp only [he, ite_true]; ring
  have hzero : (∑ T : Finset (Fin 4 × Fin 4), z T * ∑ e ∈ triEdges T, r e) = 0 := by
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : IsCopy (Prod.fst : Fin 4 × Fin 4 → Fin 4) F
      (activeCompleteGraph (Prod.fst : Fin 4 × Fin 4 → Fin 4) F) T
    · rw [obsDemand_copy_sum hF T hT, mul_zero]
    · rw [hzs T hT, zero_mul]
  have hpos : (1 : ℝ) ≤ ∑ e : Sym2 (Fin 4 × Fin 4), r e * boundary z e := by
    rw [hzr]
    have hle := Finset.single_le_sum (f := fun e => r e * r e)
      (fun e _ => mul_self_nonneg (r e)) (Finset.mem_univ s(((i, 0) : Fin 4 × Fin 4), (i, 1)))
    have hval : r s(((i, 0) : Fin 4 × Fin 4), (i, 1)) = 1 := by
      simp only [r, obsDemand_mk, and_self, ite_true]
      norm_num [obsM]
    simp only [hval, mul_one] at hle
    exact hle
  rw [hswap, hzero] at hpos
  norm_num at hpos

/-- Example: the first `ℤ/3` row of the census, `{000, 001, 002, 333}`. -/
theorem not_completeInverseCert_example :
    ¬ CompleteInverseCert ({{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {3, 3, 3}} :
      Finset (Multiset (Fin 4))) :=
  not_completeInverseCert_of_isolatedMono _ 3 (by decide)

end PaddedComponents

#print axioms PaddedComponents.not_completeInverseCert_of_isolatedMono
#print axioms PaddedComponents.not_completeInverseCert_example
