/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Target
public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.LatticeBasics

@[expose] public section

/-!
# The Latin core as a flow condition

`isIntDiv_latin_iff`: on allowed edge sets, `IsIntDiv p F_latin E` holds iff every vertex is
balanced for the cyclic orientation `0 → 1 → {2,3} → 0` (`flowCharge p E v = 0`).

`sum_flowCharge`: the conservation law `∑ v, flowCharge p E v = 0` for every edge set, and
`flowCharge_eq_zero_of_forall_ne`: no edge set changes the charge of a single vertex only.
-/
namespace PartitionedTriangleAbsorption.BlowupB.LatinCore

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse

/-- The cyclic orientation `0 → 1 → {2, 3} → 0` of the allowed class pairs of `F_latin`:
`latinOrient i j = 1` if `i → j`, `-1` if `j → i`, and `0` otherwise. -/
def latinOrient : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, -1, -1], ![-1, 0, 1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem latinOrient_antisymm : ∀ i j : Fin 4, latinOrient i j = - latinOrient j i := by decide

theorem latinOrient_apply :
    latinOrient 0 0 = 0 ∧
    latinOrient 0 1 = 1 ∧
    latinOrient 0 2 = (-1) ∧
    latinOrient 0 3 = (-1) ∧
    latinOrient 1 0 = (-1) ∧
    latinOrient 1 1 = 0 ∧
    latinOrient 1 2 = 1 ∧
    latinOrient 1 3 = 1 ∧
    latinOrient 2 0 = 1 ∧
    latinOrient 2 1 = (-1) ∧
    latinOrient 2 2 = 0 ∧
    latinOrient 2 3 = 0 ∧
    latinOrient 3 0 = 1 ∧
    latinOrient 3 1 = (-1) ∧
    latinOrient 3 2 = 0 ∧
    latinOrient 3 3 = 0 := by decide

theorem typeDegVec_012_apply :
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 0 0 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 0 1 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 0 2 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 0 3 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 1 0 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 1 1 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 1 2 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 1 3 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 2 0 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 2 1 = 1 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 2 2 = 0 ∧
    typeDegVec ({0, 1, 2} : Multiset (Fin 4)) 2 3 = 0 := by decide

theorem typeEdgeVec_012_apply :
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 0 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 1 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 2 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 0 3 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 1 0 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 1 1 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 1 2 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 1 3 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 2 0 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 2 1 = 1 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 2 2 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 2 3 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 3 0 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 3 1 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 3 2 = 0 ∧
    typeEdgeVec ({0, 1, 2} : Multiset (Fin 4)) 3 3 = 0 := by decide

theorem typeDegVec_013_apply :
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 0 0 = 0 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 0 1 = 1 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 0 2 = 0 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 0 3 = 1 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 1 0 = 1 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 1 1 = 0 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 1 2 = 0 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 1 3 = 1 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 3 0 = 1 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 3 1 = 1 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 3 2 = 0 ∧
    typeDegVec ({0, 1, 3} : Multiset (Fin 4)) 3 3 = 0 := by decide

theorem typeEdgeVec_013_apply :
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 0 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 1 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 2 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 0 3 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 1 0 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 1 1 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 1 2 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 1 3 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 2 0 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 2 1 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 2 2 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 2 3 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 3 0 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 3 1 = 1 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 3 2 = 0 ∧
    typeEdgeVec ({0, 1, 3} : Multiset (Fin 4)) 3 3 = 0 := by decide


variable {V : Type*} [DecidableEq V]

/-- The flow charge of `v`: out-degree minus in-degree for the cyclic orientation. -/
def flowCharge (p : V → Fin 4) (E : Finset (Sym2 V)) (v : V) : ℤ :=
  ∑ i, latinOrient (p v) i * degVec p E v i

theorem sum_flowCharge_edge [Fintype V] (p : V → Fin 4) (e : Sym2 V) :
    ∑ v, ∑ i, latinOrient (p v) i * degContrib p v e i = 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero]
    have h1 : ∀ v : V, (∑ i, if a = v ∧ p b = i then latinOrient (p v) i else 0) =
        if a = v then latinOrient (p v) (p b) else 0 := by
      intro v
      by_cases hv : a = v
      · simp [hv]
      · simp [hv]
    have h2 : ∀ v : V, (∑ i, if b = v ∧ p a = i then latinOrient (p v) i else 0) =
        if b = v then latinOrient (p v) (p a) else 0 := by
      intro v
      by_cases hv : b = v
      · simp [hv]
      · simp [hv]
    simp only [h1, h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [latinOrient_antisymm (p a) (p b)]
    ring

/-- **Conservation law** (finding 1). For every finite edge set whatsoever, the flow charges of all
vertices sum to zero. -/
theorem sum_flowCharge [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V)) :
    ∑ v, flowCharge p E v = 0 := by
  have h : ∀ v, flowCharge p E v = ∑ e ∈ E, ∑ i, latinOrient (p v) i * degContrib p v e i := by
    intro v
    simp only [flowCharge, degVec, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun e _ => sum_flowCharge_edge p e

/-- **No single-vertex charge token.** An edge set whose flow charge vanishes at every vertex
other than `x` has zero flow charge at `x` as well. -/
theorem flowCharge_eq_zero_of_forall_ne [Finite V] (p : V → Fin 4) (E : Finset (Sym2 V)) (x : V)
    (h : ∀ y, y ≠ x → flowCharge p E y = 0) : flowCharge p E x = 0 := by
  cases nonempty_fintype V
  have hs := sum_flowCharge p E
  rwa [Finset.sum_eq_single x (fun y _ hy => h y hy) (by simp)] at hs

theorem latin_ne : ({0, 1, 2} : Multiset (Fin 4)) ≠ {0, 1, 3} := by decide

/-- The flow functional kills every type degree vector of `F_latin`. -/
theorem latin_kill : ∀ r : Fin 4, ∀ τ ∈ F_latin, r ∈ τ →
    ∑ i, latinOrient r i * typeDegVec τ r i = 0 := by
  unfold F_latin; decide

/-- The local lattice of `F_latin`, solved: a degree vector supported on the link of `r` with zero
flow charge is an integral combination of the type degree vectors. -/
theorem latin_local (r : Fin 4) (d : Fin 4 → ℤ) (hsupp : ∀ j, d j ≠ 0 → ∃ l, Link F_latin r j l)
    (hflow : ∑ j, latinOrient r j * d j = 0) :
    ∃ c : Multiset (Fin 4) → ℤ, d = ∑ τ ∈ F_latin with r ∈ τ, c τ • typeDegVec τ r := by
  have hz : ∀ j, ¬ (∃ l, Link F_latin r j l) → d j = 0 := fun j hj => by
    by_contra h; exact hj (hsupp j h)
  simp only [Fin.sum_univ_four] at hflow
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by fin_cases r <;> simp
  · have h0 := hz 0 (by unfold Link F_latin; decide)
    refine ⟨fun τ => if τ = {0, 1, 2} then d 2 else d 3, ?_⟩
    have hf : F_latin.filter (fun τ => (0 : Fin 4) ∈ τ) = {{0, 1, 2}, {0, 1, 3}} := by
      unfold F_latin; decide
    rw [hf, sum_pair latin_ne]
    simp only [latinOrient_apply] at hflow
    funext i
    fin_cases i <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_pos, if_neg latin_ne.symm] <;>
        simp only [Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_012_apply, typeDegVec_013_apply] <;> linarith
  · have h1 := hz 1 (by unfold Link F_latin; decide)
    refine ⟨fun τ => if τ = {0, 1, 2} then d 2 else d 3, ?_⟩
    have hf : F_latin.filter (fun τ => (1 : Fin 4) ∈ τ) = {{0, 1, 2}, {0, 1, 3}} := by
      unfold F_latin; decide
    rw [hf, sum_pair latin_ne]
    simp only [latinOrient_apply] at hflow
    funext i
    fin_cases i <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_pos, if_neg latin_ne.symm] <;>
        simp only [Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_012_apply, typeDegVec_013_apply] <;> linarith
  · have h2 := hz 2 (by unfold Link F_latin; decide)
    have h3 := hz 3 (by unfold Link F_latin; decide)
    refine ⟨fun _ => d 0, ?_⟩
    have hf : F_latin.filter (fun τ => (2 : Fin 4) ∈ τ) = {{0, 1, 2}} := by
      unfold F_latin; decide
    rw [hf, sum_singleton]
    simp only [latinOrient_apply] at hflow
    funext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_012_apply] <;> linarith
  · have h2 := hz 2 (by unfold Link F_latin; decide)
    have h3 := hz 3 (by unfold Link F_latin; decide)
    refine ⟨fun _ => d 0, ?_⟩
    have hf : F_latin.filter (fun τ => (3 : Fin 4) ∈ τ) = {{0, 1, 3}} := by
      unfold F_latin; decide
    rw [hf, sum_singleton]
    simp only [latinOrient_apply] at hflow
    funext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk, typeDegVec_013_apply] <;> linarith

/-- Integral divisibility forces zero flow charge at every vertex. -/
theorem flowCharge_eq_zero_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : IsIntDiv p F_latin E) (v : V) : flowCharge p E v = 0 := by
  obtain ⟨c, hc⟩ := h.2 v
  unfold flowCharge
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  obtain ⟨hτF, hvτ⟩ := Finset.mem_filter.mp hτ
  have hk := latin_kill (p v) τ hτF hvτ
  calc ∑ i, latinOrient (p v) i * (c τ * typeDegVec τ (p v) i)
      = c τ * ∑ i, latinOrient (p v) i * typeDegVec τ (p v) i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hk, mul_zero]

/-- A class-summed balance: `∑_j o(r,j) e(r,j) = ∑_{v ∈ V_r} flowCharge v`. -/
theorem sum_orient_edgeVec [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V)) (r : Fin 4) :
    ∑ j, latinOrient r j * edgeVec p E r j =
      ∑ v ∈ univ.filter (fun v => p v = r), flowCharge p E v := by
  simp only [StructuralF3General.LatticeBasics.edgeVec_eq_sum_degVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [flowCharge, (Finset.mem_filter.mp hv).2]

/-- **Finding 1, formally.** On allowed support, integral `F_latin`-divisibility is exactly the
Eulerian condition: zero flow charge at every vertex. -/
theorem isIntDiv_latin_iff [Finite V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F_latin p E) :
    IsIntDiv p F_latin E ↔ ∀ v, flowCharge p E v = 0 := by
  cases nonempty_fintype V
  constructor
  · exact fun h v => flowCharge_eq_zero_of_isIntDiv p E h v
  intro hflow
  have hsupp : ∀ v j, degVec p E v j ≠ 0 → ∃ l, Link F_latin (p v) j l := by
    intro v j hj
    obtain ⟨b, hb, hpb⟩ := exists_of_degVec_ne_zero hj
    exact hpb ▸ hact v b hb
  refine ⟨?_, fun v => latin_local (p v) (degVec p E v) (hsupp v) (hflow v)⟩
  have hzero : ∀ i j, ¬ (∃ l, Link F_latin i j l) → edgeVec p E i j = 0 := by
    intro i j hij
    rw [StructuralF3General.LatticeBasics.edgeVec_eq_sum_degVec]
    refine Finset.sum_eq_zero fun v hv => ?_
    by_contra hne
    exact hij ((Finset.mem_filter.mp hv).2 ▸ hsupp v j hne)
  have hbal : ∀ r, ∑ j, latinOrient r j * edgeVec p E r j = 0 := fun r => by
    rw [sum_orient_edgeVec]; exact Finset.sum_eq_zero fun v _ => hflow v
  have hsym := StructuralF3General.LatticeBasics.edgeVec_symm p E
  have b0 := hbal 0
  have b1 := hbal 1
  have b2 := hbal 2
  have b3 := hbal 3
  simp only [Fin.sum_univ_four, latinOrient_apply] at b0 b1 b2 b3
  have z00 := hzero 0 0 (by unfold Link F_latin; decide)
  have z11 := hzero 1 1 (by unfold Link F_latin; decide)
  have z22 := hzero 2 2 (by unfold Link F_latin; decide)
  have z33 := hzero 3 3 (by unfold Link F_latin; decide)
  have z23 := hzero 2 3 (by unfold Link F_latin; decide)
  have z32 := hzero 3 2 (by unfold Link F_latin; decide)
  have s01 := hsym 0 1
  have s02 := hsym 0 2
  have s03 := hsym 0 3
  have s12 := hsym 1 2
  have s13 := hsym 1 3
  refine ⟨fun τ => if τ = {0, 1, 2} then edgeVec p E 0 2 else edgeVec p E 0 3, ?_⟩
  unfold F_latin
  rw [sum_pair latin_ne]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_pos, if_neg latin_ne.symm,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, typeEdgeVec_012_apply,
      typeEdgeVec_013_apply] <;> linarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.sum_flowCharge
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.flowCharge_eq_zero_of_forall_ne
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.isIntDiv_latin_iff


