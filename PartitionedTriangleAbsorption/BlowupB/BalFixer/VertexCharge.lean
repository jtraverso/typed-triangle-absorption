/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.TokenLayerStruct

@[expose] public section

/-!
# The signed degree at one vertex as a class-pair charge

For a vertex `x` of a class whose link is bipartite (sides weighted by `σ = ±1`), the local
divisibility condition at `x` is `vcharge σ p x E = ∑ i, σ i * degVec p E x i = 0`.

To feed it to the token layer (whose charges are class-pair charges `charge χ p`), `x` is given a new
label `Fin.last t` (`relab p x`), and `chiV σ` weights the pairs (new label, old label `i`) by
`σ i`. Then `charge (chiV σ) (relab p x) E = vcharge σ p x E` on loopless edge sets.

* `vcharge_eq_charge`: the identification;
* `two_dvd_vcharge`: on an edge set even at `x`, with odd weights on the classes it reaches;
* `vcharge_eq_zero_of_isIntDiv`: the charge vanishes on integrally divisible edge sets.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {W : Type*} [DecidableEq W]

/-- `x` gets the new label `Fin.last t`, every other vertex keeps its label. -/
def relab (p : W → Fin t) (x : W) (w : W) : Fin (t + 1) :=
  if w = x then Fin.last t else (p w).castSucc

/-- The weight `σ i` on the ordered pair (new label, `i`), zero elsewhere. -/
def chiV (σ : Fin t → ℤ) (i j : Fin (t + 1)) : ℤ :=
  if h : i = Fin.last t ∧ j ≠ Fin.last t then σ (j.castPred h.2) else 0

/-- The signed degree of `x`. -/
def vcharge (σ : Fin t → ℤ) (p : W → Fin t) (x : W) (E : Finset (Sym2 W)) : ℤ :=
  ∑ i, σ i * degVec p E x i

theorem chiV_last_castSucc (σ : Fin t → ℤ) (i : Fin t) :
    chiV σ (Fin.last t) i.castSucc = σ i := by
  simp [chiV, Fin.castSucc_ne_last]

theorem chiV_castSucc (σ : Fin t → ℤ) (i : Fin t) (j : Fin (t + 1)) :
    chiV σ i.castSucc j = 0 := by
  simp [chiV, Fin.castSucc_ne_last]

theorem chiV_any_last (σ : Fin t → ℤ) (i : Fin (t + 1)) : chiV σ i (Fin.last t) = 0 := by
  simp [chiV]

/-- Pairing a weight matrix with the vector of one edge. -/
theorem pair_pairVec_mk {s : ℕ} (χ : Fin s → Fin s → ℤ) (q : W → Fin s) (a b : W) :
    pair χ (pairVec q s(a, b)) = χ (q a) (q b) + χ (q b) (q a) := by
  have h1 : ∀ u v : W, (∑ i, ∑ j, if q u = i then (if q v = j then χ i j else 0) else 0) =
      χ (q u) (q v) := by
    intro u v
    rw [Finset.sum_eq_single (q u)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  simp only [pair, pairVec, Sym2.lift_mk, mul_add, sum_add_distrib, ite_and, mul_ite, mul_one,
    mul_zero]
  rw [h1 a b, h1 b a]

theorem sigma_degContrib_mk (σ : Fin t → ℤ) (p : W → Fin t) (x a b : W) :
    ∑ i, σ i * degContrib p x s(a, b) i =
      (if a = x then σ (p b) else 0) + (if b = x then σ (p a) else 0) := by
  simp only [degContrib, Sym2.lift_mk, mul_add, sum_add_distrib, ite_and, mul_ite, mul_one,
    mul_zero]
  congr 1
  · by_cases h : a = x
    · simp [h, sum_ite_eq']
    · simp [h]
  · by_cases h : b = x
    · simp [h, sum_ite_eq']
    · simp [h]

theorem pair_relab_edge (σ : Fin t → ℤ) (p : W → Fin t) (x : W) (e : Sym2 W) (he : ¬ e.IsDiag) :
    pair (chiV σ) (pairVec (relab p x) e) = ∑ i, σ i * degContrib p x e i := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)
    rw [pair_pairVec_mk, sigma_degContrib_mk]
    by_cases ha : a = x
    · have hb : b ≠ x := fun h => hab (ha.trans h.symm)
      simp [relab, ha, hb, chiV_last_castSucc, chiV_castSucc]
    · by_cases hb : b = x
      · simp [relab, ha, hb, chiV_last_castSucc, chiV_castSucc]
      · simp [relab, ha, hb, chiV_castSucc]

/-- **The signed degree is a class-pair charge** after relabelling `x`. -/
theorem vcharge_eq_charge (σ : Fin t → ℤ) (p : W → Fin t) (x : W) (E : Finset (Sym2 W))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    charge (chiV σ) (relab p x) E = vcharge σ p x E := by
  rw [charge_eq_sum, vcharge]
  simp only [degVec, Finset.sum_apply, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun e he => pair_relab_edge σ p x e (hloop e he)

/-- On an edge set of even degree at `x` whose classes at `x` carry odd weights, the signed
degree is even. -/
theorem two_dvd_vcharge (σ : Fin t → ℤ) (p : W → Fin t) (x : W) (E : Finset (Sym2 W))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hσ : ∀ i, degVec p E x i ≠ 0 → Odd (σ i))
    (heven : Even (incidentLoad E x)) : (2 : ℤ) ∣ vcharge σ p x E := by
  have hsum := TypedDivisibilityCollapse.sum_degVec p E hloop x
  have hdiff : (2 : ℤ) ∣ vcharge σ p x E - ∑ j, degVec p E x j := by
    rw [vcharge, ← sum_sub_distrib]
    refine dvd_sum fun i _ => ?_
    by_cases h : degVec p E x i = 0
    · simp [h]
    · obtain ⟨k, hk⟩ := hσ i h
      rw [hk]
      exact ⟨k * degVec p E x i, by ring⟩
  have hev : (2 : ℤ) ∣ ∑ j, degVec p E x j := by
    rw [hsum]
    obtain ⟨m, hm⟩ := heven
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  have := dvd_add hdiff hev
  simpa using this

/-- The signed degree vanishes on integrally divisible edge sets, when `σ` kills every type
through the class of `x`. -/
theorem vcharge_eq_zero_of_isIntDiv (σ : Fin t → ℤ) {p : W → Fin t}
    {F : Finset (Multiset (Fin t))} (x : W)
    (hσF : ∀ τ ∈ F, p x ∈ τ → ∑ i, σ i * typeDegVec τ (p x) i = 0)
    {E : Finset (Sym2 W)} (hdiv : IsIntDiv p F E) : vcharge σ p x E = 0 := by
  obtain ⟨c, hc⟩ := hdiv.2 x
  rw [vcharge, hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun τ hτ => ?_
  obtain ⟨hτF, hxτ⟩ := mem_filter.mp hτ
  have h := hσF τ hτF hxτ
  calc ∑ i, σ i * (c τ * typeDegVec τ (p x) i)
      = c τ * ∑ i, σ i * typeDegVec τ (p x) i := by
        rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [h, mul_zero]

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.vcharge_eq_charge
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.two_dvd_vcharge
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.vcharge_eq_zero_of_isIntDiv
