/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse

@[expose] public section

/-!
# Collapse of the vertex conditions under `FiveStepLinks`

`TypedDivisibilityCollapse.isIntDiv_iff` uses `ThreeStepLinks` only to put `basis a + basis b` in
the vertex lattice of a class `r` for active `a, b` (an alternating sum along a link walk of length
three). A walk of length five works the same way. All 27 `KappaLinks` classes of the census without
`ThreeStepLinks` satisfy `FiveStepLinks` (Python, `kappa_gate.py`).
-/

namespace PartitionedTriangleAbsorption.TypedDivisibilityCollapse

open Finset TypedTransformer AntiEdgeSelection

variable {t : ℕ}

/-- Link walks of length five between active classes. -/
def FiveStepLinks (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ r a b, (∃ c, Link F r a c) → (∃ c, Link F r b c) →
    ∃ v1 v2 v3 v4, Link F r a v1 ∧ Link F r v1 v2 ∧ Link F r v2 v3 ∧ Link F r v3 v4 ∧
      Link F r v4 b

theorem active_pair_mem_five {F : Finset (Multiset (Fin t))} (hF : FiveStepLinks F)
    {r a b : Fin t} (ha : ∃ c, Link F r a c) (hb : ∃ c, Link F r b c) :
    basis a + basis b ∈ (latticeHom F r).range := by
  obtain ⟨v1, v2, v3, v4, h1, h2, h3, h4, h5⟩ := hF r a b ha hb
  have e : basis a + basis b = (basis a + basis v1) - (basis v1 + basis v2) +
      (basis v2 + basis v3) - (basis v3 + basis v4) + (basis v4 + basis b) := by abel
  rw [e]
  exact add_mem (sub_mem (add_mem (sub_mem (link_mem h1) (link_mem h2)) (link_mem h3))
    (link_mem h4)) (link_mem h5)

/-- An even-sum vector supported on active link vertices lies in the vertex lattice. -/
theorem mem_of_active_even_five {F : Finset (Multiset (Fin t))} (hF : FiveStepLinks F) {r : Fin t}
    (d : Fin t → ℤ) (hsupp : ∀ j, d j ≠ 0 → ∃ c, Link F r j c) (heven : Even (∑ j, d j)) :
    d ∈ (latticeHom F r).range := by
  by_cases h0 : ∃ a, ∃ c, Link F r a c
  · obtain ⟨a, ha⟩ := h0
    obtain ⟨m, hm⟩ := heven
    have hsum : (∑ j, d j • (basis j + basis a)) ∈ (latticeHom F r).range := by
      refine sum_mem fun j _ => ?_
      by_cases hj : d j = 0
      · rw [hj, zero_smul]; exact zero_mem _
      · exact zsmul_mem (active_pair_mem_five hF (hsupp j hj) ha) _
    have hsq : m • (basis a + basis a) ∈ (latticeHom F r).range :=
      zsmul_mem (active_pair_mem_five hF ha ha) _
    have e : d = (∑ j, d j • (basis j + basis a)) - m • (basis a + basis a) := by
      funext k
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        mul_add, sum_add_distrib, ← sum_mul, hm]
      simp only [basis, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
      split_ifs <;> ring
    rw [e]
    exact sub_mem hsum hsq
  · push Not at h0
    have : d = 0 := by
      funext j
      by_contra hj
      obtain ⟨c, hc⟩ := hsupp j hj
      exact h0 j c hc
    rw [this]
    exact zero_mem _

variable {V : Type*} [DecidableEq V]
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- **Reverse direction.** Activity, parity and the global lattice condition give integral
divisibility, for every family with `ThreeStepLinks`. -/
theorem isIntDiv_of_active_even_five (hF : FiveStepLinks F) {E : Finset (Sym2 V)}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F p E)
    (heven : ∀ v, Even (incidentLoad E v))
    (hedge : ∃ c : Multiset (Fin t) → ℤ, edgeVec p E = ∑ τ ∈ F, c τ • typeEdgeVec τ) :
    IsIntDiv p F E := by
  refine ⟨hedge, fun v => ?_⟩
  rw [← mem_range_latticeHom]
  apply mem_of_active_even_five hF
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := exists_of_degVec_ne_zero hj
    exact hact v b hb
  · rw [sum_degVec p E hloop v]
    obtain ⟨m, hm⟩ := heven v
    exact ⟨m, by rw [hm]; push_cast; ring⟩

/-- **Collapse under `FiveStepLinks`.** -/
theorem isIntDiv_iff_five (hF : FiveStepLinks F) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F E ↔ ActiveEdges F p E ∧ (∀ v, Even (incidentLoad E v)) ∧
      ∃ c : Multiset (Fin t) → ℤ, edgeVec p E = ∑ τ ∈ F, c τ • typeEdgeVec τ :=
  ⟨fun h => ⟨active_of_isIntDiv hcard h, even_of_isIntDiv hcard hloop h, h.1⟩,
    fun ⟨ha, he, hc⟩ => isIntDiv_of_active_even_five hF hloop ha he hc⟩

end PartitionedTriangleAbsorption.TypedDivisibilityCollapse

#print axioms PartitionedTriangleAbsorption.TypedDivisibilityCollapse.isIntDiv_iff_five
