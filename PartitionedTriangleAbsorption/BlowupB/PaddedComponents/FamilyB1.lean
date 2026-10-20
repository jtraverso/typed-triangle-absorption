/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ComponentLattice

@[expose] public section

/-!
# A disconnected `ℤ/3` family: `FB1 = {000, 001, 222, 223}`

Allowed pairs `00, 01, 22, 23`; two components `{0, 1}` and `{2, 3}` (labels `cB1 = (0,0,2,2)`).
Inside each component the lattice is ordinary divisibility (`Even3`); globally it is the
"`Even3` per component" lattice, whose quotient by ordinary divisibility is `ℤ/3`. It is the
second `ℤ/3` row of the census and has no isolated monochromatic class.

* finite facts (`decide`);
* `even3Inside_FB1`: the lattice is trivial inside every component;
* `witnessBound_FB1`: every integral witness is the unique one, with coefficients `≥ -(2e+4)`;
* `universalCert_FB1`: `UniversalCert FB1`, from `universalCert_of_even3_components`.
-/

namespace PaddedComponents

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon

/-- The family `{000, 001, 222, 223}`. -/
noncomputable def FB1 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {2, 2, 2}, {2, 2, 3}}

/-- Component labels of `FB1`. -/
def cB1 : Fin 4 → Fin 4 := ![0, 0, 2, 2]

theorem FB1_card : ∀ τ ∈ FB1, Multiset.card τ = 3 := by unfold FB1; decide

theorem FB1_three : ThreeStepLinks FB1 := by unfold ThreeStepLinks Link FB1; decide

theorem familyFacts_FB1 : FamilyFacts FB1 :=
  ⟨FB1_card, by unfold Link FB1; decide, by intro i; fin_cases i <;> (unfold Link FB1; decide)⟩

theorem compLabel_FB1 : CompLabel FB1 cB1 := by unfold CompLabel Link FB1 cB1; decide

theorem typesInside_FB1 : TypesInside FB1 cB1 := by unfold TypesInside FB1 cB1; decide

theorem localWalk4_FB1 (k : Fin 4) : LocalWalk4 FB1 cB1 k := by
  revert k; unfold LocalWalk4 Link FB1 cB1; decide

/-- `FB1` has two components, so `Walk4` fails on the whole allowed-pair graph. -/
theorem not_walk4_FB1 : ¬ LocalWalk4 FB1 (fun _ => 0) 0 := by
  unfold LocalWalk4 Link FB1; decide

set_option maxHeartbeats 4000000 in
theorem scalar_inside_FB1 (k : Fin 4) : ∀ u, ScalarHyp FB1 u → CountsInside cB1 k u →
    ∃ w, LatEq FB1 u w := by
  intro u hu hin
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have z02 : u 0 2 = 0 := hf 0 2 (by unfold Link FB1; decide)
  have z03 : u 0 3 = 0 := hf 0 3 (by unfold Link FB1; decide)
  have z11 : u 1 1 = 0 := hf 1 1 (by unfold Link FB1; decide)
  have z12 : u 1 2 = 0 := hf 1 2 (by unfold Link FB1; decide)
  have z13 : u 1 3 = 0 := hf 1 3 (by unfold Link FB1; decide)
  have z33 : u 3 3 = 0 := hf 3 3 (by unfold Link FB1; decide)
  have hsplit : (u 2 2 = 0 ∧ u 2 3 = 0) ∨ (u 0 0 = 0 ∧ u 0 1 = 0) := by
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨hin 2 2 (by left; decide), hin 2 3 (by left; decide)⟩
    · exact Or.inr ⟨hin 0 0 (by left; simpa [cB1] using Ne.symm hk),
        hin 0 1 (by left; simpa [cB1] using Ne.symm hk)⟩
  have p1 := hp 1
  have p3 := hp 3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at p1 p3
  unfold totalU at h3
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl] at h3
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0
  have s21 := hs 2 1; have s31 := hs 3 1; have s32 := hs 3 2
  have n00 := hn 0 0; have n01 := hn 0 1; have n22 := hn 2 2; have n23 := hn 2 3
  refine ⟨coeffList [({0,0,0}, (u 0 0 - u 0 1 / 2) / 3), ({0,0,1}, u 0 1 / 2),
    ({2,2,2}, (u 2 2 - u 2 3 / 2) / 3), ({2,2,3}, u 2 3 / 2)], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [FB1, coeffList, typeEdgeVec, sum_insert] <;> omega

theorem even3Inside_FB1 (k : Fin 4) : Even3Inside FB1 cB1 k :=
  even3Inside_of_scalar FB1 cB1 k FB1_three FB1_card (scalar_inside_FB1 k)

set_option maxHeartbeats 4000000 in
theorem scalar_witness_FB1 : ∀ u c0, ScalarHyp FB1 u → LatEq FB1 u c0 →
    ∃ c, LatEq FB1 u c ∧ ∀ τ ∈ FB1, -(2 * totalU u + 4) ≤ c τ := by
  intro u c0 hu hc0
  refine ⟨c0, hc0, ?_⟩
  obtain ⟨hs, hn, hf, hp, h3⟩ := hu
  have e00 := hc0 0 0
  have e01 := hc0 0 1
  have e22 := hc0 2 2
  have e23 := hc0 2 3
  simp (config := {decide := true}) [FB1, typeEdgeVec, sum_insert] at e00 e01 e22 e23
  unfold totalU
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceLE, ite_true, ite_false, le_refl]
  have n00 := hn 0 0; have n01 := hn 0 1; have n02 := hn 0 2; have n03 := hn 0 3
  have n11 := hn 1 1; have n12 := hn 1 2; have n13 := hn 1 3; have n22 := hn 2 2
  have n23 := hn 2 3; have n33 := hn 3 3
  intro τ hτ
  simp only [FB1, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;> simp only [Multiset.insert_eq_cons] <;> omega

theorem witnessBound_FB1 (K : ℕ) : WitnessBoundK FB1 K (FB1.card * (2 * K + 4)) :=
  witnessBound_of_latEq_lower FB1 FB1_card scalar_witness_FB1 K

theorem FB1_card_eq : FB1.card = 4 := by unfold FB1; decide

/-- **`UniversalCert FB1`.** -/
theorem universalCert_FB1 : UniversalCert FB1 := by
  have hB : WitnessBoundK FB1 168 1360 := by
    rw [show (1360 : ℕ) = FB1.card * (2 * 168 + 4) by rw [FB1_card_eq]]
    exact witnessBound_FB1 168
  exact universalCert_of_even3_components FB1 cB1 compLabel_FB1 typesInside_FB1 FB1_card
    FB1_three localWalk4_FB1 even3Inside_FB1 1360 hB
    (by norm_num [terminalOrder]) (by norm_num [terminalSize])

end PaddedComponents

#print axioms PaddedComponents.universalCert_FB1
