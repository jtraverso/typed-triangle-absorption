/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedTransformerLabels

@[expose] public section

/-!
# `KappaLinks`: a weakening of `ThreeStepLinks` that still feeds the eleven-edge transformer

`exists_auxiliary_types` uses `ThreeStepLinks` only to join the auxiliary labels `u i` (the third
class chosen for the trail edge entering position `i`) and `u (σ i)` (the one chosen for the edge
leaving it) by a walk of length three in the link of `r i`. It is enough to choose, once and for
all, a third class `κ a b` for every oriented allowed pair `a → b` such that consecutive choices are
joined by such walks. That is `KappaLinks`.

`ThreeStepLinks F → KappaLinks F` (`kappaLinks_of_threeStep`). The local census found 27 S₄-classes
of four-class families WITHOUT `ThreeStepLinks` that satisfy `KappaLinks` (exactly those whose links
are odd-connected; `cegis/b0_refiner/Fstar_20261012/kappa_gate.py`, Python).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Kappa

open Finset PartitionedTriangleAbsorption.TypedTransformer

variable {t : ℕ}

/-- A choice of third classes for oriented allowed pairs, consecutive choices joined by link walks
of length three. -/
def KappaLinks (F : Finset (Multiset (Fin t))) : Prop :=
  ∃ κ : Fin t → Fin t → Fin t,
    (∀ a b, (∃ c, Link F a b c) → Link F a b (κ a b)) ∧
    ∀ x r y, (∃ c, Link F x r c) → (∃ c, Link F r y c) →
      ∃ v w, Link F r (κ x r) v ∧ Link F r v w ∧ Link F r w (κ r y)

theorem kappaLinks_of_threeStep {F : Finset (Multiset (Fin t))} (hF : ThreeStepLinks F) :
    KappaLinks F := by
  classical
  refine ⟨fun a b => if h : ∃ c, Link F a b c then h.choose else a, ?_, ?_⟩
  · intro a b h
    simp only [dif_pos h]
    exact h.choose_spec
  · intro x r y hx hy
    have hκx : Link F x r (if h : ∃ c, Link F x r c then h.choose else x) := by
      simp only [dif_pos hx]; exact hx.choose_spec
    have hκy : Link F r y (if h : ∃ c, Link F r y c then h.choose else r) := by
      simp only [dif_pos hy]; exact hy.choose_spec
    apply hF
    · exact ⟨x, (link_swap F _ _ _).mp ((link_root_swap F _ _ _).mpr hκx)⟩
    · exact ⟨y, (link_swap F _ _ _).mp hκy⟩

/-- `exists_auxiliary_types` under `KappaLinks`. -/
theorem exists_auxiliary_types_kappa {I : Type*} (F : Finset (Multiset (Fin t)))
    (hF : KappaLinks F) (σ : Equiv.Perm I) (r : I → Fin t)
    (he : ∀ i, ∃ c, Link F (r i) (r (σ i)) c) :
    ∃ a : I × Fin 3 → Fin t, AuxiliaryTypes F σ r a := by
  classical
  obtain ⟨κ, hκ, hwalk⟩ := hF
  let u : I → Fin t := fun i => κ (r (σ.symm i)) (r i)
  have hu : ∀ i, Link F (r i) (r (σ i)) (u (σ i)) := by
    intro i
    have := hκ (r i) (r (σ i)) (he i)
    simpa [u] using this
  have hin : ∀ i, ∃ c, Link F (r (σ.symm i)) (r i) c := by
    intro i
    simpa using he (σ.symm i)
  have hb : ∀ i, ∃ v w, Link F (r i) (u i) v ∧ Link F (r i) v w ∧ Link F (r i) w (u (σ i)) := by
    intro i
    obtain ⟨v, w, h1, h2, h3⟩ := hwalk (r (σ.symm i)) (r i) (r (σ i)) (hin i) (he i)
    exact ⟨v, w, by simpa [u] using h1, h2, by simpa [u] using h3⟩
  choose v w hw using hb
  refine ⟨fun z => ![u z.1, v z.1, w z.1] z.2, ?_⟩
  intro i
  exact ⟨hu i, (hw i).2.1, (hw i).1, (hw i).2.2⟩

end PartitionedTriangleAbsorption.BlowupB.Kappa

#print axioms PartitionedTriangleAbsorption.BlowupB.Kappa.kappaLinks_of_threeStep
#print axioms PartitionedTriangleAbsorption.BlowupB.Kappa.exists_auxiliary_types_kappa
