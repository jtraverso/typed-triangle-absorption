/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedAnchors

@[expose] public section

/-! Place the vertices of one fixed catalogue, fixing prescribed physical
roots and charging the actual catalogue degree at every assigned anchor. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAnchors

open Finset Cycles

variable {A V : Type} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V] [Nonempty V]

def free (pin : A → Option V) : Finset A := univ.filter (fun a => pin a = none)

def pinnedLoad (pin : A → Option V) (weight : A → ℝ) (r : V) : ℝ :=
  ∑ a, if pin a = some r then weight a else 0

def placed (pin : A → Option V) (g : A → V) (a : A) : V := (pin a).getD (g a)

omit [DecidableEq A] [Fintype V] [Nonempty V] in
theorem placement_load (pin : A → Option V) (weight : A → ℝ) (g : A → V) (r : V) :
    (∑ a, if placed pin g a = r then weight a else 0) =
      WeightedAnchors.load (pinnedLoad pin weight) weight g (free pin) r := by
  unfold WeightedAnchors.load pinnedLoad free
  rw [sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  cases h : pin a with
  | none => simp [placed, h]
  | some v => simp [placed, h]

omit [DecidableEq A] [Nonempty V] in
theorem total_pinned_free (pin : A → Option V) (weight : A → ℝ) :
    (∑ r, pinnedLoad pin weight r) + ∑ a ∈ free pin, weight a = ∑ a, weight a := by
  unfold pinnedLoad free
  rw [sum_comm, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  cases h : pin a with
  | none => simp
  | some v => simp

/-- The anchor map is constructed from class supplies. Pinned vertices keep
their prescribed images, and every catalogue degree is charged on placement. -/
theorem exists_anchors (lib : Finset (Finset (A × A)))
    (pin : A → Option V) (label : A → Fin 3) (p : V → Fin 3)
    (a T W M : ℝ) (hT : 0 < T) (hW : 0 ≤ W)
    (hpin : ∀ v r, pin v = some r → p r = label v)
    (hicap : ∀ r, pinnedLoad pin (fun v => (catalogLoad lib v : ℝ)) r ≤ T)
    (hwcap : ∀ v, (catalogLoad lib v : ℝ) ≤ W)
    (hsupply : ∀ i, a ≤ (univ.filter (fun r : V => p r = i)).card)
    (hbudget : M < a * T) (hmass : (∑ v, (catalogLoad lib v : ℝ)) ≤ M) :
    ∃ f : A → V,
      (∀ v r, pin v = some r → f v = r) ∧
      (∀ v, p (f v) = label v) ∧
      (∀ r, (∑ v, if f v = r then (catalogLoad lib v : ℝ) else 0) ≤ T + W) ∧
      (∑ r, ∑ v, if f v = r then (catalogLoad lib v : ℝ) else 0) ≤ M := by
  let weight := fun v => (catalogLoad lib v : ℝ)
  have hi : ∀ r, 0 ≤ pinnedLoad pin weight r := by
    intro r
    apply sum_nonneg
    intro v _
    split_ifs <;> positivity
  obtain ⟨g, hg, hcap, htotal⟩ := WeightedAnchors.exists_placement
    (free pin) (fun v => univ.filter (fun r : V => p r = label v))
    weight (pinnedLoad pin weight) a T W M hT hW hi hicap
    (fun v => Nat.cast_nonneg _) hwcap (fun v => hsupply (label v)) hbudget
    ((total_pinned_free pin weight).le.trans hmass)
  refine ⟨placed pin g, ?_, ?_, ?_, ?_⟩
  · intro v r hv
    simp [placed, hv]
  · intro v
    cases hv : pin v with
    | none =>
      have hvfree : v ∈ free pin := by simp [free, hv]
      have hcol := (mem_filter.mp (hg v hvfree)).2
      simpa [placed, hv] using hcol
    | some r => simpa [placed, hv] using hpin v r hv
  · intro r
    rw [placement_load]
    exact hcap r
  · simp_rw [placement_load]
    exact htotal

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAnchors

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAnchors.exists_anchors
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAnchors.total_pinned_free
