/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Defs

@[expose] public section

/-!
# Explicit directed cycles

`cycF f` is the arc set of the closed walk `f 0 → f 1 → ⋯ → f k → f 0` for `f : Fin (k+1) → W`.
When `f` is injective it is a directed simple cycle in the sense of `IsDirCycle`, it has `k + 1`
arcs, and every vertex of the cycle has in- and out-degree one.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset Fin.NatCast

variable {W : Type*} [DecidableEq W]

/-- The arcs `f i → f (i + 1)` (indices modulo the length). -/
def cycF {n : ℕ} (f : Fin n → W) : Finset (W × W) :=
  Finset.univ.image (fun i => (f i, f (finRotate n i)))

section

variable {k : ℕ} {f : Fin (k + 1) → W}

omit [DecidableEq W] in
lemma cycF_arc_injective (hf : Function.Injective f) :
    Function.Injective (fun i : Fin (k + 1) => (f i, f (finRotate (k + 1) i))) :=
  fun _ _ h => hf (Prod.ext_iff.1 h).1

lemma mem_cycF {a : W × W} : a ∈ cycF f ↔ ∃ i, (f i, f (i + 1)) = a := by
  simp [cycF, finRotate_succ_apply]

lemma card_cycF (hf : Function.Injective f) : (cycF f).card = k + 1 := by
  unfold cycF
  rw [Finset.card_image_of_injective _ (cycF_arc_injective hf), Finset.card_univ,
    Fintype.card_fin]

lemma inDeg_cycF (hf : Function.Injective f) (x : W) :
    inDeg (cycF f) x = if x ∈ Set.range f then 1 else 0 := by
  unfold inDeg cycF
  rw [Finset.filter_image, Finset.card_image_of_injective _ (cycF_arc_injective hf)]
  split_ifs with hx
  · obtain ⟨j, rfl⟩ := hx
    rw [Finset.card_eq_one]
    refine ⟨(finRotate (k + 1)).symm j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [← hf h]
      simp
    · rintro rfl
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ h
    exact hx ⟨_, h⟩

lemma outDeg_cycF (hf : Function.Injective f) (x : W) :
    outDeg (cycF f) x = if x ∈ Set.range f then 1 else 0 := by
  unfold outDeg cycF
  rw [Finset.filter_image, Finset.card_image_of_injective _ (cycF_arc_injective hf)]
  split_ifs with hx
  · obtain ⟨j, rfl⟩ := hx
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hf h, fun h => h ▸ rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ h
    exact hx ⟨_, h⟩

lemma deg_cycF (hf : Function.Injective f) (x : W) :
    deg (cycF f) x = if x ∈ Set.range f then 2 else 0 := by
  unfold deg
  rw [inDeg_cycF hf, outDeg_cycF hf]
  split_ifs <;> rfl

lemma balanced_cycF (hf : Function.Injective f) : Balanced (cycF f) := by
  intro x
  rw [inDeg_cycF hf, outDeg_cycF hf]

/-- **An injective closed walk is a directed simple cycle.** -/
theorem isDirCycle_cycF (hf : Function.Injective f) : IsDirCycle (cycF f) := by
  refine ⟨⟨(f 0, f (0 + 1)), mem_cycF.2 ⟨0, rfl⟩⟩, balanced_cycF hf, ?_⟩
  intro F hFs hFne hFb
  set S : Finset (Fin (k + 1)) := Finset.univ.filter (fun i => (f i, f (i + 1)) ∈ F) with hS
  have hstep : ∀ i ∈ S, i + 1 ∈ S := by
    intro i hi
    have hiF : (f i, f (i + 1)) ∈ F := (Finset.mem_filter.1 hi).2
    have hin : 0 < inDeg F (f (i + 1)) :=
      Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hiF, rfl⟩⟩
    rw [hFb] at hin
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hin
    obtain ⟨haF, ha1⟩ := Finset.mem_filter.1 ha
    obtain ⟨j, hj⟩ := mem_cycF.1 (hFs haF)
    have hji : j = i + 1 := hf (by rw [← ha1, ← hj])
    subst hji
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj ▸ haF⟩
  obtain ⟨a0, ha0⟩ := hFne
  obtain ⟨i0, hi0⟩ := mem_cycF.1 (hFs ha0)
  have hi0S : i0 ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0 ▸ ha0⟩
  have hall : ∀ m : ℕ, i0 + (m : Fin (k + 1)) ∈ S := by
    intro m
    induction m with
    | zero => simpa using hi0S
    | succ m ih =>
      have := hstep _ ih
      rwa [Nat.cast_succ, ← add_assoc]
  refine Finset.Subset.antisymm hFs ?_
  intro a ha
  obtain ⟨j, rfl⟩ := mem_cycF.1 ha
  have hj : j = i0 + (((j - i0 : Fin (k + 1)) : ℕ) : Fin (k + 1)) := by
    rw [Fin.cast_val_eq_self]; abel
  have := hall ((j - i0 : Fin (k + 1)) : ℕ)
  rw [← hj] at this
  exact (Finset.mem_filter.1 this).2

end

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
