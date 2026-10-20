/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.GuardedPath4

@[expose] public section

/-! A weighted greedy step for the physical catalogue embedding. Endpoints
are charged separately in advance. Only the three new interiors are charged
here, by twice the catalogue weight of the routed arc. This is a step lemma,
not the global embedding theorem. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathStep

open Finset AntiEdgeSelection StructuralF3General

variable {V : Type} [Fintype V] [DecidableEq V]

def charge (load : V → ℝ) (w : ℝ) (x y z : V) (v : V) : ℝ :=
  load v + if v ∈ ({x, y, z} : Finset V) then 2 * w else 0

theorem exists_weighted_path (p : V → Fin 3) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d T S w W : ℝ) (hd : 0 ≤ d) (hT : 0 < T) (hw : 0 ≤ w) (hwW : w ≤ W)
    (hs : GuardedSupply p G (fun i j => i ≠ j) 2 a)
    (B : Finset (Sym2 V)) (hB : DegBounded B d)
    (load : V → ℝ) (hnonneg : ∀ v, 0 ≤ load v)
    (hmass : ∑ v, load v ≤ S) (hcap : ∀ v, load v ≤ T + 2 * W)
    (hbudget : S / T + 4 + 2 * d < a)
    (u v : V) (i j k : Fin 3) (hu : p u = i) (hv : p v = j)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ x y z : V,
      p x = j ∧ p y = k ∧ p z = i ∧
      x ≠ u ∧ x ≠ v ∧ z ≠ u ∧ z ≠ v ∧ x ≠ z ∧
      y ≠ u ∧ y ≠ v ∧ y ≠ x ∧ y ≠ z ∧
      G.Adj u x ∧ G.Adj x y ∧ G.Adj y z ∧ G.Adj z v ∧
      s(u,x) ∉ B ∧ s(x,y) ∉ B ∧ s(y,z) ∉ B ∧ s(z,v) ∉ B ∧
      (∀ r, 0 ≤ charge load w x y z r) ∧
      (∀ r, charge load w x y z r ≤ T + 2 * W) ∧
      (∑ r, charge load w x y z r) ≤ S + 6 * w := by
  classical
  let Z : Finset V := univ.filter fun r => T ≤ load r
  have hZmass : (Z.card : ℝ) * T ≤ S := by
    calc
      (Z.card : ℝ) * T = ∑ r ∈ Z, T := by simp
      _ ≤ ∑ r ∈ Z, load r := sum_le_sum fun r hr => (mem_filter.mp hr).2
      _ ≤ ∑ r, load r := sum_le_sum_of_subset_of_nonneg (subset_univ Z)
        (fun r _ _ => hnonneg r)
      _ ≤ S := hmass
  have hZcard : (Z.card : ℝ) ≤ S / T := (le_div_iff₀ hT).mpr hZmass
  obtain ⟨x, y, z, hx, hy, hz, hxZ, hzZ, hyZ, hux, hxy, hyz, hzv,
      huxB, hxyB, hyzB, hzvB⟩ :=
    GuardedPath4.exists_path p G a d hd hs B hB Z (by linarith)
      u v i j k hu hv hij hik hjk
  have hxl : load x < T := lt_of_not_ge fun h => hxZ
    (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, h⟩)))
  have hzl : load z < T := lt_of_not_ge fun h => hzZ
    (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
      (mem_filter.mpr ⟨mem_univ _, h⟩))))
  have hyl : load y < T := lt_of_not_ge fun h => hyZ
    (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
      (mem_filter.mpr ⟨mem_univ _, h⟩)))))
  have hdistinct : x ≠ u ∧ x ≠ v ∧ z ≠ u ∧ z ≠ v ∧ x ≠ z ∧
      y ≠ u ∧ y ≠ v ∧ y ≠ x ∧ y ≠ z := by
    simp only [mem_insert, not_or] at hxZ hzZ hyZ
    exact ⟨hxZ.1, hxZ.2.1, hzZ.2.1, hzZ.2.2.1, Ne.symm hzZ.1,
      hyZ.2.2.1, hyZ.2.2.2.1, hyZ.2.1, hyZ.1⟩
  refine ⟨x, y, z, hx, hy, hz, hdistinct.1, hdistinct.2.1, hdistinct.2.2.1,
    hdistinct.2.2.2.1, hdistinct.2.2.2.2.1, hdistinct.2.2.2.2.2.1,
    hdistinct.2.2.2.2.2.2.1, hdistinct.2.2.2.2.2.2.2.1,
    hdistinct.2.2.2.2.2.2.2.2, hux, hxy, hyz, hzv, huxB, hxyB, hyzB, hzvB, ?_, ?_, ?_⟩
  · intro r
    unfold charge
    split_ifs <;> linarith [hnonneg r]
  · intro r
    unfold charge
    split_ifs with hr
    · simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> linarith
    · simpa using hcap r
  · have hsmall : ({x,y,z} : Finset V).card ≤ 3 := by
      have h1 := card_insert_le x ({y,z} : Finset V)
      have h2 := card_insert_le y ({z} : Finset V)
      simp only [card_singleton] at h2
      omega
    have hsum : ∑ r, (if r ∈ ({x,y,z} : Finset V) then 2 * w else 0) =
        (({x,y,z} : Finset V).card : ℝ) * (2 * w) := by
      have hfilter : univ.filter (fun r => r ∈ ({x,y,z} : Finset V)) = {x,y,z} := by
        ext r
        simp only [mem_filter, mem_univ, true_and]
      rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul]
    simp only [charge, sum_add_distrib]
    rw [hsum]
    have hsmall' : (({x,y,z} : Finset V).card : ℝ) ≤ 3 := by exact_mod_cast hsmall
    nlinarith

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathStep
