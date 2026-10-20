/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.CoreSupply

@[expose] public section

/-! The conserved core inherits native three-colour supply also when the
host assumptions are stated only for the component family. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open StructuralF3General

theorem core_component_link (d : Case) (a b c : Fin d.t)
    (ha : d.comp a = d.core) (hb : d.comp b = d.core) (hc : d.comp c = d.core)
    (h : Link d.S.F' a b c) : Link (componentFamily d d.core) a b c := by
  refine mem_filter.mpr ⟨h, ?_⟩
  intro r hr
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem component_core_supply {V : Type} [Fintype V] [DecidableEq V]
    (d : Case) (hd : Checked d) (p : V → Fin d.t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (a : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link (componentFamily d d.core) i j k) D a) :
    GuardedSupply
      (fun v : {v : V // d.comp (p v) = d.core} => d.colour (p v.val))
      (G.induce {v | d.comp (p v) = d.core})
      (fun i j => ∃ k, Link tripFamily i j k) D a := by
  classical
  intro S hS j hguard
  by_cases ha : a ≤ 0
  · exact ha.trans (Nat.cast_nonneg _)
  have ha0 : 0 < a := lt_of_not_ge ha
  obtain ⟨r, hr, hcolour⟩ := hd.colours_present j
  have hcompat : ∀ v ∈ S.image Subtype.val,
      ∃ k, Link (componentFamily d d.core) (p v) r k := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    obtain ⟨k, hk⟩ := hguard x hx
    obtain ⟨s, hsc, hsk⟩ := hd.colours_present k
    refine ⟨s, core_component_link d _ _ _ x.property hr hsc
      ((hd.core_exact (p x.val) r s x.property hr hsc).mpr ?_)⟩
    simpa [Link, tripFamily, hcolour, hsk] using hk
  have hcount := hs (S.image Subtype.val) (card_image_le.trans hS) r hcompat
  let N := guardedNeighbours p G (S.image Subtype.val) r
  have hpos : 0 < N.card := by
    have h : (0 : ℝ) < N.card := ha0.trans_le hcount
    exact_mod_cast h
  obtain ⟨w0, hw0⟩ := card_pos.mp hpos
  have hw0label : p w0 = r := (mem_filter.mp hw0).2.1
  have hw0core : d.comp (p w0) = d.core := by rw [hw0label]; exact hr
  let f : V → {v : V // d.comp (p v) = d.core} := fun w =>
    if h : d.comp (p w) = d.core then ⟨w,h⟩ else ⟨w0,hw0core⟩
  have hfval : ∀ w ∈ N, (f w).val = w := by
    intro w hw
    have hwlabel : p w = r := (mem_filter.mp hw).2.1
    have hwcore : d.comp (p w) = d.core := by rw [hwlabel]; exact hr
    simp [f, hwcore]
  have hmaps : ∀ w ∈ N,
      f w ∈ guardedNeighbours
        (fun v : {v : V // d.comp (p v) = d.core} => d.colour (p v.val))
        (G.induce {v | d.comp (p v) = d.core}) S j := by
    intro w hw
    obtain ⟨hwlabel, hadj⟩ := (mem_filter.mp hw).2
    refine mem_filter.mpr ⟨mem_univ _, ?_, fun x hx => ?_⟩
    · change d.colour (p (f w).val) = j
      rw [hfval w hw, hwlabel]
      exact hcolour
    · change G.Adj x.val (f w).val
      rw [hfval w hw]
      exact hadj _ (mem_image_of_mem _ hx)
  have hinj : Set.InjOn f (N : Set V) := by
    intro w hw w' hw' h
    have hv := congrArg Subtype.val h
    simpa only [hfval w hw, hfval w' hw'] using hv
  have hcard := card_le_card_of_injOn f hmaps hinj
  have hcardR : (N.card : ℝ) ≤
      (guardedNeighbours
        (fun v : {v : V // d.comp (p v) = d.core} => d.colour (p v.val))
        (G.induce {v | d.comp (p v) = d.core}) S j).card := by exact_mod_cast hcard
  exact hcount.trans hcardR

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.component_core_supply
