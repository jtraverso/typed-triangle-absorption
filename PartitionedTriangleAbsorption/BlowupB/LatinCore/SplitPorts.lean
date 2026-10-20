/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.PhysicalTransport

@[expose] public section

/-! Split the incidences of the actual input arc set. Each input arc has two
private ports, so its lifted input graph is a matching. Pinning the ports back
to their original vertices is injective on arcs, not on vertices. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts

open Finset Cycles

variable {V : Type} [DecidableEq V] (X : Finset (V × V))

abbrev Port := {e : V × V // e ∈ X} × Fin 2

def root (p : Port X) : V := if p.2 = 0 then p.1.val.1 else p.1.val.2

def input : {e : V × V // e ∈ X} ↪ Port X × Port X where
  toFun e := ((e,0),(e,1))
  inj' := by
    intro e f h
    exact congrArg (fun a => a.1.1) h

def arcsOf (L : Finset (V × V)) : Finset (Port X × Port X) :=
  (univ.filter (fun e : {e : V × V // e ∈ X} => e.val ∈ L)).map (input X)

def arcs : Finset (Port X × Port X) := arcsOf X X

theorem mem_arcsOf {L : Finset (V × V)} {a : Port X × Port X} :
    a ∈ arcsOf X L ↔ ∃ e : {e : V × V // e ∈ X}, e.val ∈ L ∧ input X e = a := by
  simp [arcsOf]

theorem arcsOf_subset (L : Finset (V × V)) : arcsOf X L ⊆ arcs X := by
  intro a ha
  obtain ⟨e, -, rfl⟩ := (mem_arcsOf X).mp ha
  exact (mem_arcsOf X).mpr ⟨e,e.property,rfl⟩

theorem port_card : Fintype.card (Port X) = 2 * X.card := by
  simp [Port, mul_comm]

theorem root_input (e : {e : V × V // e ∈ X}) :
    arcImage (root X) (input X e) = e.val := by
  change (root X (e,0), root X (e,1)) = e.val
  simp [root]

theorem root_injective (L : Finset (V × V)) :
    Set.InjOn (arcImage (root X)) (arcsOf X L : Set (Port X × Port X)) := by
  intro a ha b hb hab
  obtain ⟨e, -, rfl⟩ := (mem_arcsOf X).mp ha
  obtain ⟨f, -, rfl⟩ := (mem_arcsOf X).mp hb
  rw [root_input, root_input] at hab
  exact congrArg (input X) (Subtype.ext hab)

theorem root_image (L : Finset (V × V)) (hL : L ⊆ X) :
    (arcsOf X L).image (arcImage (root X)) = L := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    obtain ⟨e, he, rfl⟩ := (mem_arcsOf X).mp hb
    simpa only [root_input] using he
  · intro ha
    refine mem_image.mpr ⟨input X ⟨a,hL ha⟩, ?_, ?_⟩
    · exact (mem_arcsOf X).mpr ⟨⟨a,hL ha⟩,ha,rfl⟩
    · exact root_input X _

theorem arcsOf_card (L : Finset (V × V)) (hL : L ⊆ X) :
    (arcsOf X L).card = L.card := by
  calc
    _ = ((arcsOf X L).image (arcImage (root X))).card :=
      (card_image_of_injOn (root_injective X L)).symm
    _ = L.card := congrArg Finset.card (root_image X L hL)

theorem in_count (L : Finset (V × V)) (p : Port X) :
    inDeg (arcsOf X L) p = if p.2 = 1 ∧ p.1.val ∈ L then 1 else 0 := by
  have hset : (arcsOf X L).filter (fun a => a.2 = p) =
      if p.2 = 1 ∧ p.1.val ∈ L then {input X p.1} else ∅ := by
    ext a
    simp only [mem_filter, mem_arcsOf]
    by_cases hp : p.2 = 1 ∧ p.1.val ∈ L
    · rw [if_pos hp, mem_singleton]
      constructor
      · rintro ⟨⟨e, he, rfl⟩, h⟩
        have heq : e = p.1 := congrArg Prod.fst h
        exact congrArg (input X) heq
      · intro h
        subst a
        refine ⟨⟨p.1,hp.2,rfl⟩, ?_⟩
        change (p.1, (1 : Fin 2)) = p
        exact Prod.ext rfl hp.1.symm
    · simp only [if_neg hp, Finset.notMem_empty, iff_false]
      rintro ⟨⟨e, he, rfl⟩, h⟩
      apply hp
      have heq : e = p.1 := congrArg Prod.fst h
      exact ⟨(congrArg Prod.snd h).symm, by simpa [← heq] using he⟩
  unfold inDeg
  rw [hset]
  split_ifs <;> simp

theorem out_count (L : Finset (V × V)) (p : Port X) :
    outDeg (arcsOf X L) p = if p.2 = 0 ∧ p.1.val ∈ L then 1 else 0 := by
  have hset : (arcsOf X L).filter (fun a => a.1 = p) =
      if p.2 = 0 ∧ p.1.val ∈ L then {input X p.1} else ∅ := by
    ext a
    simp only [mem_filter, mem_arcsOf]
    by_cases hp : p.2 = 0 ∧ p.1.val ∈ L
    · rw [if_pos hp, mem_singleton]
      constructor
      · rintro ⟨⟨e, he, rfl⟩, h⟩
        have heq : e = p.1 := congrArg Prod.fst h
        exact congrArg (input X) heq
      · intro h
        subst a
        refine ⟨⟨p.1,hp.2,rfl⟩, ?_⟩
        change (p.1, (0 : Fin 2)) = p
        exact Prod.ext rfl hp.1.symm
    · simp only [if_neg hp, Finset.notMem_empty, iff_false]
      rintro ⟨⟨e, he, rfl⟩, h⟩
      apply hp
      have heq : e = p.1 := congrArg Prod.fst h
      exact ⟨(congrArg Prod.snd h).symm, by simpa [← heq] using he⟩
  unfold outDeg
  rw [hset]
  split_ifs <;> simp

theorem matching (L : Finset (V × V)) : MaxDegLE (arcsOf X L) 1 := by
  intro p
  unfold deg
  rw [in_count, out_count]
  split_ifs <;> simp_all

theorem cyclic (c : V → ZMod 3) (hc : IsCyc c X) :
    IsCyc (c ∘ root X) (arcs X) := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := (mem_arcsOf X).mp ha
  change c (root X (e,1)) = c (root X (e,0)) + 1
  simpa [root] using hc e.val he

end PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts.matching
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts.matching
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts.root_image
