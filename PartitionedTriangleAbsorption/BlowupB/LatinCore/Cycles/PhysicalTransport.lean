/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Defs

@[expose] public section

/-! Physical vertex identifications preserve balance when arcs remain
injective. Vertices themselves need NOT be mapped injectively. This is a
transport theorem, not a producer of an embedding or a universal reserve. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

def arcImage (f : V → W) (e : V × V) : W × W := (f e.1, f e.2)

theorem degree_fiber (E : Finset (V × V)) (f : V → W)
    (h : Set.InjOn (arcImage f) (E : Set (V × V)))
    (endpoint : V × V → V) (endpoint' : W × W → W)
    (hendpoint : ∀ e, endpoint' (arcImage f e) = f (endpoint e)) (w : W) :
    ((E.image (arcImage f)).filter (fun e => endpoint' e = w)).card =
      ∑ v ∈ univ.filter (fun v => f v = w), (E.filter (fun e => endpoint e = v)).card := by
  rw [Finset.filter_image]
  have hinj : Set.InjOn (arcImage f)
      (↑(E.filter (fun e => endpoint' (arcImage f e) = w)) : Set (V × V)) :=
    h.mono (by intro e he; exact (Finset.mem_filter.mp he).1)
  rw [Finset.card_image_of_injOn hinj]
  simp only [hendpoint]
  rw [Finset.card_eq_sum_card_fiberwise
    (s := E.filter (fun e => f (endpoint e) = w)) (f := endpoint)
    (t := univ.filter (fun v => f v = w))
    (by intro e he; simpa using (Finset.mem_filter.mp he).2)]
  apply Finset.sum_congr rfl
  intro v hv
  have hvf := (Finset.mem_filter.mp hv).2
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨he, _⟩, hev⟩
    exact ⟨he, hev⟩
  · rintro ⟨he, hev⟩
    exact ⟨⟨he, by simpa [hev] using hvf⟩, hev⟩

theorem balanced_arcImage (E : Finset (V × V)) (f : V → W)
    (h : Set.InjOn (arcImage f) (E : Set (V × V))) (hE : Balanced E) :
    Balanced (E.image (arcImage f)) := by
  intro w
  unfold inDeg outDeg
  rw [degree_fiber E f h Prod.snd Prod.snd (fun _ => rfl),
      degree_fiber E f h Prod.fst Prod.fst (fun _ => rfl)]
  exact Finset.sum_congr rfl (fun v _ => hE v)

theorem deg_arcImage (E : Finset (V × V)) (f : V → W)
    (h : Set.InjOn (arcImage f) (E : Set (V × V))) (w : W) :
    deg (E.image (arcImage f)) w =
      ∑ v ∈ univ.filter (fun v => f v = w), deg E v := by
  unfold deg inDeg outDeg
  rw [degree_fiber E f h Prod.snd Prod.snd (fun _ => rfl),
      degree_fiber E f h Prod.fst Prod.fst (fun _ => rfl),
      Finset.sum_add_distrib]

/-- Exact load accounting for an indexed catalogue. Deduplicating the
physical pieces can only decrease its load; no vertex injectivity is used. -/
theorem catalog_load_arcImage (lib : Finset (Finset (V × V))) (f : V → W)
    (h : ∀ E ∈ lib, Set.InjOn (arcImage f) (E : Set (V × V))) (w : W) :
    ∑ E ∈ lib, deg (E.image (arcImage f)) w =
      ∑ v ∈ univ.filter (fun v => f v = w), ∑ E ∈ lib, deg E v := by
  calc
    _ = ∑ E ∈ lib, ∑ v ∈ univ.filter (fun v => f v = w), deg E v :=
      Finset.sum_congr rfl (fun E hE => deg_arcImage E f (h E hE) w)
    _ = _ := Finset.sum_comm

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.degree_fiber
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.balanced_arcImage
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.deg_arcImage
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.catalog_load_arcImage
