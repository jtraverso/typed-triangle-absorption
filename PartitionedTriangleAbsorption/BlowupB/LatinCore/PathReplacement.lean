/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Positivization.Channels

@[expose] public section

/-! Arc-disjoint path replacement preserves balance even when original vertices
are identified. The endpoint identity is sufficient; vertex injectivity is not.
This transport lemma does not assert the existence of the physical paths. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.PathReplacement

open Finset Cycles Positivization

variable {V W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]

theorem endpoint_fiber (Q : Finset (V × V)) (f : V → W)
    (endpoint : V × V → V) (w : W) :
    (Q.filter (fun e => f (endpoint e) = w)).card =
      ∑ v ∈ univ.filter (fun v => f v = w), (Q.filter (fun e => endpoint e = v)).card := by
  rw [card_eq_sum_card_fiberwise
    (s := Q.filter (fun e => f (endpoint e) = w)) (f := endpoint)
    (t := univ.filter (fun v => f v = w))
    (by intro e he; simpa using (mem_filter.mp he).2)]
  apply sum_congr rfl
  intro v hv
  have hvf := (mem_filter.mp hv).2
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨he, _⟩, hev⟩
    exact ⟨he, hev⟩
  · rintro ⟨he, hev⟩
    exact ⟨⟨he, by simpa [hev] using hvf⟩, hev⟩

/-- Paths may share vertices, including identified endpoints, but not arcs. -/
theorem balanced_replace (Q : Finset (V × V)) (f : V → W)
    (path : (V × V) → Finset (W × W))
    (hdis : (Q : Set (V × V)).PairwiseDisjoint path)
    (hnet : ∀ e ∈ Q, ∀ w, net (path e) w =
      (if f e.2 = w then 1 else 0) - (if f e.1 = w then 1 else 0))
    (hb : Balanced Q) : Balanced (Q.biUnion path) := by
  apply (balanced_iff_net _).mpr
  intro w
  rw [net_biUnion Q path hdis]
  rw [sum_congr rfl (fun e he => hnet e he w)]
  rw [sum_sub_distrib]
  have heq : (Q.filter (fun e => f e.2 = w)).card =
      (Q.filter (fun e => f e.1 = w)).card := by
    rw [endpoint_fiber Q f Prod.snd, endpoint_fiber Q f Prod.fst]
    exact sum_congr rfl (fun v _ => hb v)
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcast
  exact sub_eq_zero.mpr hcast

end PartitionedTriangleAbsorption.BlowupB.LatinCore.PathReplacement

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.PathReplacement.balanced_replace
