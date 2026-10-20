/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PathReplacement

@[expose] public section

/-! Balance after root identification and arc-disjoint path replacement.
The source need only be balanced after identifying its endpoints. In particular,
an unused channel closes when its two ports have the same physical root.
This file does not supply the physical paths or their disjointness. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.FibrePathTransport

open Finset Cycles Positivization

variable {V W : Type} [DecidableEq V] [DecidableEq W]

theorem balanced_of_fibres (Q : Finset (V × V)) (f : V → W)
    (path : (V × V) → Finset (W × W))
    (hdis : (Q : Set (V × V)).PairwiseDisjoint path)
    (hnet : ∀ e ∈ Q, ∀ w, net (path e) w =
      (if f e.2 = w then 1 else 0) - (if f e.1 = w then 1 else 0))
    (hb : ∀ w, (Q.filter (fun e => f e.2 = w)).card =
      (Q.filter (fun e => f e.1 = w)).card) : Balanced (Q.biUnion path) := by
  apply (balanced_iff_net _).mpr
  intro w
  rw [net_biUnion Q path hdis, sum_congr rfl (fun e he => hnet e he w),
    sum_sub_distrib]
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hb w)
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcast
  exact sub_eq_zero.mpr hcast

theorem closed_walk_replace (v : ℕ → V) (m : ℕ) (f : V → W)
    (path : (V × V) → Finset (W × W))
    (hinj : Set.InjOn (fun j => (v j, v (j + 1))) (range m : Set ℕ))
    (hdis : (pathArcs v m : Set (V × V)).PairwiseDisjoint path)
    (hnet : ∀ e ∈ pathArcs v m, ∀ w, net (path e) w =
      (if f e.2 = w then 1 else 0) - (if f e.1 = w then 1 else 0))
    (hclose : f (v m) = f (v 0)) : Balanced ((pathArcs v m).biUnion path) := by
  apply (balanced_iff_net _).mpr
  intro w
  rw [net_biUnion (pathArcs v m) path hdis,
    sum_congr rfl (fun e he => hnet e he w)]
  unfold pathArcs
  rw [sum_image hinj]
  simpa only [hclose, sub_self] using
    (sum_range_sub (fun j => if f (v j) = w then (1 : ℤ) else 0) m)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.FibrePathTransport

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FibrePathTransport.balanced_of_fibres
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.FibrePathTransport.closed_walk_replace
