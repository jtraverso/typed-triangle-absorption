/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.ChannelAssembly
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueLiftAugment
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.RootedMesoscopicSpec

@[expose] public section

/-! Complete a rooted mesoscopic catalogue with a fixed library of unused
paths. This is an abstract finite-set assembly, not a physical embedding. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CompletedCatalogue

open Finset Cycles Cycles.DenseRed

variable {V : Type} [Fintype V] [DecidableEq V]

def Spec (c : V → ZMod 3) (N I : Finset (V × V))
    (extra : Finset (Finset (V × V))) (C K H : ℕ) : Prop :=
  ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
    (R : Finset ((V ⊕ U) × (V ⊕ U)))
    (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U)))),
    IsCyc (Sum.elim c cU) R ∧ Disjoint R ((N ∪ I).map (liftArc V U)) ∧
    (∀ Q ∈ lib, Q.Nonempty ∧ Q ⊆ R ∪ (N ∪ I).map (liftArc V U) ∧
      Q.card ≤ max K H ∧ (Balanced Q ∨ Q ∈ CatalogueLift.lift U extra)) ∧
    (∀ v, catalogLoad lib (Sum.inl v) ≤ 73 * deg (N ∪ I) v + catalogLoad extra v) ∧
    (∀ u : U, catalogLoad lib (Sum.inr u) ^ 2 ≤ C ^ 2 * (N ∪ I).card) ∧
    lib.card ≤ C * (N ∪ I).card + extra.card ∧
    (∑ e ∈ CatalogueWeights.arcs lib, CatalogueWeights.weight lib e) ≤
      K * (C * (N ∪ I).card) + H * extra.card ∧
    ∀ L ⊆ I, (∃ A ⊆ N, Balanced (A ∪ L)) →
      ∃ Q ⊆ lib, (Q : Set (Finset ((V ⊕ U) × (V ⊕ U)))).PairwiseDisjoint id ∧
        Q.biUnion id = R ∪ (N ∪ L).map (liftArc V U)

theorem assemble (c : V → ZMod 3) (N I : Finset (V × V))
    (extra : Finset (Finset (V × V))) (C K H : ℕ)
    (hNI : Disjoint N I)
    (he : ∀ P ∈ extra, P.Nonempty ∧ P ⊆ N ∧ P.card ≤ H)
    (hrest : ∀ L ⊆ I, ∀ A ⊆ N, Balanced (A ∪ L) →
      ∃ Q ⊆ extra, (Q : Set (Finset (V × V))).PairwiseDisjoint id ∧
        Q.biUnion id = N \ A)
    (hmeso : RootedMesoscopicFor C K c (N ∪ I)) : Spec c N I extra C K H := by
  obtain ⟨U, hUf, hUd, cU, R, base, hcyc, hdis, hp, hsize, hload, hpart, hold⟩ := hmeso
  refine ⟨U, hUf, hUd, cU, R, base ∪ CatalogueLift.lift U extra,
    hcyc, hdis, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    rcases mem_union.mp hQ with hQ | hQ
    · exact ⟨(hp Q hQ).1, (hp Q hQ).2.1,
        (hp Q hQ).2.2.1.trans (le_max_left _ _), Or.inl (hp Q hQ).2.2.2⟩
    · obtain ⟨P, hP, rfl⟩ := mem_image.mp hQ
      refine ⟨(he P hP).1.map, ?_, ?_, Or.inr (mem_image.mpr ⟨P, hP, rfl⟩)⟩
      · exact (map_subset_map.mpr ((he P hP).2.1.trans subset_union_left)).trans
          subset_union_right
      · simpa only [card_map] using (he P hP).2.2.trans (le_max_right K H)
  · intro v
    exact (CatalogueLiftAugment.old_load base extra v).trans
      (Nat.add_le_add_right (hold v) _)
  · intro u
    exact (Nat.pow_le_pow_left (CatalogueLiftAugment.new_load base extra u) 2).trans
      (hload (Sum.inr u))
  · exact (card_union_le base _).trans (Nat.add_le_add hsize (CatalogueLift.size U extra))
  · exact (CatalogueLiftAugment.mass base extra K H
      (fun Q hQ => (hp Q hQ).2.2.1) (fun P hP => (he P hP).2.2)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left K hsize) _)
  · intro L hLI hcomp
    obtain ⟨A, hAN, hb⟩ := hcomp
    obtain ⟨Q, hQlib, hQdis, hQeq⟩ := hpart _ (union_subset_union hAN hLI) hb
    obtain ⟨unused, hu, hupair, hueq⟩ := hrest L hLI A hAN hb
    exact ChannelAssembly.complete_partition (liftArc V U) N L A hAN
      (hNI.mono_right hLI) extra unused hu hupair hueq R
      (hdis.mono_right (map_subset_map.mpr subset_union_left)) base Q hQlib hQdis hQeq

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CompletedCatalogue

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CompletedCatalogue.assemble
