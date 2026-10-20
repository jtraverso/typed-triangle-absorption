/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Defs
public import PartitionedTriangleAbsorption.BlowupB.Flex.Relabel

@[expose] public section

/-! Exact physical transport of the conserved component to one tripartite
triangle family. Vertices and edges are unchanged; no existence theorem is
assumed or asserted. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer

def tripFamily : Finset (Multiset (Fin 3)) := {{0, 1, 2}}

theorem split_card_three (d : Case) (hd : Checked d)
    (τ : Multiset (Fin d.t)) (hτ : τ ∈ d.S.F') : τ.card = 3 := by
  simpa using hd.card_three (τ.map d.S.π) (d.S.π_mem τ hτ)

theorem core_type_iff (d : Case) (hd : Checked d)
    (τ : Multiset (Fin d.t)) (hτ : τ.card = 3)
    (hcore : ∀ r ∈ τ, d.comp r = d.core) :
    τ ∈ d.S.F' ↔ τ.map d.colour ∈ tripFamily := by
  obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hτ
  simpa [Link, tripFamily] using hd.core_exact a b c
    (hcore a (by simp)) (hcore b (by simp)) (hcore c (by simp))

theorem component_maps_to_trip (d : Case) (hd : Checked d)
    (τ : Multiset (Fin d.t)) (hτ : τ ∈ componentFamily d d.core) :
    τ.map d.colour ∈ tripFamily := by
  obtain ⟨hF, hc⟩ := Finset.mem_filter.mp hτ
  exact (core_type_iff d hd τ (split_card_three d hd τ hF) hc).mp hF

variable {V : Type*} [DecidableEq V]

theorem typedTri_iff (d : Case) (hd : Checked d) (p : V → Fin d.t)
    (hcore : ∀ v, d.comp (p v) = d.core) (s : Finset V) :
    IsTypedTri p d.S.F' s ↔ IsTypedTri (d.colour ∘ p) tripFamily s := by
  have hc : ∀ r ∈ s.val.map p, d.comp r = d.core := by
    intro r hr
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hr
    exact hcore v
  constructor
  · intro hs
    refine ⟨hs.1, ?_⟩
    have h := (core_type_iff d hd (s.val.map p) (by simpa using hs.1) hc).mp hs.2
    simpa only [Multiset.map_map] using h
  · intro hs
    refine ⟨hs.1, ?_⟩
    apply (core_type_iff d hd (s.val.map p) (by simpa using hs.1) hc).mpr
    simpa only [Multiset.map_map] using hs.2

theorem isDecomp_iff (d : Case) (hd : Checked d) (p : V → Fin d.t)
    (hcore : ∀ v, d.comp (p v) = d.core)
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) :
    IsDecomp p d.S.F' E D ↔ IsDecomp (d.colour ∘ p) tripFamily E D := by
  constructor
  · intro h
    exact ⟨fun s hs => (typedTri_iff d hd p hcore s).mp (h.1 s hs), h.2⟩
  · intro h
    exact ⟨fun s hs => (typedTri_iff d hd p hcore s).mpr (h.1 s hs), h.2⟩

theorem hasDecomp_iff (d : Case) (hd : Checked d) (p : V → Fin d.t)
    (hcore : ∀ v, d.comp (p v) = d.core) (E : Finset (Sym2 V)) :
    HasDecomp p d.S.F' E ↔ HasDecomp (d.colour ∘ p) tripFamily E :=
  exists_congr fun D => isDecomp_iff d hd p hcore E D

theorem isIntDiv_push [Fintype V] (d : Case) (hd : Checked d) (p : V → Fin d.t)
    (hcore : ∀ v, d.comp (p v) = d.core) {E : Finset (Sym2 V)}
    (h : IsIntDiv p d.S.F' E) : IsIntDiv (d.colour ∘ p) tripFamily E := by
  have hf : IsIntDiv p (componentFamily d d.core) E := by
    apply Flex.isIntDiv_filter p (fun r => d.comp r = d.core) hcore d.S.F' ?_ h
    intro τ hτ i hi hci j hj
    exact (hd.inside τ hτ i j (Multiset.count_pos.mpr hi)
      (Multiset.count_pos.mpr hj)).symm.trans hci
  exact Flex.isIntDiv_push d.colour p (componentFamily d d.core) tripFamily
    (component_maps_to_trip d hd) hf

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.core_type_iff
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.hasDecomp_iff
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.isIntDiv_push
