/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.Transfer

@[expose] public section

/-!
# Vertex splitting: allowed edges and guarded supply of the split host

* `splitG_allowed`: the edges of the split host are allowed for the split family `F'`.
* `guardedSupply_split`: the guarded supply of `G` (for `F`) is a guarded supply of the split host
  (for `F'`), with the same guard size and the same absolute value, under two finite conditions on
  the splitting data: the allowed pairs of `F'` are the copy pairs (`hpair`), and every class of
  `Fin t'` is a copy class (`hsurj`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.VertexSplit

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

variable {t t' : ℕ} {F : Finset (Multiset (Fin t))} (S : SplitData F t')
variable {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin t)

theorem π_sp (x : SV S p) : S.π (sp S p x) = p (fstV S p x) := by
  obtain ⟨s, hs⟩ := x.2
  show S.π x.1.2 = p x.1.1
  rw [hs]
  exact S.π_cls _ _

theorem splitG_adj_cp (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (h : G.Adj u w) :
    (splitG S p G).Adj (cp S p u (p w)) (cp S p w (p u)) := by
  have hmem : splitEdge S p s(u, w) ∈ splitE S p G.edgeFinset :=
    mem_image_of_mem _ (SimpleGraph.mem_edgeFinset.mpr h)
  rw [← edgeFinset_splitG, splitEdge_mk, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet] at hmem
  exact hmem

/-- The edges of the split host are allowed for `F'`. -/
theorem splitG_allowed (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) :
    ∀ x y, (splitG S p G).Adj x y → ∃ k', Link S.F' (sp S p x) (sp S p y) k' := by
  intro x y hxy
  have hmem : s(x, y) ∈ splitE S p G.edgeFinset := by
    rw [← edgeFinset_splitG]; exact SimpleGraph.mem_edgeFinset.mpr hxy
  obtain ⟨e, he, hexy⟩ := mem_image.mp hmem
  induction e using Sym2.ind with
  | _ u w =>
    have hadj : G.Adj u w := SimpleGraph.mem_edgeFinset.mp he
    obtain ⟨k, hk⟩ := hG u w hadj
    have hsig := S.sig_mem _ hk
    rw [S.sig_tri _ _ _ hk] at hsig
    have hcu : S.cls (p u) (p w) = S.κ (p u) (p w) := S.cls_of_link hk
    have hcw : S.cls (p w) (p u) = S.κ (p w) (p u) :=
      S.cls_of_link ((link_root_swap F _ _ _).mp hk)
    rw [splitEdge_mk, Sym2.eq_iff] at hexy
    rcases hexy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨S.κ k (p u), ?_⟩
      rw [sp_cp, sp_cp, hcu, hcw]
      exact hsig
    · refine ⟨S.κ k (p u), ?_⟩
      rw [sp_cp, sp_cp, hcu, hcw]
      exact (link_root_swap S.F' _ _ _).mp hsig

/-- **The guarded supply passes to the split host.** -/
theorem guardedSupply_split (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (a : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) D a)
    (hpair : ∀ i' j' : Fin t', (∃ k', Link S.F' i' j' k') →
      S.cls (S.π i') (S.π j') = i' ∧ S.cls (S.π j') (S.π i') = j')
    (hsurj : ∀ j' : Fin t', ∃ s, S.cls (S.π j') s = j') :
    GuardedSupply (sp S p) (splitG S p G) (fun i j => ∃ k, Link S.F' i j k) D a := by
  classical
  intro T' hT' j' hguard
  have hT : (T'.image (fstV S p)).card ≤ D := card_image_le.trans hT'
  have hTg : ∀ u ∈ T'.image (fstV S p), ∃ k, Link F (p u) (S.π j') k := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    obtain ⟨k', hk'⟩ := hguard x hx
    have := S.π_mem _ hk'
    refine ⟨S.π k', ?_⟩
    rw [← π_sp S p x]
    simpa [Link] using this
  have h1 := hs _ hT (S.π j') hTg
  obtain ⟨s0, hs0⟩ := hsurj j'
  let f : V → SV S p := fun w =>
    if h : p w = S.π j' then ⟨(w, j'), s0, by show j' = S.cls (p w) s0; rw [h]; exact hs0.symm⟩
    else cp S p w (p w)
  have hfpos : ∀ w (h : p w = S.π j'), f w =
      ⟨(w, j'), s0, by show j' = S.cls (p w) s0; rw [h]; exact hs0.symm⟩ :=
    fun w h => dif_pos h
  have hfneg : ∀ w, ¬ p w = S.π j' → f w = cp S p w (p w) := fun w h => dif_neg h
  have hf1 : ∀ w, fstV S p (f w) = w := by
    intro w
    by_cases h : p w = S.π j'
    · rw [hfpos w h]; rfl
    · rw [hfneg w h]; rfl
  have hmaps : ∀ w ∈ guardedNeighbours p G (T'.image (fstV S p)) (S.π j'),
      f w ∈ guardedNeighbours (sp S p) (splitG S p G) T' j' := by
    intro w hw
    obtain ⟨hpw, hadj⟩ := (mem_filter.mp hw).2
    refine mem_filter.mpr ⟨mem_univ _, ?_, fun x hx => ?_⟩
    · rw [hfpos w hpw]; rfl
    · have hux : G.Adj (fstV S p x) w := hadj _ (mem_image_of_mem _ hx)
      have hA := splitG_adj_cp S p G hux
      obtain ⟨hc1, hc2⟩ := hpair (sp S p x) j' (hguard x hx)
      have hpx : p (fstV S p x) = S.π (sp S p x) := (π_sp S p x).symm
      have e1 : cp S p (fstV S p x) (p w) = x := by
        apply Subtype.ext
        refine Prod.ext rfl ?_
        show S.cls (p (fstV S p x)) (p w) = sp S p x
        rw [hpx, hpw]; exact hc1
      have e2 : cp S p w (p (fstV S p x)) = f w := by
        rw [hfpos w hpw]
        apply Subtype.ext
        refine Prod.ext rfl ?_
        show S.cls (p w) (p (fstV S p x)) = j'
        rw [hpx, hpw]; exact hc2
      rw [e1, e2] at hA
      exact hA
  have hinj : Set.InjOn f (guardedNeighbours p G (T'.image (fstV S p)) (S.π j')) :=
    fun w _ w' _ h => by rw [← hf1 w, ← hf1 w', h]
  have h2 := card_le_card_of_injOn f hmaps hinj
  have h2' : ((guardedNeighbours p G (T'.image (fstV S p)) (S.π j')).card : ℝ) ≤
      (guardedNeighbours (sp S p) (splitG S p G) T' j').card := by exact_mod_cast h2
  exact h1.trans h2'

end PartitionedTriangleAbsorption.BlowupB.VertexSplit

#print axioms PartitionedTriangleAbsorption.BlowupB.VertexSplit.splitG_allowed
#print axioms PartitionedTriangleAbsorption.BlowupB.VertexSplit.guardedSupply_split
