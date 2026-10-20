/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.ComponentCoreSupply
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.CoreScales
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Bridge.TriAbsorber
public import PartitionedTriangleAbsorption.BlowupB.Flex.Via

@[expose] public section

/-! Transfer a native three-colour certificate through the actual induced
conserved core, then return its absorber to the original physical host. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open StructuralF3General PaddedGeneral.RealInverse VertexSplit BalFixer PrivateTemplateStage69
open PhysicalHingeSupply

set_option maxHeartbeats 1000000

theorem hasDecomp_component {W : Type} [DecidableEq W]
    (d : Case) (p : W → Fin d.t) (hcore : ∀ w, d.comp (p w) = d.core)
    (E : Finset (Sym2 W)) (h : HasDecomp p d.S.F' E) :
    HasDecomp p (componentFamily d d.core) E := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, ?_, hD.2⟩
  intro s hs
  have ht := hD.1 s hs
  refine ⟨ht.1, mem_filter.mpr ⟨ht.2, ?_⟩⟩
  intro r hr
  obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hr
  exact hcore w

theorem component_core_absorbers {V : Type} [Fintype V] [DecidableEq V]
    (d : Case) (hd : Checked d) (L : ℕ)
    (hU : RefinerAbsorber.UniversalFamilyCert Bridge.F_tri L)
    (p : V → Fin d.t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω δ ρ : ℝ) (hfl : FlexScalesL L ω δ ρ (Fintype.card V))
    (hG : ∀ u v, G.Adj u v → ∃ k, Link (componentFamily d d.core) (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link (componentFamily d d.core) i j k)
      (2 ^ 21) (ω * Fintype.card V)) :
    let W := {v : V // d.comp (p v) = d.core}
    UniversalAbsorbers (fun v : W => d.colour (p v.val)) Bridge.F_tri
      (G.induce {v | d.comp (p v) = d.core})
      (ρ * Fintype.card V / Fintype.card W)
      (δ * Fintype.card V / Fintype.card W) := by
  classical
  let W := {v : V // d.comp (p v) = d.core}
  let q : W → Fin 3 := fun v => d.colour (p v.val)
  let H : SimpleGraph W := G.induce {v | d.comp (p v) = d.core}
  have hs' : GuardedSupply q H (fun i j => ∃ k, Link Bridge.F_tri i j k)
      (2 ^ 21) (ω * Fintype.card V) := component_core_supply d hd p G _ _ hs
  have hclass := hs' ∅ (by simp) (0 : Fin 3) (by simp)
  have hcard : (Fintype.card W : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_subtype_le (fun v : V => d.comp (p v) = d.core)
  have hsupply : ω * Fintype.card V ≤ Fintype.card W := hclass.trans
    (by exact_mod_cast card_le_univ (guardedNeighbours q H ∅ (0 : Fin 3)))
  have hsc := core_scales hfl hcard hsupply
  have hW : (Fintype.card W : ℝ) ≠ 0 := by
    intro hz
    have hh := hsc.ρn
    rw [hz] at hh
    norm_num at hh
  have hHG : ∀ u v : W, H.Adj u v → ∃ k, Link Bridge.F_tri (q u) (q v) k := by
    intro u v huv
    obtain ⟨k, hk⟩ := hG u.val v.val huv
    have hfull : Link d.S.F' (p u.val) (p v.val) k := (mem_filter.mp hk).1
    have hkc : d.comp k = d.core := (mem_filter.mp hk).2 k (by simp)
    refine ⟨d.colour k, ?_⟩
    have hh := (hd.core_exact _ _ _ u.property v.property hkc).mp hfull
    simpa only [Link, Bridge.F_tri, mem_singleton] using hh
  apply hU W q H (ω * Fintype.card V / Fintype.card W)
    (δ * Fintype.card V / Fintype.card W) (ρ * Fintype.card V / Fintype.card W) hsc hHG
  have heq : (ω * Fintype.card V / Fintype.card W) * Fintype.card W = ω * Fintype.card V :=
    div_mul_cancel₀ _ hW
  rw [heq]
  exact hs'

theorem core_certificate (d : Case) (hd : Checked d) (L : ℕ)
    (hU : RefinerAbsorber.UniversalFamilyCert Bridge.F_tri L) :
    ComponentCertFlexTL (componentFamily d d.core) d.comp d.core L := by
  intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hXdeg hXin
  classical
  let W := {v : V // d.comp (p v) = d.core}
  let ι : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let H : SimpleGraph W := G.induce {v | d.comp (p v) = d.core}
  let q : W → Fin 3 := fun v => d.colour (p v.val)
  have hUW := component_core_absorbers d hd L hU p G ω δ ρ hfl hG hs
  have hs' := component_core_supply d hd p G (2 ^ 21) (ω * Fintype.card V) hs
  have hsupply : ω * Fintype.card V ≤ (Fintype.card W : ℝ) :=
    (hs' ∅ (by simp) (0 : Fin 3) (by simp)).trans
      (by exact_mod_cast card_le_univ (guardedNeighbours q H ∅ (0 : Fin 3)))
  have hn : 0 < (Fintype.card V : ℝ) := by
    have hρn := hfl.ρn
    have hρ : 0 < ρ := by by_contra h; push Not at h; nlinarith [hfl.n_nonneg]
    nlinarith
  have hW : (Fintype.card W : ℝ) ≠ 0 := by
    have hh : 0 < ω * (Fintype.card V : ℝ) := mul_pos hfl.ω_pos hn
    linarith
  have hXW : ∀ e ∈ X, ∀ v ∈ e, ∃ w : W, ι w = v := by
    intro e he v hv
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha,hb⟩ := (CompT.insideE_mk p d.comp d.core a b).mp (hXin _ he)
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ⟨⟨v,ha⟩,rfl⟩
      · exact ⟨⟨v,hb⟩,rfl⟩
  let XW : Finset (Sym2 W) := univ.filter (fun e => edgeEmb ι e ∈ X)
  have hXmap : XW.map (edgeEmb ι) = X := Flex.map_filter_preimage ι X hXW
  have hXWH : XW ⊆ H.edgeFinset := by
    intro e he
    have hh := hXG (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ a b =>
      apply SimpleGraph.mem_edgeFinset.mpr
      change G.Adj a.val b.val
      exact SimpleGraph.mem_edgeFinset.mp hh
  have heqρ : 2 * (ρ * Fintype.card V / Fintype.card W) * Fintype.card W =
      2 * ρ * Fintype.card V := by field_simp
  have hXWd : DegBounded XW (2 * (ρ * Fintype.card V / Fintype.card W) * Fintype.card W) := by
    rw [heqρ]
    intro w
    have hh := hXdeg (ι w)
    rw [← hXmap, Flex.card_filter_map_emb] at hh
    exact hh
  obtain ⟨AW,hAWH,hAWX,hAWdec,hAWdeg,hAWL⟩ := hUW XW hXWH hXWd
  have heqδ : 2 * (δ * Fintype.card V / Fintype.card W) * Fintype.card W =
      2 * δ * Fintype.card V := by field_simp
  have hedge : ∀ e ∈ H.edgeFinset, edgeEmb ι e ∈ G.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      apply SimpleGraph.mem_edgeFinset.mpr
      change G.Adj a.val b.val
      exact SimpleGraph.mem_edgeFinset.mp he
  have hdec : ∀ E : Finset (Sym2 W), HasDecomp q Bridge.F_tri E →
      HasDecomp p (componentFamily d d.core) (E.map (edgeEmb ι)) := by
    intro E hh
    have hfull := (hasDecomp_iff d hd (p ∘ ι) (fun w => w.property) E).mpr hh
    exact PhysicalHingeSupply.hasDecomp_map ι (fun _ => rfl)
      (hasDecomp_component d (p ∘ ι) (fun w => w.property) E hfull)
  refine ⟨AW.map (edgeEmb ι), ?_, ?_, ?_, hdec AW hAWdec, ?_, ?_⟩
  · intro e he
    obtain ⟨e',he',rfl⟩ := mem_map.mp he
    exact hedge e' (hAWH he')
  · rw [← hXmap, disjoint_map]
    exact hAWX
  · intro e he
    obtain ⟨e',_,rfl⟩ := mem_map.mp he
    induction e' using Sym2.ind with
    | _ a b => exact (CompT.insideE_mk p d.comp d.core a.val b.val).mpr ⟨a.property,b.property⟩
  · rw [heqδ] at hAWdeg
    exact Flex.degBounded_map_emb ι hAWdeg (by have hδ := hfl.δ_pos; positivity)
  · intro R hRX hRdiv
    let RW : Finset (Sym2 W) := univ.filter (fun e => edgeEmb ι e ∈ R)
    have hRmap : RW.map (edgeEmb ι) = R :=
      Flex.map_filter_preimage ι R (fun e he => hXW e (hRX he))
    have hRsub : RW ⊆ XW := fun e he => mem_filter.mpr ⟨mem_univ _,hRX (mem_filter.mp he).2⟩
    have hdivW : IsIntDiv (p ∘ ι) (componentFamily d d.core) RW :=
      isIntDiv_comap ι (by rw [hRmap]; exact hRdiv)
    have htrip : IsIntDiv q Bridge.F_tri RW := Flex.isIntDiv_push d.colour (p ∘ ι)
      (componentFamily d d.core) tripFamily (component_maps_to_trip d hd) hdivW
    have hh := hdec _ (hAWL RW hRsub htrip)
    rwa [map_union,hRmap] at hh

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.core_certificate
