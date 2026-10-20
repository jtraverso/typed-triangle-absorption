/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.Reuse
public import PartitionedTriangleAbsorption.BlowupB.Flex.Relabel
public import PartitionedTriangleAbsorption.BlowupB.VertexSplit.ComponentsT

@[expose] public section

/-!
# A component of a family on `Fin t'` through a covered family on `Fin 4`

`CompIso F' c' k Fc cc kc`: label maps `φ : Fin t' → Fin 4`, `ψ : Fin 4 → Fin t'`, inverse
bijections between the classes of component `k` of `F'` and of component `kc` of `Fc`, carrying the
types inside one component onto the types inside the other (a finite fact, checked by `decide`).

`componentAbsorbers_via`: the flexible component certificate of `(Fc, cc, kc)` gives, in every host
on `Fin t'` with allowed edges and supply `a` in the classes of component `k`, componentwise
universal absorbers for component `k` (the hypothesis `hk` of
`CompT.universalAbsorbers_of_components`), at absolute degree bounds `R ≤ 2 ρ N`, `2 δ N ≤ D`,
where `N` is the size of the fake completion of the component part (`absorbers_of_componentFlex`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.PhysicalHingeSupply
open PaddedF12 PaddedGeneral PrivateTemplateStage69

/-- An isomorphism between component `k` of `F'` and component `kc` of `Fc`. -/
structure CompIso {t' : ℕ} (F' : Finset (Multiset (Fin t'))) (c' : Fin t' → Fin t') (k : Fin t')
    (Fc : Finset (Multiset (Fin 4))) (cc : Fin 4 → Fin 4) (kc : Fin 4) where
  φ : Fin t' → Fin 4
  ψ : Fin 4 → Fin t'
  φ_mem : ∀ i, c' i = k → cc (φ i) = kc
  ψφ : ∀ i, c' i = k → ψ (φ i) = i
  ψ_mem : ∀ j, cc j = kc → c' (ψ j) = k
  φψ : ∀ j, cc j = kc → φ (ψ j) = j
  map_φ : ∀ τ ∈ F', (∀ i ∈ τ, c' i = k) → τ.map φ ∈ Fc
  map_ψ : ∀ σ ∈ Fc, (∀ j ∈ σ, cc j = kc) → σ.map ψ ∈ F'

section Emb

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

theorem mem_map_emb_iff (f : W ↪ V) (w : W) (e : Sym2 W) :
    f w ∈ edgeEmb f e ↔ w ∈ e := by
  show f w ∈ Sym2.map f e ↔ w ∈ e
  constructor
  · intro hw
    obtain ⟨a, ha, hwa⟩ := Sym2.mem_map.mp hw
    exact f.injective hwa ▸ ha
  · intro hw
    exact Sym2.mem_map.mpr ⟨w, hw, rfl⟩

theorem card_filter_map_emb (f : W ↪ V) (E : Finset (Sym2 W)) (w : W) :
    ((E.map (edgeEmb f)).filter (fun e => f w ∈ e)).card = (E.filter (fun e => w ∈ e)).card := by
  rw [filter_map, card_map]
  congr 1
  exact filter_congr fun e _ => mem_map_emb_iff f w e

theorem card_filter_map_emb_out (f : W ↪ V) (E : Finset (Sym2 W)) (v : V) (hv : ∀ w, f w ≠ v) :
    ((E.map (edgeEmb f)).filter (fun e => v ∈ e)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hx
  obtain ⟨e', -, rfl⟩ := mem_map.mp he
  obtain ⟨a, -, ha⟩ := Sym2.mem_map.mp (show v ∈ Sym2.map f e' from hx)
  exact hv a ha

theorem degBounded_map_emb (f : W ↪ V) {E : Finset (Sym2 W)} {D : ℝ} (hE : DegBounded E D)
    (hD : 0 ≤ D) : DegBounded (E.map (edgeEmb f)) D := by
  intro v
  by_cases hv : ∃ w, f w = v
  · obtain ⟨w, rfl⟩ := hv
    rw [card_filter_map_emb]
    exact hE w
  · push Not at hv
    rw [card_filter_map_emb_out f E v hv]
    simpa using hD

theorem degBounded_comap_emb (f : W ↪ V) {E : Finset (Sym2 W)} {D : ℝ}
    (hE : DegBounded (E.map (edgeEmb f)) D) : DegBounded E D := by
  intro w
  have := hE (f w)
  rwa [card_filter_map_emb] at this

variable [Fintype W]

theorem map_filter_preimage (f : W ↪ V) (X : Finset (Sym2 V))
    (hX : ∀ e ∈ X, ∀ v ∈ e, ∃ w, f w = v) :
    (univ.filter fun e : Sym2 W => edgeEmb f e ∈ X).map (edgeEmb f) = X := by
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    exact (mem_filter.mp he').2
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨wx, rfl⟩ := hX _ he x (Sym2.mem_mk_left x y)
      obtain ⟨wy, rfl⟩ := hX _ he y (Sym2.mem_mk_right _ _)
      exact mem_map.mpr ⟨s(wx, wy), mem_filter.mpr ⟨mem_univ _, he⟩, rfl⟩

end Emb

/-- The decidable adjacency of the induced host on a subtype. -/
instance comapSubtypeDec {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (P : V → Prop) :
    DecidableRel (G.comap (Subtype.val : Subtype P → V)).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u.1 v.1))

/-- **A component of `F'` through a covered family.** -/
theorem componentAbsorbers_via {t' : ℕ} {F' : Finset (Multiset (Fin t'))} {c' : Fin t' → Fin t'}
    {k : Fin t'} (hτ' : VertexSplit.CompT.TypesInside F' c')
    {Fc : Finset (Multiset (Fin 4))} {cc : Fin 4 → Fin 4} {kc : Fin 4}
    (hcc : PaddedComponents.CompLabel Fc cc) (hτc : PaddedComponents.TypesInside Fc cc)
    (I : CompIso F' c' k Fc cc kc) (hcert : ComponentUniversalCertFlex Fc cc kc)
    {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin t') (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v → ∃ l, Link F' (p u) (p v) l)
    (a : ℝ) (hsupp : ∀ S : Finset V, S.card ≤ 2 ^ 21 → ∀ i, c' i = k →
      (∀ u ∈ S, ∃ l, Link F' (p u) i l) → a ≤ ((guardedNeighbours p G S i).card : ℝ))
    (M : ℕ) (ω δ ρ R D : ℝ)
    (hfl : FlexScales ω δ ρ (Fintype.card (WC cc kc M (W := {v // c' (p v) = k}))))
    (ha : ω * Fintype.card (WC cc kc M (W := {v // c' (p v) = k})) ≤ a)
    (hM : ω * Fintype.card (WC cc kc M (W := {v // c' (p v) = k})) + 2 ^ 21 ≤ M)
    (hR : R ≤ 2 * ρ * Fintype.card (WC cc kc M (W := {v // c' (p v) = k})))
    (hD : 2 * δ * Fintype.card (WC cc kc M (W := {v // c' (p v) = k})) ≤ D) :
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X R →
      (∀ e ∈ X, VertexSplit.CompT.InsideE p c' k e) →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
        (∀ e ∈ A, VertexSplit.CompT.InsideE p c' k e) ∧ HasDecomp p F' A ∧ DegBounded A D ∧
        ∀ L ⊆ X, IsIntDiv p F' L → HasDecomp p F' (A ∪ L) := by
  classical
  intro X hXG hX hXin
  let W := {v // c' (p v) = k}
  let ι : W ↪ V := Function.Embedding.subtype _
  let q : W → Fin 4 := fun w => I.φ (p w.1)
  let H : SimpleGraph W := G.comap Subtype.val
  have hq : ∀ w, cc (q w) = kc := fun w => I.φ_mem _ w.2
  have hpι : ∀ w : W, p (ι w) = (I.ψ ∘ q) w := fun w => (I.ψφ _ w.2).symm
  -- types through a vertex of component `k` lie inside `k`
  have hinside : ∀ τ ∈ F', ∀ i ∈ τ, c' i = k → ∀ j ∈ τ, c' j = k := by
    intro τ hτ i hi hik j hj
    rw [← hik]
    exact hτ' τ hτ j i (Multiset.count_pos.mpr hj) (Multiset.count_pos.mpr hi)
  have hinsidec : ∀ σ ∈ Fc, ∀ i ∈ σ, cc i = kc → ∀ j ∈ σ, cc j = kc := by
    intro σ hσ i hi hik j hj
    rw [← hik]
    exact hτc σ hσ j i (Multiset.count_pos.mpr hj) (Multiset.count_pos.mpr hi)
  -- the induced host on the component part
  have hH : ∀ u v : W, H.Adj u v → ∃ l, Link Fc (q u) (q v) l := by
    intro u v huv
    obtain ⟨l, hl⟩ := hG _ _ huv
    have hin : ∀ i ∈ ({p u.1, p v.1, l} : Multiset (Fin t')), c' i = k :=
      hinside _ hl (p u.1) (by simp) u.2
    have := I.map_φ _ hl hin
    exact ⟨I.φ l, by simpa [Link] using this⟩
  have hsuppW : ∀ S : Finset W, S.card ≤ 2 ^ 21 → ∀ i, cc i = kc →
      (∀ u ∈ S, ∃ l, Link Fc (q u) i l) →
        a ≤ ((univ.filter fun w => q w = i ∧ ∀ u ∈ S, H.Adj u w).card : ℝ) := by
    intro S hS i hi hguard
    have hguard' : ∀ u ∈ S.map ι, ∃ l, Link F' (p u) (I.ψ i) l := by
      intro u hu
      obtain ⟨u', hu', rfl⟩ := mem_map.mp hu
      obtain ⟨l, hl⟩ := hguard u' hu'
      have hin : ∀ j ∈ ({q u', i, l} : Multiset (Fin 4)), cc j = kc :=
        hinsidec _ hl (q u') (by simp) (hq u')
      have := I.map_ψ _ hl hin
      refine ⟨I.ψ l, ?_⟩
      have h1 : I.ψ (q u') = p u'.1 := I.ψφ _ u'.2
      simp only [Link, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at this ⊢
      rw [h1] at this
      exact this
    have h1 := hsupp (S.map ι) (by rw [card_map]; exact hS) (I.ψ i) (I.ψ_mem i hi) hguard'
    have hsub : guardedNeighbours p G (S.map ι) (I.ψ i) ⊆
        (univ.filter fun w => q w = i ∧ ∀ u ∈ S, H.Adj u w).map ι := by
      intro w' hw'
      obtain ⟨hpw, hadj⟩ := (mem_filter.mp hw').2
      have hw'k : c' (p w') = k := by rw [hpw]; exact I.ψ_mem i hi
      refine mem_map.mpr ⟨⟨w', hw'k⟩, mem_filter.mpr ⟨mem_univ _, ?_, fun u hu => ?_⟩, rfl⟩
      · show I.φ (p w') = i
        rw [hpw]; exact I.φψ i hi
      · exact hadj (ι u) (mem_map_of_mem _ hu)
    have h2 := card_le_card hsub
    rw [card_map] at h2
    have h2' : ((guardedNeighbours p G (S.map ι) (I.ψ i)).card : ℝ) ≤
        ((univ.filter fun w => q w = i ∧ ∀ u ∈ S, H.Adj u w).card : ℝ) := by exact_mod_cast h2
    linarith
  -- the reserve, pulled back to the component part
  have hXW : ∀ e ∈ X, ∀ v ∈ e, ∃ w : W, ι w = v := by
    intro e he v hv
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx, hy⟩ := (VertexSplit.CompT.insideE_mk p c' k x y).mp (hXin _ he)
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ⟨⟨v, hx⟩, rfl⟩
      · exact ⟨⟨v, hy⟩, rfl⟩
  set XW : Finset (Sym2 W) := univ.filter fun e : Sym2 W => edgeEmb ι e ∈ X with hXWdef
  have hXmap : XW.map (edgeEmb ι) = X := map_filter_preimage ι X hXW
  have hedge : ∀ e : Sym2 W, edgeEmb ι e ∈ G.edgeFinset → e ∈ H.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have : s(x.1, y.1) ∈ G.edgeFinset := he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this ⊢
      exact this
  have hedge' : ∀ e : Sym2 W, e ∈ H.edgeFinset → edgeEmb ι e ∈ G.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      show s(x.1, y.1) ∈ G.edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
      exact he
  have hXWH : XW ⊆ H.edgeFinset := fun e he => hedge e (hXG (mem_filter.mp he).2)
  have hXWdeg : DegBounded XW (2 * ρ * Fintype.card (WC cc kc M (W := W))) := by
    intro w
    have h1 := hX (ι w)
    rw [← hXmap, card_filter_map_emb] at h1
    exact h1.trans hR
  obtain ⟨AW, hAWH, hAWX, hAWdec, hAWdeg, hAWL⟩ :=
    absorbers_of_componentFlex Fc cc kc M hcc hcert q hq H hH a hsuppW ω δ ρ hfl ha hM
      XW hXWH hXWdeg
  have hδN : 0 ≤ 2 * δ * Fintype.card (WC cc kc M (W := W)) := by
    have := hfl.δ_pos; positivity
  -- decompositions on the component part give decompositions in the host
  have hdec : ∀ E : Finset (Sym2 W), HasDecomp q Fc E → HasDecomp p F' (E.map (edgeEmb ι)) := by
    intro E hE
    have h1 := hasDecomp_relabel q I.ψ (fun j => cc j = kc) hq Fc F'
      (fun σ hσ hin => I.map_ψ σ hσ hin) hE
    exact PhysicalHingeSupply.hasDecomp_map ι hpι h1
  refine ⟨AW.map (edgeEmb ι), fun e he => ?_, ?_, fun e he => ?_, hdec AW hAWdec, ?_, ?_⟩
  · obtain ⟨e', he', rfl⟩ := mem_map.mp he
    exact hedge' e' (hAWH he')
  · rw [← hXmap, disjoint_map]
    exact hAWX
  · obtain ⟨e', -, rfl⟩ := mem_map.mp he
    induction e' using Sym2.ind with
    | _ x y => exact (VertexSplit.CompT.insideE_mk p c' k x.1 y.1).mpr ⟨x.2, y.2⟩
  · exact degBounded_map_emb ι (fun w => (hAWdeg w).trans hD) (hδN.trans hD)
  · intro L hLX hL
    have hLW : ∀ e ∈ L, ∀ v ∈ e, ∃ w : W, ι w = v := fun e he => hXW e (hLX he)
    set LW : Finset (Sym2 W) := univ.filter fun e : Sym2 W => edgeEmb ι e ∈ L with hLWdef
    have hLmap : LW.map (edgeEmb ι) = L := map_filter_preimage ι L hLW
    have hLsub : LW ⊆ XW := fun e he =>
      mem_filter.mpr ⟨mem_univ _, hLX (mem_filter.mp he).2⟩
    have h1 : IsIntDiv (p ∘ ι) F' LW := isIntDiv_comap ι (by rw [hLmap]; exact hL)
    have h2 := isIntDiv_filter (p ∘ ι) (fun i => c' i = k) (fun w => w.2) F'
      (fun τ hτ i hi hik j hj => hinside τ hτ i hi hik j hj) h1
    have h3 := isIntDiv_push I.φ (p ∘ ι) _ Fc
      (fun τ hτ => I.map_φ τ (mem_filter.mp hτ).1 (mem_filter.mp hτ).2) h2
    have h4 := hAWL LW hLsub h3
    have h5 := hdec _ h4
    rwa [map_union, hLmap] at h5

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.componentAbsorbers_via
