/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.DenseVc
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseFinal

@[expose] public section

/-!
# `DenseRefiner` is proved

`denseRefinerWith : DenseRefinerWith Cdense 20` with the explicit absolute constant
`Cdense = Ccard + Cload`, and hence `denseRefiner : DenseRefiner` and, by the previously proved
reduction `mesoscopicRefiner_of_denseRefiner`, `mesoscopicRefiner : MesoscopicRefiner`.

Proof: the vertices of `H` are embedded colour-preservingly into the padded blow-up
`Vc N = ZMod 3 × Fin N` (`N = |H|`, each colour class has at most `N` vertices); the dense producer
on `Vc N` (`dense_on_Vc`) is applied to the image of `D`, and everything is transported along the
equivalence `Vc N ⊕ Priv ≃ H ⊕ (Pad ⊕ Priv)`, where `Pad` is the set of padding vertices.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer

open Finset Positivization Cycles

section Transport

variable {W X : Type} [DecidableEq W] [DecidableEq X]

/-- Arc map induced by a vertex embedding. -/
def arcMap (g : W ↪ X) : W × W ↪ X × X :=
  ⟨fun e => (g e.1, g e.2), by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (g.injective h.1) (g.injective h.2)⟩

theorem arcMap_apply (g : W ↪ X) (e : W × W) : arcMap g e = (g e.1, g e.2) := rfl

theorem inDeg_map_apply (g : W ↪ X) (P : Finset (W × W)) (w : W) :
    inDeg (P.map (arcMap g)) (g w) = inDeg P w := by
  unfold inDeg
  rw [filter_map, card_map]
  congr 1
  apply filter_congr
  intro e _
  change g e.2 = g w ↔ e.2 = w
  exact g.injective.eq_iff

theorem outDeg_map_apply (g : W ↪ X) (P : Finset (W × W)) (w : W) :
    outDeg (P.map (arcMap g)) (g w) = outDeg P w := by
  unfold outDeg
  rw [filter_map, card_map]
  congr 1
  apply filter_congr
  intro e _
  change g e.1 = g w ↔ e.1 = w
  exact g.injective.eq_iff

theorem inDeg_map_notin (g : W ↪ X) (P : Finset (W × W)) (x : X) (hx : ∀ w, g w ≠ x) :
    inDeg (P.map (arcMap g)) x = 0 := by
  unfold inDeg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he h
  obtain ⟨e, -, rfl⟩ := mem_map.mp he
  exact hx _ h

theorem outDeg_map_notin (g : W ↪ X) (P : Finset (W × W)) (x : X) (hx : ∀ w, g w ≠ x) :
    outDeg (P.map (arcMap g)) x = 0 := by
  unfold outDeg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he h
  obtain ⟨e, -, rfl⟩ := mem_map.mp he
  exact hx _ h

theorem balanced_map (g : W ↪ X) (P : Finset (W × W)) (hP : Balanced P) :
    Balanced (P.map (arcMap g)) := by
  intro x
  by_cases hx : ∃ w, g w = x
  · obtain ⟨w, rfl⟩ := hx
    rw [inDeg_map_apply, outDeg_map_apply, hP w]
  · push_neg at hx
    rw [inDeg_map_notin g P x hx, outDeg_map_notin g P x hx]

theorem deg_map_apply (g : W ↪ X) (P : Finset (W × W)) (w : W) :
    deg (P.map (arcMap g)) (g w) = deg P w := by
  unfold deg; rw [inDeg_map_apply, outDeg_map_apply]

theorem catalogLoad_map (g : W ↪ X) (lib : Finset (Finset (W × W))) (w : W) :
    catalogLoad (lib.map (Finset.mapEmbedding (arcMap g)).toEmbedding) (g w) =
      catalogLoad lib w := by
  unfold catalogLoad
  rw [sum_map]
  apply Finset.sum_congr rfl
  intro P _
  exact deg_map_apply g P w

theorem isCyc_map (g : W ↪ X) (cW : W → ZMod 3) (cX : X → ZMod 3) (hc : ∀ w, cX (g w) = cW w)
    (R : Finset (W × W)) (hR : IsCyc cW R) : IsCyc cX (R.map (arcMap g)) := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_map.mp he
  simp only [arcMap_apply, hc]
  exact hR e' he'

theorem biUnion_map (g : W ↪ X) (Q : Finset (Finset (W × W))) :
    (Q.map (Finset.mapEmbedding (arcMap g)).toEmbedding).biUnion id =
      (Q.biUnion id).map (arcMap g) := by
  ext α
  simp only [mem_biUnion, mem_map, id, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
  constructor
  · rintro ⟨_, ⟨P, hP, rfl⟩, hα⟩
    obtain ⟨β, hβ, rfl⟩ := mem_map.mp hα
    exact ⟨β, ⟨P, hP, hβ⟩, rfl⟩
  · rintro ⟨β, ⟨P, hP, hβ⟩, rfl⟩
    exact ⟨P.map (arcMap g), ⟨P, hP, rfl⟩, mem_map_of_mem _ hβ⟩

theorem pairwiseDisjoint_map (g : W ↪ X) (Q : Finset (Finset (W × W)))
    (hQ : (Q : Set (Finset (W × W))).PairwiseDisjoint id) :
    ((Q.map (Finset.mapEmbedding (arcMap g)).toEmbedding : Finset (Finset (X × X))) :
      Set (Finset (X × X))).PairwiseDisjoint id := by
  intro A hA B hB hAB
  simp only [coe_map, Set.mem_image, mem_coe, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply] at hA hB
  obtain ⟨P, hP, rfl⟩ := hA
  obtain ⟨P', hP', rfl⟩ := hB
  have hne : P ≠ P' := fun h => hAB (h ▸ rfl)
  simp only [Function.onFun, id]
  rw [disjoint_map]
  exact hQ hP hP' hne

end Transport

section Embedding

/-- A colour-preserving injection of `H` into the padded blow-up `Vc |H|`. -/
theorem exists_colour_embedding (H : Type) [Fintype H] [DecidableEq H] (c : H → ZMod 3) :
    ∃ ι : H → Vc (Fintype.card H), Function.Injective ι ∧ ∀ h, (ι h).1 = c h := by
  classical
  have hle : ∀ i : ZMod 3, Fintype.card {h // c h = i} ≤ Fintype.card (Fin (Fintype.card H)) := by
    intro i; rw [Fintype.card_fin]; exact Fintype.card_subtype_le _
  let emb : ∀ i : ZMod 3, {h // c h = i} ↪ Fin (Fintype.card H) :=
    fun i => Classical.choice (Function.Embedding.nonempty_of_card_le (hle i))
  refine ⟨fun h => (c h, emb (c h) ⟨h, rfl⟩), ?_, fun h => rfl⟩
  have key : ∀ (i j : ZMod 3) (x : {h // c h = i}) (y : {h // c h = j}), i = j →
      emb i x = emb j y → x.1 = y.1 := by
    rintro i j x y rfl hxy
    exact congrArg Subtype.val ((emb i).injective hxy)
  intro h h' hh
  simp only [Prod.mk.injEq] at hh
  exact key (c h) (c h') ⟨h, rfl⟩ ⟨h', rfl⟩ hh.1 hh.2

end Embedding

/-- **The explicit absolute constant of the dense producer.** -/
def Cdense : ℕ := Ccard + Cload

/-- **`DenseRefinerWith Cdense 20` is proved.** -/
theorem denseRefinerWith : DenseRefinerWith Cdense 20 := by
  intro H _ _ c D hD
  by_cases hN : Fintype.card H = 0
  · -- empty vertex set
    have hHe : IsEmpty H := Fintype.card_eq_zero_iff.mp hN
    refine ⟨Empty, inferInstance, inferInstance, Empty.elim, ∅, ∅, fun e he => by simp at he,
      disjoint_empty_left _, fun P hP => by simp at hP, by simp, fun v => ?_,
      fun L _ _ => ⟨∅, empty_subset _, by simp, ?_⟩⟩
    · simp [catalogLoad]
    · ext α
      simp only [biUnion_empty, notMem_empty, false_iff, mem_union, mem_map, not_or]
      refine ⟨by simp, ?_⟩
      rintro ⟨e, -, -⟩
      exact hHe.elim e.1
  · set n := Fintype.card H with hn
    haveI : NeZero n := ⟨hN⟩
    obtain ⟨ι, hι, hιc⟩ := exists_colour_embedding H c
    let ιe : H ↪ Vc n := ⟨ι, hι⟩
    let D' := D.map (arcMap ιe)
    have hD' : D' ⊆ Qc n := by
      intro α hα
      obtain ⟨e, he, rfl⟩ := mem_map.mp hα
      rw [mem_Qc]
      simp only [arcMap_apply, ιe, Function.Embedding.coeFn_mk, hιc]
      exact hD e he
    obtain ⟨R', lib', hR'cyc, hR'disj, hpieces, hcard, hload, hcover⟩ := dense_on_Vc D' hD'
    -- the padding vertices and the equivalence
    let Pad := {v : Vc n // v ∉ Set.range ι}
    let Pv := Priv (Vc n) Tc
    haveI : DecidableEq Pad := inferInstanceAs (DecidableEq {v : Vc n // v ∉ Set.range ι})
    haveI : Fintype Pad := by
      classical exact inferInstanceAs (Fintype {v : Vc n // v ∉ Set.range ι})
    haveI : DecidableEq Pv := inferInstanceAs (DecidableEq (Priv (Vc n) Tc))
    haveI : Fintype Pv := inferInstanceAs (Fintype (Priv (Vc n) Tc))
    let e1 : H ⊕ Pad ≃ Vc n :=
      ((Equiv.ofInjective ι hι).sumCongr (Equiv.refl Pad)).trans
        (@Equiv.sumCompl _ (fun v => v ∈ Set.range ι) (Classical.decPred _))
    let τ : H ⊕ (Pad ⊕ Pv) ≃ XV (Vc n) Tc :=
      (Equiv.sumAssoc H Pad Pv).symm.trans (e1.sumCongr (Equiv.refl Pv))
    have hτ : ∀ h, τ (Sum.inl h) = Sum.inl (ι h) := by
      intro h
      simp [τ, e1, Equiv.sumCompl]
    let σ : XV (Vc n) Tc ↪ H ⊕ (Pad ⊕ Pv) := τ.symm.toEmbedding
    have hσ : ∀ h, σ (Sum.inl (ι h)) = Sum.inl h := by
      intro h
      simp only [σ, Equiv.coe_toEmbedding]
      rw [← hτ h, Equiv.symm_apply_apply]
    let cW : XV (Vc n) Tc → ZMod 3 := Sum.elim (fun v : Vc n => v.1) (privColor (fun v => v.1))
    let cU : Pad ⊕ Pv → ZMod 3 := fun u => cW (τ (Sum.inr u))
    have hcol : ∀ w, Sum.elim c cU (σ w) = cW w := by
      intro w
      have hw : w = τ (σ w) := by simp [σ]
      generalize σ w = x at hw
      subst hw
      rcases x with h | u
      · simp only [Sum.elim_inl, hτ, cW, hιc]
      · rfl
    -- lifted arcs
    have hlift : ∀ L : Finset (H × H),
        ((L.map (arcMap ιe)).map (liftArc (Vc n) Pv)).map (arcMap σ) =
          L.map (liftArc H (Pad ⊕ Pv)) := by
      intro L
      rw [map_map, map_map]
      congr 1
      ext e : 1
      change (σ (Sum.inl (ι e.1)), σ (Sum.inl (ι e.2))) = (Sum.inl e.1, Sum.inl e.2)
      rw [hσ, hσ]
    refine ⟨Pad ⊕ Pv, inferInstance, inferInstance, cU, R'.map (arcMap σ),
      lib'.map (Finset.mapEmbedding (arcMap σ)).toEmbedding, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isCyc_map σ cW _ hcol R' hR'cyc
    · rw [← hlift D]
      exact (disjoint_map _).mpr hR'disj
    · intro P hP
      simp only [mem_map, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply] at hP
      obtain ⟨P, hP, rfl⟩ := hP
      obtain ⟨h1, h2, h3, h4⟩ := hpieces P hP
      refine ⟨h1.map, ?_, by rw [card_map]; exact h3, balanced_map σ P h4⟩
      rw [← hlift D, ← map_union]
      exact map_subset_map.mpr h2
    · rw [card_map]
      refine hcard.trans ?_
      unfold Cdense
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · intro x
      have hx : x = σ (τ x) := by simp [σ]
      rw [hx, catalogLoad_map]
      refine (hload _).trans ?_
      unfold Cdense
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    · intro L hLD hbal
      have hL'D : L.map (arcMap ιe) ⊆ D' := map_subset_map.mpr hLD
      obtain ⟨Q, hQ, hQdisj, hQcov⟩ := hcover _ hL'D (balanced_map ιe L hbal)
      refine ⟨Q.map (Finset.mapEmbedding (arcMap σ)).toEmbedding, ?_,
        pairwiseDisjoint_map σ Q hQdisj, ?_⟩
      · intro P hP
        simp only [mem_map, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply] at hP ⊢
        obtain ⟨P, hP, rfl⟩ := hP
        exact ⟨P, hQ hP, rfl⟩
      · rw [biUnion_map, hQcov, map_union, hlift L]

/-- **The dense refiner is proved** (absolute constants `Cdense`, `K = 20`). -/
theorem denseRefiner : DenseRefiner :=
  ⟨Cdense, 20, by unfold Cdense Ccard; omega, by norm_num, denseRefinerWith⟩

/-- **The mesoscopic refiner**, obtained from `denseRefiner` by the already proved reduction
`mesoscopicRefiner_of_denseRefiner`. -/
theorem mesoscopicRefiner : MesoscopicRefiner :=
  mesoscopicRefiner_of_denseRefiner denseRefiner

end PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer
