/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseTags
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.PhysicalTransport

@[expose] public section

/-!
# `DenseRefiner + good partition → mesoscopic conclusion`

Given a good hub partition `p` of `Y` (`HasGoodPartition`) and the dense refiner applied to the
simple quotient `D₀ = {(p u, p v) : (u, v) ∈ Y}` on the hub set `P`, we build the reserve

  `R = ⋃_{e ∈ Y} (π_e + O_e + Q_e + I_e)  ∪  ι(R')`

and the fixed library

  `lib = {e + π_e} ∪ {basal pieces} ∪ {I_e + O_f : e.2 = f.1} ∪ ι(lib')`.

For a balanced `L ⊆ Y`: triangles for `e ∈ L`, basal pieces for `e ∉ L`, transition cycles
`I_e + O_{β e}` at every vertex, and the hub-level residual `{Q_e : e ∈ L}` is exactly the
image of the balanced quotient `D_L = p(L) ⊆ D₀`, which the dense refiner partitions together
with `R'`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace DenseRed

open Hub (ne_of_cyc deg_biUnion)
open MesoCutHub (dPairs deg_mono deg_union_le sum_union_le' sum_image_le'
  sum_filter_prod_fst_le sum_filter_prod_snd_le outDeg_le_of_maxDeg inDeg_le_of_maxDeg
  card_dPairs_le)

section Partition

variable {V P U' : Type} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
  [Fintype U'] [DecidableEq U'] (p : V → P)

/-- The first-level reserve. -/
def R1 (Y : Finset (V × V)) : Finset (TV V P U' × TV V P U') := Y.biUnion (Ccyc p)

/-- The total reserve. -/
def resv (Y : Finset (V × V)) (R' : Finset ((P ⊕ U') × (P ⊕ U'))) :
    Finset (TV V P U' × TV V P U') :=
  R1 p Y ∪ R'.map arcE

/-- The total library. -/
def libT (Y : Finset (V × V)) (lib' : Finset (Finset ((P ⊕ U') × (P ⊕ U')))) :
    Finset (Finset (TV V P U' × TV V P U')) :=
  Y.image Tcyc ∪ Y.image (Ccyc p) ∪ (dPairs Y).image (fun ef => Dcyc p ef.1 ef.2) ∪
    lib'.image (fun P' => P'.map arcE)

omit [Fintype V] [Fintype P] [Fintype U'] in
lemma mem_liftArc_iff {L : Finset (V × V)} {a : TV V P U' × TV V P U'} :
    a ∈ L.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U'))) ↔ ∃ e ∈ L, a = (old e.1, old e.2) := by
  simp only [Finset.mem_map, liftArc, Function.Embedding.coeFn_mk, old]
  exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩

/-- Classes of arcs inside the chosen pieces. -/
def Cls (Y L : Finset (V × V)) (β : V × V → V × V) (Q' : Finset (Finset ((P ⊕ U') × (P ⊕ U'))))
    (q : Finset (TV V P U' × TV V P U')) (a : TV V P U' × TV V P U') : Prop :=
  (∃ e ∈ L, q = Tcyc e ∧ (a = (old e.1, old e.2) ∨ tag a = some (e, 0))) ∨
  (∃ f ∈ Y, f ∉ L ∧ q = Ccyc p f ∧ ((∃ k, tag a = some (f, k)) ∨ a = (hub (p f.1), hub (p f.2)))) ∨
  (∃ e ∈ L, q = Dcyc p e (β e) ∧ (tag a = some (e, 2) ∨ tag a = some (β e, 1))) ∨
  (∃ q' ∈ Q', q = q'.map arcE ∧ ∃ x ∈ q', arcE x = a)

theorem partition_libT {Y : Finset (V × V)}
    (hinj : ∀ e ∈ Y, ∀ e' ∈ Y, p e.1 = p e'.1 → p e.2 = p e'.2 → e = e')
    (R' : Finset ((P ⊕ U') × (P ⊕ U'))) (lib' : Finset (Finset ((P ⊕ U') × (P ⊕ U'))))
    (hR'disj : Disjoint R' ((Y.image (arcImage p)).map (liftArc P U')))
    (hpart' : ∀ L ⊆ Y.image (arcImage p), Balanced L →
      ∃ Q' ⊆ lib', (Q' : Set (Finset ((P ⊕ U') × (P ⊕ U')))).PairwiseDisjoint id ∧
        Q'.biUnion id = R' ∪ L.map (liftArc P U'))
    (L : Finset (V × V)) (hLY : L ⊆ Y) (hLb : Balanced L) :
    ∃ Q ⊆ libT p Y lib', (Q : Set (Finset (TV V P U' × TV V P U'))).PairwiseDisjoint id ∧
      Q.biUnion id = resv p Y R' ∪ L.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U'))) := by
  classical
  obtain ⟨β, hβ, hβinj, hβsurj⟩ := Hub.exists_pairing L hLb
  have hInjL : Set.InjOn (arcImage p) (L : Set (V × V)) := by
    intro e he e' he' h
    simp only [arcImage, Prod.mk.injEq] at h
    exact hinj e (hLY he) e' (hLY he') h.1 h.2
  have hDL : L.image (arcImage p) ⊆ Y.image (arcImage p) := Finset.image_subset_image hLY
  have hDLb : Balanced (L.image (arcImage p)) := balanced_arcImage L p hInjL hLb
  obtain ⟨Q', hQ'lib, hQ'disj, hQ'cov⟩ := hpart' _ hDL hDLb
  -- the hub arc of `e`, as a hub-level arc
  have hQAe : ∀ e : V × V, ((hub (p e.1), hub (p e.2)) : TV V P U' × TV V P U') =
      arcE (liftArc P U' (arcImage p e)) := fun e => rfl
  refine ⟨L.image Tcyc ∪ (Y \ L).image (Ccyc p) ∪ L.image (fun e => Dcyc p e (β e)) ∪
    Q'.image (fun q' => q'.map arcE), ?_, ?_, ?_⟩
  · -- inside the library
    intro q hq
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
    simp only [libT, dPairs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product]
    rcases hq with ((⟨e, he, rfl⟩ | ⟨e, ⟨he, -⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨q', hq', rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨e, hLY he, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))
    · exact Or.inl (Or.inr ⟨(e, β e), ⟨⟨hLY he, hLY (hβ e he).1⟩, (hβ e he).2.symm⟩, rfl⟩)
    · exact Or.inr ⟨q', hQ'lib hq', rfl⟩
  · -- pairwise disjointness
    have hclass : ∀ q ∈ L.image Tcyc ∪ (Y \ L).image (Ccyc p) ∪
        L.image (fun e => Dcyc p e (β e)) ∪ Q'.image (fun q' => q'.map arcE),
        ∀ a ∈ q, Cls p Y L β Q' q a := by
      intro q hq a ha
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hq
      rcases hq with ((⟨e, he, rfl⟩ | ⟨f, ⟨hf, hfL⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨q', hq', rfl⟩
      · refine Or.inl ⟨e, he, rfl, ?_⟩
        simp only [Tcyc, Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact Or.inl rfl
        · exact Or.inr (tag_piA ha)
      · exact Or.inr (Or.inl ⟨f, hf, hfL, rfl, Ccyc_cases p ha⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨e, he, rfl, ?_⟩))
        simp only [Dcyc, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact Or.inl (tag_IA p ha)
        · exact Or.inr (tag_OA p ha)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
        exact Or.inr (Or.inr (Or.inr ⟨q', hq', rfl, x, hx, rfl⟩))
    have hcls_eq : ∀ {q₁ q₂ a}, Cls p Y L β Q' q₁ a → Cls p Y L β Q' q₂ a → q₁ = q₂ := by
      intro q₁ q₂ a h₁ h₂
      rcases h₁ with ⟨e₁, he₁, rfl, t₁⟩ | ⟨f₁, hf₁, hf₁L, rfl, t₁⟩ | ⟨e₁, he₁, rfl, t₁⟩ |
          ⟨q₁', hq₁', rfl, x₁, hx₁, rfl⟩ <;>
        rcases h₂ with ⟨e₂, he₂, rfl, t₂⟩ | ⟨f₂, hf₂, hf₂L, rfl, t₂⟩ | ⟨e₂, he₂, rfl, t₂⟩ |
          ⟨q₂', hq₂', rfl, x₂, hx₂, h₂x⟩
      -- T T
      · rcases t₁ with rfl | t₁ <;> rcases t₂ with h | t₂
        · simp only [old, Prod.mk.injEq, Sum.inl.injEq] at h; rw [Prod.ext h.1 h.2]
        · rw [tag_old] at t₂; simp at t₂
        · rw [h, tag_old] at t₁; simp at t₁
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂; rw [t₂.1]
      -- T C
      · exfalso
        rcases t₁ with rfl | t₁ <;> rcases t₂ with ⟨k, t₂⟩ | t₂
        · rw [tag_old] at t₂; simp at t₂
        · simp [old, hub] at t₂
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂
          exact hf₂L (t₂.1 ▸ he₁)
        · rw [t₂, tag_hub] at t₁; simp at t₁
      -- T D
      · exfalso
        rcases t₁ with rfl | t₁ <;> rcases t₂ with t₂ | t₂
        · rw [tag_old] at t₂; simp at t₂
        · rw [tag_old] at t₂; simp at t₂
        · rw [t₁] at t₂; simp at t₂
        · rw [t₁] at t₂; simp at t₂
      -- T Q'
      · exfalso
        rcases t₁ with h | t₁
        · exact old_ne_arcE _ _ x₂ (h₂x.trans h)
        · exact arcE_not_mem_tagged t₁ x₂ h₂x
      -- C T
      · exfalso
        rcases t₂ with h | t₂ <;> rcases t₁ with ⟨k, t₁⟩ | t₁
        · rw [h, tag_old] at t₁; simp at t₁
        · rw [h] at t₁; simp [old, hub] at t₁
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂
          exact hf₁L (t₂.1 ▸ he₂)
        · rw [t₁, tag_hub] at t₂; simp at t₂
      -- C C
      · rcases t₁ with ⟨k, t₁⟩ | t₁ <;> rcases t₂ with ⟨k', t₂⟩ | t₂
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂; rw [t₂.1]
        · rw [t₂, tag_hub] at t₁; simp at t₁
        · rw [t₁, tag_hub] at t₂; simp at t₂
        · rw [t₁] at t₂
          simp only [hub, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq] at t₂
          rw [hinj f₁ hf₁ f₂ hf₂ t₂.1 t₂.2]
      -- C D
      · exfalso
        rcases t₁ with ⟨k, t₁⟩ | t₁ <;> rcases t₂ with t₂ | t₂
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂
          exact hf₁L (t₂.1 ▸ he₂)
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂
          exact hf₁L (t₂.1 ▸ (hβ e₂ he₂).1)
        · rw [t₁, tag_hub] at t₂; simp at t₂
        · rw [t₁, tag_hub] at t₂; simp at t₂
      -- C Q'
      · exfalso
        rcases t₁ with ⟨k, t₁⟩ | t₁
        · exact arcE_not_mem_tagged t₁ x₂ h₂x
        · rw [hQAe] at t₁
          have hx : x₂ = liftArc P U' (arcImage p f₁) := arcE.injective (h₂x.trans t₁)
          have hmem : x₂ ∈ R' ∪ (L.image (arcImage p)).map (liftArc P U') := by
            rw [← hQ'cov]; exact Finset.mem_biUnion.2 ⟨q₂', hq₂', hx₂⟩
          rcases Finset.mem_union.1 hmem with h | h
          · rw [hx] at h
            exact Finset.disjoint_left.1 hR'disj h
              (Finset.mem_map_of_mem _ (Finset.mem_image_of_mem _ hf₁))
          · rw [hx] at h
            obtain ⟨y, hy, hyx⟩ := Finset.mem_map.1 h
            obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hy
            have := (liftArc P U').injective hyx
            simp only [arcImage, Prod.mk.injEq] at this
            exact hf₁L (hinj e' (hLY he') f₁ hf₁ this.1 this.2 ▸ he')
      -- D T
      · exfalso
        rcases t₂ with h | t₂ <;> rcases t₁ with t₁ | t₁
        · rw [h, tag_old] at t₁; simp at t₁
        · rw [h, tag_old] at t₁; simp at t₁
        · rw [t₁] at t₂; simp at t₂
        · rw [t₁] at t₂; simp at t₂
      -- D C
      · exfalso
        rcases t₂ with ⟨k, t₂⟩ | t₂ <;> rcases t₁ with t₁ | t₁
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂
          exact hf₂L (t₂.1 ▸ he₁)
        · rw [t₁] at t₂; simp only [Option.some.injEq, Prod.mk.injEq] at t₂
          exact hf₂L (t₂.1 ▸ (hβ e₁ he₁).1)
        · rw [t₂, tag_hub] at t₁; simp at t₁
        · rw [t₂, tag_hub] at t₁; simp at t₁
      -- D D
      · rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂ <;> rw [t₁] at t₂ <;>
          simp only [Option.some.injEq, Prod.mk.injEq] at t₂
        · rw [t₂.1]
        · simp at t₂
        · simp at t₂
        · rw [hβinj e₁ he₁ e₂ he₂ t₂.1]
      -- D Q'
      · exfalso
        rcases t₁ with t₁ | t₁ <;> exact arcE_not_mem_tagged t₁ x₂ h₂x
      -- Q' T
      · exfalso
        rcases t₂ with h | t₂
        · exact old_ne_arcE _ _ x₁ h
        · rw [tag_arcE] at t₂; simp at t₂
      -- Q' C
      · exfalso
        rcases t₂ with ⟨k, t₂⟩ | t₂
        · rw [tag_arcE] at t₂; simp at t₂
        · rw [hQAe] at t₂
          have hx : x₁ = liftArc P U' (arcImage p f₂) := arcE.injective t₂
          have hmem : x₁ ∈ R' ∪ (L.image (arcImage p)).map (liftArc P U') := by
            rw [← hQ'cov]; exact Finset.mem_biUnion.2 ⟨q₁', hq₁', hx₁⟩
          rcases Finset.mem_union.1 hmem with h | h
          · rw [hx] at h
            exact Finset.disjoint_left.1 hR'disj h
              (Finset.mem_map_of_mem _ (Finset.mem_image_of_mem _ hf₂))
          · rw [hx] at h
            obtain ⟨y, hy, hyx⟩ := Finset.mem_map.1 h
            obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hy
            have := (liftArc P U').injective hyx
            simp only [arcImage, Prod.mk.injEq] at this
            exact hf₂L (hinj e' (hLY he') f₂ hf₂ this.1 this.2 ▸ he')
      -- Q' D
      · exfalso
        rcases t₂ with t₂ | t₂ <;> (rw [tag_arcE] at t₂; simp at t₂)
      -- Q' Q'
      · have hx : x₁ = x₂ := arcE.injective h₂x.symm
        subst hx
        by_contra hne
        have hne' : q₁' ≠ q₂' := fun h => hne (by rw [h])
        exact Finset.disjoint_left.1 (hQ'disj hq₁' hq₂' hne') hx₁ hx₂
    intro q₁ hq₁ q₂ hq₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a h₁ h₂
    exact hne (hcls_eq (hclass q₁ hq₁ a h₁) (hclass q₂ hq₂ a h₂))
  · -- coverage
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff, id_eq,
      resv, R1]
    constructor
    · rintro ⟨q, ((⟨e, he, rfl⟩ | ⟨f, ⟨hf, -⟩, rfl⟩) | ⟨e, he, rfl⟩) | ⟨q', hq', rfl⟩, ha⟩
      · simp only [Tcyc, Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact Or.inr (mem_liftArc_iff.2 ⟨e, he, rfl⟩)
        · exact Or.inl (Or.inl ⟨e, hLY he, (mem_Ccyc p).2 (Or.inl ha)⟩)
      · exact Or.inl (Or.inl ⟨f, hf, ha⟩)
      · simp only [Dcyc, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact Or.inl (Or.inl ⟨e, hLY he, (mem_Ccyc p).2 (Or.inr (Or.inr (Or.inr ha)))⟩)
        · exact Or.inl (Or.inl ⟨β e, hLY (hβ e he).1, (mem_Ccyc p).2 (Or.inr (Or.inl ha))⟩)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
        have hmem : x ∈ R' ∪ (L.image (arcImage p)).map (liftArc P U') := by
          rw [← hQ'cov]; exact Finset.mem_biUnion.2 ⟨q', hq', hx⟩
        rcases Finset.mem_union.1 hmem with h | h
        · exact Or.inl (Or.inr (Finset.mem_map_of_mem _ h))
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 h
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
          refine Or.inl (Or.inl ⟨e, hLY he, (mem_Ccyc p).2 (Or.inr (Or.inr (Or.inl ?_)))⟩)
          rw [QA_eq_arcE]; exact Finset.mem_singleton_self _
    · rintro ((⟨f, hf, haf⟩ | ha) | ha)
      · by_cases hfL : f ∈ L
        · rcases (mem_Ccyc p).1 haf with h | h | h | h
          · exact ⟨Tcyc f, Or.inl (Or.inl (Or.inl ⟨f, hfL, rfl⟩)), Finset.mem_insert_of_mem h⟩
          · obtain ⟨e, he, rfl⟩ := hβsurj f hfL
            exact ⟨Dcyc p e (β e), Or.inl (Or.inr ⟨e, he, rfl⟩), Finset.mem_union_right _ h⟩
          · rw [QA_eq_arcE, Finset.mem_singleton] at h
            subst h
            have hmem : liftArc P U' (arcImage p f) ∈ Q'.biUnion id := by
              rw [hQ'cov]
              exact Finset.mem_union_right _
                (Finset.mem_map_of_mem _ (Finset.mem_image_of_mem _ hfL))
            obtain ⟨q', hq', hx⟩ := Finset.mem_biUnion.1 hmem
            exact ⟨q'.map arcE, Or.inr ⟨q', hq', rfl⟩, Finset.mem_map_of_mem _ hx⟩
          · exact ⟨Dcyc p f (β f), Or.inl (Or.inr ⟨f, hfL, rfl⟩), Finset.mem_union_left _ h⟩
        · exact ⟨Ccyc p f, Or.inl (Or.inl (Or.inr ⟨f, ⟨hf, hfL⟩, rfl⟩)), haf⟩
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
        have hmem : x ∈ Q'.biUnion id := by rw [hQ'cov]; exact Finset.mem_union_left _ hx
        obtain ⟨q', hq', hxq⟩ := Finset.mem_biUnion.1 hmem
        exact ⟨q'.map arcE, Or.inr ⟨q', hq', rfl⟩, Finset.mem_map_of_mem _ hxq⟩
      · obtain ⟨e, he, rfl⟩ := mem_liftArc_iff.1 ha
        exact ⟨Tcyc e, Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩)), Finset.mem_insert_self _ _⟩

end Partition

end DenseRed

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
