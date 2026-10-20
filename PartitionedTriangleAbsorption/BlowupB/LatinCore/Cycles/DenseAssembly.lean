/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseOldLoad
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.RootedMesoscopicSpec

@[expose] public section

/-!
# Assembly: `DenseRefinerWith C K` and a good partition give the mesoscopic conclusion

`mesoscopicFor_of_dense` checks every clause of the mesoscopic interface for the reserve and
library of `DenseReduction.lean`: colouring, disjointness from `Y`, validity of the pieces,
`|lib| ≤ C' |Y|`, catalogue load `≤ C' √|Y|` (square form), and the exact positive partitions.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace DenseRed

open Hub (ne_of_cyc deg_biUnion)
open MesoCutHub (dPairs deg_mono deg_union_le sum_union_le' sum_image_le'
  sum_filter_prod_fst_le sum_filter_prod_snd_le outDeg_le_of_maxDeg inDeg_le_of_maxDeg
  card_dPairs_le MesoscopicFor load_sq_le)

section Assembly

variable {V P U' : Type} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
  [Fintype U'] [DecidableEq U'] (p : V → P)

/-- The constant of the reduction. -/
def denseConst (C A : ℕ) : ℕ := 19 + C * A + 1241 + (72 + C) * (2 * A)

/-- **Assembly.** -/
theorem rootedMesoscopicFor_of_dense (C K A : ℕ) (hD : DenseRefinerWith C K)
    (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V))
    (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17) (hG : HasGoodPartition A c Y) :
    RootedMesoscopicFor (denseConst C A) (max 9 K) c Y := by
  classical
  obtain ⟨P, hPf, hPd, p, col, hcol, hcross, hinj, hcard, hload⟩ := hG
  set D0 : Finset (P × P) := Y.image (arcImage p) with hD0def
  have hD0 : IsCyc col D0 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
    simp only [arcImage, (hcol e he).1, (hcol e he).2]
    exact hY e he
  obtain ⟨U', hUf, hUd, cU', R', lib', hR'c, hR'd, hlib'v, hlib'card, hlib'load, hpart'⟩ :=
    hD P col D0 hD0
  refine ⟨P ⊕ (((V × V) × Fin 5) ⊕ U'), inferInstance, inferInstance,
    Sum.elim col (Sum.elim (pcol c) cU'), resv p Y R', libT p Y lib', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- colouring
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.1 h
      exact isCyc_Ccyc p c col cU' (hY e he) (hcol e he).1 (hcol e he).2 a hae
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 h
      have := hR'c x hx
      change tcol c col cU' (ι x.2) = tcol c col cU' (ι x.1) + 1
      rw [tcol_ι, tcol_ι]; exact this
  · -- disjoint from `Y`
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, -, rfl⟩ := mem_liftArc_iff.1 hb
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.1 h
      exact old_not_mem_Ccyc p f _ _ hf
    · obtain ⟨x, -, hx⟩ := Finset.mem_map.1 h
      exact old_ne_arcE _ _ x hx
  · -- validity of the pieces
    have hRmem : ∀ e ∈ Y, ∀ {a}, a ∈ Ccyc (U' := U') p e → a ∈ resv p Y R' ∪
        Y.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U'))) :=
      fun e he a ha => Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨e, he, ha⟩))
    intro q hq
    simp only [libT, dPairs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product] at hq
    rcases hq with ((⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨⟨e, f⟩, ⟨⟨he, hf⟩, hef⟩, rfl⟩) |
        ⟨q', hq', rfl⟩
    · obtain ⟨h1, h2⟩ := isDirCycle_T (P := P) (U' := U') (ne_of_cyc c (hY e he))
      refine ⟨h1.1, ?_, h2.trans (le_max_left _ _), h1.2.1⟩
      intro a ha
      simp only [Tcyc, Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · exact Finset.mem_union_right _ (mem_liftArc_iff.2 ⟨e, he, rfl⟩)
      · exact hRmem e he ((mem_Ccyc p).2 (Or.inl ha))
    · obtain ⟨h1, h2⟩ := isDirCycle_C (U' := U') p (ne_of_cyc c (hY e he)) (hcross e he)
      exact ⟨h1.1, fun a ha => hRmem e he ha, h2.trans (le_max_left _ _), h1.2.1⟩
    · obtain ⟨h1, h2⟩ := isDirCycle_D (U' := U') p (e := e) (f := f) hef
      refine ⟨h1.1, ?_, h2.trans (le_max_left _ _), h1.2.1⟩
      intro a ha
      simp only [Dcyc, Finset.mem_union] at ha
      rcases ha with ha | ha
      · exact hRmem e he ((mem_Ccyc p).2 (Or.inr (Or.inr (Or.inr ha))))
      · exact hRmem f hf ((mem_Ccyc p).2 (Or.inr (Or.inl ha)))
    · obtain ⟨hne, hsub, hcardq, hbal⟩ := hlib'v q' hq'
      refine ⟨hne.map, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
        rcases Finset.mem_union.1 (hsub hx) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_map_of_mem _ h))
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 h
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
          refine hRmem e he ((mem_Ccyc p).2 (Or.inr (Or.inr (Or.inl ?_))))
          rw [QA_eq_arcE]; exact Finset.mem_singleton_self _
      · rw [Finset.card_map]; exact hcardq.trans (le_max_right _ _)
      · have hb := balanced_arcImage q' (ι (V := V) (P := P) (U' := U'))
          (fun x _ y _ h => by
            simp only [arcImage, Prod.mk.injEq] at h
            exact Prod.ext (ι_injective h.1) (ι_injective h.2)) hbal
        have heq : q'.image (arcImage (ι (V := V) (P := P) (U' := U'))) = q'.map arcE := by
          rw [Finset.map_eq_image]; rfl
        rw [heq] at hb; exact hb
  · -- library count
    have h1 := Finset.card_union_le (Y.image Tcyc ∪ Y.image (Ccyc p) ∪
      (dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2))
      (lib'.image (fun P' => P'.map (arcE (V := V))))
    have h2 := Finset.card_union_le (Y.image Tcyc ∪ Y.image (Ccyc (U' := U') p))
      ((dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2))
    have h3 := Finset.card_union_le (Y.image (Tcyc (P := P) (U' := U'))) (Y.image (Ccyc (U' := U') p))
    have i1 := Finset.card_image_le (s := Y) (f := Tcyc (P := P) (U' := U'))
    have i2 := Finset.card_image_le (s := Y) (f := Ccyc (U' := U') p)
    have i3 := Finset.card_image_le (s := dPairs Y) (f := fun ef => Dcyc (U' := U') p ef.1 ef.2)
    have i4 := Finset.card_image_le (s := lib') (f := fun P' => P'.map (arcE (V := V)))
    have d1 := card_dPairs_le hdeg
    have hl : lib'.card ≤ C * A * Y.card := by
      calc lib'.card ≤ C * Fintype.card P ^ 2 := hlib'card
        _ ≤ C * (A * Y.card) := Nat.mul_le_mul_left _ hcard
        _ = C * A * Y.card := by ring
    unfold libT denseConst
    nlinarith
  · -- catalogue load
    intro w
    rcases Nat.eq_zero_or_pos Y.card with hm | hm
    · have hY0 : Y = ∅ := Finset.card_eq_zero.1 hm
      have hP0 : Fintype.card P = 0 := by
        have := hcard; rw [hm, mul_zero] at this
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (Nat.le_zero.1 this)
      have hlib0 : lib' = ∅ := by
        have := hlib'card; rw [hP0] at this; simpa using this
      have : libT p Y lib' = ∅ := by simp [libT, dPairs, hY0, hlib0]
      simp [this, catalogLoad, hm]
    · -- bound the four classes
      have hdisjY : ∀ i ∈ Y, ∀ j ∈ Y, i ≠ j → Disjoint (Ccyc (U' := U') p i) (Ccyc p j) :=
        fun i hi j hj hij => Ccyc_disjoint p hij (fun h => hij (hinj i hi j hj h.1 h.2))
      set S := ∑ e ∈ Y, deg (Ccyc (U' := U') p e) w with hS
      have hT : ∑ q ∈ Y.image (Tcyc (P := P) (U' := U')), deg q w ≤ S +
          deg (Y.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U')))) w := by
        refine (sum_image_le' _ _ _).trans ?_
        rw [← sum_deg_single_lift', hS, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun e _ => deg_Tcyc_le' p e w
      have hC : ∑ q ∈ Y.image (Ccyc (U' := U') p), deg q w ≤ S := sum_image_le' _ _ _
      have hDp : ∑ q ∈ (dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2), deg q w ≤
          34 * S := by
        refine (sum_image_le' _ _ _).trans ?_
        refine (Finset.sum_le_sum fun ef _ => deg_Dcyc_le' p ef.1 ef.2 w).trans ?_
        rw [Finset.sum_add_distrib]
        have h1 : ∑ x ∈ dPairs Y, deg (Ccyc (U' := U') p x.1) w ≤ 17 * S :=
          sum_filter_prod_fst_le Y (fun e f => e.2 = f.1)
            (fun e => deg (Ccyc (U' := U') p e) w) 17 fun e _ => by
              simpa [eq_comm] using outDeg_le_of_maxDeg hdeg e.2
        have h2 : ∑ x ∈ dPairs Y, deg (Ccyc (U' := U') p x.2) w ≤ 17 * S :=
          sum_filter_prod_snd_le Y (fun e f => e.2 = f.1)
            (fun e => deg (Ccyc (U' := U') p e) w) 17 fun f _ =>
              inDeg_le_of_maxDeg hdeg f.1
        omega
      have hHub : ∑ q ∈ lib'.image (fun P' => P'.map (arcE (V := V))), deg q w ≤
          C * Fintype.card P := by
        refine (sum_image_le' _ _ _).trans ?_
        by_cases hw : ∃ x, ι x = w
        · obtain ⟨x, rfl⟩ := hw
          simp only [deg_map_arcE]
          exact hlib'load x
        · push_neg at hw
          simp only [deg_map_arcE_of_not_range _ _ hw, Finset.sum_const_zero]
          exact Nat.zero_le _
      -- the basal count
      have hSle : S ≤ 2 * (Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e))).card := by
        rw [hS]
        refine le_of_eq ?_
        calc ∑ e ∈ Y, deg (Ccyc (U' := U') p e) w
            = ∑ e ∈ Y, (if w ∈ Set.range (f9 (U' := U') p e) then 2 else 0) :=
              Finset.sum_congr rfl fun e he =>
                deg_Ccyc_eq p (ne_of_cyc c (hY e he)) (hcross e he) w
          _ = 2 * (Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e))).card := by
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
      obtain ⟨ℓ, hℓ, hcnt⟩ : ∃ ℓ : ℕ, ℓ ^ 2 ≤ A * Y.card ∧
          (Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e))).card ≤ 17 + ℓ := by
        have h := count_basal_le p c hdeg w
        rcases w with v | a | x | u
        · exact ⟨0, by simp, h⟩
        · exact ⟨_, hload a, h⟩
        · exact ⟨0, by simp, h⟩
        · exact ⟨0, by simp, h⟩
      have hYd : deg (Y.map (liftArc V (P ⊕ (((V × V) × Fin 5) ⊕ U')))) w ≤ 17 :=
        maxDegLE_map_liftArc hdeg w
      have hx : catalogLoad (libT p Y lib') w ≤
          1241 + (72 + C) * (ℓ + Fintype.card P) := by
        unfold catalogLoad libT
        have u1 := sum_union_le' (Y.image Tcyc ∪ Y.image (Ccyc (U' := U') p) ∪
          (dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2))
          (lib'.image (fun P' => P'.map (arcE (V := V)))) (fun q => deg q w)
        have u2 := sum_union_le' (Y.image Tcyc ∪ Y.image (Ccyc (U' := U') p))
          ((dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2)) (fun q => deg q w)
        have u3 := sum_union_le' (Y.image (Tcyc (P := P) (U' := U')))
          (Y.image (Ccyc (U' := U') p)) (fun q => deg q w)
        nlinarith
      have hA : A ≤ A ^ 2 := by
        rcases Nat.eq_zero_or_pos A with h | h
        · simp [h]
        · nlinarith
      have ht : (ℓ + Fintype.card P) ^ 2 ≤ (2 * A) ^ 2 * Y.card := by
        have e1 : (ℓ + Fintype.card P) ^ 2 ≤ 2 * ℓ ^ 2 + 2 * Fintype.card P ^ 2 := by
          nlinarith [sq_nonneg ((ℓ : ℤ) - Fintype.card P)]
        have e2 : 2 * ℓ ^ 2 + 2 * Fintype.card P ^ 2 ≤ 4 * A * Y.card := by nlinarith
        have e3 : 4 * A * Y.card ≤ (2 * A) ^ 2 * Y.card := by
          have := Nat.mul_le_mul_right Y.card hA
          nlinarith
        omega
      have hsq := load_sq_le 1241 (72 + C) (2 * A) Y.card (ℓ + Fintype.card P) _ hm ht hx
      refine hsq.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ?_ 2))
      unfold denseConst; omega
  · -- partitions
    intro L hLY hLb
    exact partition_libT p hinj R' lib' hR'd hpart' L hLY hLb

  · -- The same concrete catalogue retains its sharper old-vertex estimate.
    intro v
    exact catalogLoad_old_le p c Y hY hdeg hcross lib' v

/-- Forgetting the old-vertex clause recovers the original interface. -/
theorem mesoscopicFor_of_dense (C K A : ℕ) (hD : DenseRefinerWith C K)
    (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V))
    (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17) (hG : HasGoodPartition A c Y) :
    MesoscopicFor (denseConst C A) (max 9 K) c Y :=
  (rootedMesoscopicFor_of_dense C K A hD V c Y hY hdeg hG).forget

end Assembly

/-- For empty `Y` the mesoscopic conclusion holds trivially. -/
theorem mesoscopicFor_empty (C K : ℕ) (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) :
    MesoscopicFor C K c (∅ : Finset (V × V)) := by
  refine ⟨Empty, inferInstance, inferInstance, Empty.elim, ∅, ∅, by simp [IsCyc], by simp,
    by simp, by simp, by simp [catalogLoad], ?_⟩
  intro L hL _
  have : L = ∅ := Finset.subset_empty.1 hL
  subst this
  exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩

end DenseRed

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
