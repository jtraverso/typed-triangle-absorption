/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseAssemblyBounds

@[expose] public section

/-! The dense-to-mesoscopic construction has a stronger estimate on its original
vertices than its global square-root estimate. This estimate requires no inhabitant
of DenseRefiner: it holds for every hub catalogue, since that catalogue avoids old
vertices. It is a local construction bound, not a physical embedding theorem. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseRed

open Finset
open MesoCutHub (dPairs deg_union_le sum_image_le' sum_union_le'
  sum_filter_prod_fst_le sum_filter_prod_snd_le outDeg_le_of_maxDeg inDeg_le_of_maxDeg)

variable {V P U' : Type} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
  [Fintype U'] [DecidableEq U']

/-- Old vertices incur only their own input degree, even if many old vertices will
later be identified with the same physical root. -/
theorem catalogLoad_old_le (p : V → P) (c : V → ZMod 3) (Y : Finset (V × V))
    (hY : IsCyc c Y) (hdeg : MaxDegLE Y 17)
    (hcross : ∀ e ∈ Y, p e.1 ≠ p e.2)
    (lib' : Finset (Finset ((P ⊕ U') × (P ⊕ U')))) (v : V) :
    catalogLoad (libT p Y lib') (old v) ≤ 73 * deg Y v := by
  classical
  let w : TV V P U' := old v
  let S := ∑ e ∈ Y, deg (Ccyc (U' := U') p e) w
  have hS : S ≤ 2 * deg Y v := by
    have hc : (Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e))).card ≤ deg Y v := by
      have hs : Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e)) ⊆
          Y.filter (fun e => e.2 = v) ∪ Y.filter (fun e => e.1 = v) := by
        intro e he
        obtain ⟨he, hw⟩ := Finset.mem_filter.1 he
        rcases mem_range_f9 p hw with h | h | h | h | ⟨k, h⟩ <;>
          simp [w, old, hub, pv] at h
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, h.symm⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h.symm⟩)
      exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    have heq : S = 2 * (Y.filter (fun e => w ∈ Set.range (f9 (U' := U') p e))).card := by
      change (∑ e ∈ Y, deg (Ccyc (U' := U') p e) w) = _
      calc
        _ = ∑ e ∈ Y, (if w ∈ Set.range (f9 (U' := U') p e) then 2 else 0) :=
          Finset.sum_congr rfl fun e he =>
            deg_Ccyc_eq p (Hub.ne_of_cyc c (hY e he)) (hcross e he) w
        _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [heq]
    exact Nat.mul_le_mul_left _ hc
  have hT : ∑ q ∈ Y.image (Tcyc (P := P) (U' := U')), deg q w ≤ S + deg Y v := by
    refine (sum_image_le' _ _ _).trans ?_
    have hh := Finset.sum_le_sum (fun e (_ : e ∈ Y) => deg_Tcyc_le' p e w)
    rw [Finset.sum_add_distrib, sum_deg_single_lift'] at hh
    simpa [S, w, old, deg, inDeg_map_liftArc, outDeg_map_liftArc] using hh
  have hC : ∑ q ∈ Y.image (Ccyc (U' := U') p), deg q w ≤ S := sum_image_le' _ _ _
  have hDp : ∑ q ∈ (dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2),
      deg q w ≤ 34 * S := by
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
  have hHub : ∑ q ∈ lib'.image (fun q' => q'.map (arcE (V := V))), deg q w = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨q', _, rfl⟩ := Finset.mem_image.1 hq
    apply deg_map_arcE_of_not_range
    rintro (a | u) h <;> simp [ι, w, old, hub, ext] at h
  change (∑ q ∈ libT p Y lib', deg q w) ≤ 73 * deg Y v
  unfold libT
  have u1 := sum_union_le' (Y.image Tcyc ∪ Y.image (Ccyc (U' := U') p) ∪
    (dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2))
    (lib'.image (fun q' => q'.map (arcE (V := V)))) (fun q => deg q w)
  have u2 := sum_union_le' (Y.image Tcyc ∪ Y.image (Ccyc (U' := U') p))
    ((dPairs Y).image (fun ef => Dcyc (U' := U') p ef.1 ef.2)) (fun q => deg q w)
  have u3 := sum_union_le' (Y.image (Tcyc (P := P) (U' := U')))
    (Y.image (Ccyc (U' := U') p)) (fun q => deg q w)
  change _ ≤ 73 * deg Y v
  omega

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseRed
