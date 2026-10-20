/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEmbeddingBudget

@[expose] public section

/-! Scalar consequences of the concrete catalogue bounds. The root witness
supplies the mass, squared new-vertex loads and old-vertex cap used here. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueScaleBudget

theorem vertex_load (C q t n x load : ℝ) (hC : 0 ≤ C)
    (ht : 0 < t) (ht1 : t ≤ 1) (hn : 0 < n) (hsize : 1 ≤ t ^ 2 * n)
    (hx : x ≤ t ^ 2 * n ^ 2) (_hl : 0 ≤ load)
    (hq : 1257 + 14 * C ≤ q)
    (hload : load ≤ 1257 ∨ load ^ 2 ≤ C ^ 2 * (49 * x)) :
    load ≤ q * t * n := by
  have htn : 1 ≤ t * n := by
    have hsq : t ^ 2 ≤ t := by nlinarith
    exact hsize.trans (mul_le_mul_of_nonneg_right hsq hn.le)
  have hq0 : 0 ≤ q := by linarith
  rcases hload with hold | hnew
  · have hh := mul_le_mul_of_nonneg_left htn hq0
    nlinarith
  · have hbound : load ^ 2 ≤ (7 * C * t * n) ^ 2 := by
      calc load ^ 2 ≤ C ^ 2 * (49 * x) := hnew
        _ ≤ C ^ 2 * (49 * (t ^ 2 * n ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 49)) (sq_nonneg C)
        _ = _ := by ring
    have hnonneg : 0 ≤ 7 * C * t * n := by positivity
    have hroot : load ≤ 7 * C * t * n := by nlinarith
    have hcoeff : 7 * C ≤ q := by linarith
    exact hroot.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoeff (mul_pos ht hn).le])

theorem mass (C q t n x total : ℝ) (hC : 0 ≤ C) (hx : x ≤ t ^ 2 * n ^ 2)
    (hq : 1960 * C + 96 ≤ q) (hmass : total ≤ (1960 * C + 96) * x) :
    total ≤ q * t ^ 2 * n ^ 2 := by
  calc total ≤ (1960 * C + 96) * x := hmass
    _ ≤ (1960 * C + 96) * (t ^ 2 * n ^ 2) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ q * (t ^ 2 * n ^ 2) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

theorem anchor_budget (a d T W M : ℝ) (hd : 0 ≤ d) (hT : 0 < T)
    (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hbudget : 4 * M / T + 4 + 2 * (d + T + 2 * W) < a) : M < a * T := by
  have hdiv : 0 ≤ M / T := div_nonneg hM hT.le
  have hrest : 0 ≤ 4 + 2 * (d + T + 2 * W) := by positivity
  have hb : 4 * (M / T) + 4 + 2 * (d + T + 2 * W) < a := by
    simpa only [mul_div_assoc] using hbudget
  have hMa : M / T < a := by linarith
  exact (div_lt_iff₀ hT).mp hMa

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueScaleBudget

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueScaleBudget.vertex_load
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueScaleBudget.mass
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueScaleBudget.anchor_budget
