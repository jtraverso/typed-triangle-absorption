/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.UniversalFamilies

@[expose] public section

/-!
# Framework for the complete signed inverse of the six base families

`TernaryInverse F` is the ternary form of the bounded signed inverse (symmetric ternary weights
supported on `F`-admissible triples, with load equal to any bounded `F`-supported symmetric demand
and every weight at most `2^20 ε/(γ^6 n)`). It needs no compatibility condition: the six base
families have type vectors spanning all allowed class-pair coordinates.

`completeInverseCert_of_ternary` turns it into `CompleteInverseCert F` for every `F ⊇ F0` with the
same allowed pairs (the copy step of the F* / Fbit certificates).

`lc d a₀ a₁ a₂ a₃` is a linear combination of the four row demands of a vertex; it is used as the
input of the vertex modes.
-/

noncomputable section

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedF12 PaddedGeneral

/-- The ternary bounded signed inverse for `F` (no compatibility condition). -/
def TernaryInverse (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ),
    0 ≤ ε → 0 < γ → γ ≤ 1 → 4 ≤ γ * (Fintype.card V : ℝ) →
    (∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i) →
    (∀ a b, g a b = g b a) → (∀ a, g a a = 0) → EdgeSupported p F g →
    (∀ a b, |g a b| ≤ ε) →
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ))

/-- **The complete inverse certificate from a ternary inverse of a base with the same allowed
pairs.** -/
theorem completeInverseCert_of_ternary {F0 F : Finset (Multiset (Fin 4))} (hsub : F0 ⊆ F)
    (hallow : ∀ i j : Fin 4, (∃ k, Link F i j k) ↔ (∃ k, Link F0 i j k))
    (hT : TernaryInverse F0) : CompleteInverseCert F := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _
  have hsE : EdgeSupported p F0 (fun a b => r s(a, b)) := by
    intro a b hab
    exact hs.edgeSupported a b (fun h => hab ((hallow _ _).mp h))
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := hT V p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hsE
    (fun a b => hr s(a, b))
  have htwF : TernarySupported p F w := by
    intro a b c hna
    exact htw a b c fun h => hna ⟨h.1, h.2.1, h.2.2.1, hsub h.2.2.2⟩
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p F w hsw htwF _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p F (activeCompleteGraph p F) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p F (activeCompleteGraph p F) z,
    copyRestriction_supported p F (activeCompleteGraph p F) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p F (activeCompleteGraph p F) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p F (activeCompleteGraph p F) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A linear combination of the four row demands of a vertex. -/
def lc (d : V → Fin 4 → ℝ) (a0 a1 a2 a3 : ℝ) (v : V) : ℝ :=
  a0 * d v 0 + a1 * d v 1 + a2 * d v 2 + a3 * d v 3

theorem lc_sum_zero (p : V → Fin 4) (d : V → Fin 4 → ℝ) (hz : VertexDemandZero p d)
    (a0 a1 a2 a3 : ℝ) (i : Fin 4) :
    ∑ v ∈ classVertices p i, lc d a0 a1 a2 a3 v = 0 := by
  simp only [lc, sum_add_distrib, ← mul_sum]
  rw [hz i 0, hz i 1, hz i 2, hz i 3]
  ring

theorem lc_bound (d : V → Fin 4 → ℝ) (D : ℝ) (hd : ∀ a j, |d a j| ≤ D)
    (a0 a1 a2 a3 : ℝ) (v : V) :
    |lc d a0 a1 a2 a3 v| ≤ (|a0| + |a1| + |a2| + |a3|) * D := by
  unfold lc
  have h0 := abs_mul a0 (d v 0)
  have h1 := abs_mul a1 (d v 1)
  have h2 := abs_mul a2 (d v 2)
  have h3 := abs_mul a3 (d v 3)
  have m0 := mul_le_mul_of_nonneg_left (hd v 0) (abs_nonneg a0)
  have m1 := mul_le_mul_of_nonneg_left (hd v 1) (abs_nonneg a1)
  have m2 := mul_le_mul_of_nonneg_left (hd v 2) (abs_nonneg a2)
  have m3 := mul_le_mul_of_nonneg_left (hd v 3) (abs_nonneg a3)
  calc |a0 * d v 0 + a1 * d v 1 + a2 * d v 2 + a3 * d v 3|
      ≤ |a0 * d v 0| + |a1 * d v 1| + |a2 * d v 2| + |a3 * d v 3| := by
        have := abs_add_le (a0 * d v 0 + a1 * d v 1 + a2 * d v 2) (a3 * d v 3)
        have := abs_add_le (a0 * d v 0 + a1 * d v 1) (a2 * d v 2)
        have := abs_add_le (a0 * d v 0) (a1 * d v 1)
        linarith
    _ ≤ _ := by rw [h0, h1, h2, h3]; linarith

/-- The vertex-mode input bound used by every base family: coefficients of total size `≤ 2`. -/
theorem lc_bound_two (d : V → Fin 4 → ℝ) (D : ℝ) (hD : 0 ≤ D) (hd : ∀ a j, |d a j| ≤ D)
    (a0 a1 a2 a3 : ℝ) (ha : |a0| + |a1| + |a2| + |a3| ≤ 2) (v : V) :
    |lc d a0 a1 a2 a3 v| ≤ 2 * D :=
  (lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right ha hD)

end PaddedNoCommon
