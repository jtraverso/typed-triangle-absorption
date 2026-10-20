/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Universal
public import PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Inverse
public import PartitionedTriangleAbsorption.BlowupB.KeevashPerm
public import PartitionedTriangleAbsorption.BlowupB.KeevashPaddedMain

@[expose] public section

/-!
# The padded Keevash statement for `Ftriv` and its relabellings

* `completeInverseCert_Ftriv`: the bounded signed inverse on the complete allowed blowup;
* `keevashPaddedSpec_Ftriv`: `PaddedInputs.KeevashPaddedSpec Ftriv`, from
  `PaddedGeneral.keevashPaddedSpec_of_certs`;
* `keevashPaddedSpec_perm_Ftriv`: the same for every relabelling `permFam σ Ftriv`;
* `teoremaB_Ftriv`, `teoremaB_perm_Ftriv`: Theorem B in the weighted form of
  `teoremaB_of_keevash`. (`teoremaB_balanced` does not apply: `Ftriv` has no balanced
  weights, `not_balancedWeights_Ftriv`.)

Nothing here is assumed: no Keevash hypothesis, no certificate hypothesis.
-/

noncomputable section

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_complete_inverse_Ftriv (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p Ftriv g) (hg : ∀ a b, |g a b| ≤ ε) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p Ftriv w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    exact (mul_pos_iff_of_pos_left hγ).mp (lt_of_lt_of_le (by norm_num) hlarge)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hε1 : 0 ≤ 33 * ε / γ ^ 3 := by positivity
  have hε2 : 0 ≤ 9537 * ε / γ ^ 5 := by positivity
  have hm (i : Fin 4) : classSize p i ≠ 0 := by have := hmin i; linarith
  have hm1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hmin i; linarith
  have hm2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hmin i; linarith
  obtain ⟨hstep1, hstep2, hbudget⟩ := complete_inverse_budgets ε γ n hε hγ hγ1 hn
  have he0 : 32 * (ε * n ^ 2) / (γ * n) ^ 3 = 32 * ε / (γ ^ 3 * n) := by
    field_simp [hγ0, hn0]
  have he1 : 288 * (n * (33 * ε / γ ^ 3)) / (γ * n) ^ 2 =
      9504 * ε / (γ ^ 5 * n) := by
    field_simp [hγ0, hn0]
    ring
  have he2 : 96 * (9537 * ε / γ ^ 5) / (γ * n) = 915552 * ε / (γ ^ 6 * n) := by
    field_simp [hγ0, hn0]
    ring
  have hstage : ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p Ftriv w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p Ftriv g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_Ftriv p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨trivVertexWeight p d, trivVertexWeight_symmetric p d,
        trivVertexWeight_supported p d, trivVertexWeight_rows p d hz hds hm hm1 hm2, ?_⟩
      intro a b c
      exact he1 ▸ trivVertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨trivZeroRowWeight p f, trivZeroRowWeight_symmetric p f hf,
        trivZeroRowWeight_supported p f, trivZeroRowWeight_load p f hf hr hfd hfs hm, ?_⟩
      intro a b c
      exact he2 ▸ trivZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

theorem exists_complete_chain_inverse_Ftriv (p : V → Fin 4) (r : Sym2 V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hs : Sym2DemandSupported p Ftriv r) (hr : ∀ e, |r e| ≤ ε) :
    ∃ z : TriangleChain V, CopySupported p Ftriv (activeCompleteGraph p Ftriv) z ∧
      boundary z = r ∧
      ∀ T, |z T| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_inverse_Ftriv p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hs.edgeSupported
    (fun a b => hr s(a, b))
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p Ftriv w hsw htw _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p Ftriv (activeCompleteGraph p Ftriv) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p Ftriv (activeCompleteGraph p Ftriv) z,
    copyRestriction_supported p Ftriv (activeCompleteGraph p Ftriv) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p Ftriv (activeCompleteGraph p Ftriv) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p Ftriv (activeCompleteGraph p Ftriv) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

/-- **Certificate 2 for `Ftriv`**: the bounded signed inverse on the complete allowed blowup.
The span hypothesis is not needed (the type edge vectors of `Ftriv` span all class totals). -/
theorem completeInverseCert_Ftriv : PaddedGeneral.CompleteInverseCert Ftriv :=
  fun _ _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr _ =>
    exists_complete_chain_inverse_Ftriv p r ε γ hε hγ hγ1 hlarge hmin hs hr

/-- **The padded Keevash statement for `Ftriv`**, unconditional. -/
theorem keevashPaddedSpec_Ftriv : PaddedInputs.KeevashPaddedSpec Ftriv :=
  PaddedGeneral.keevashPaddedSpec_of_certs Ftriv familyFacts_Ftriv universalCert_Ftriv
    completeInverseCert_Ftriv

/-- **The padded Keevash statement for every relabelling of `Ftriv`**, unconditional. -/
theorem keevashPaddedSpec_perm_Ftriv (σ : Equiv.Perm (Fin 4)) :
    PaddedInputs.KeevashPaddedSpec (BlowupB.permFam σ Ftriv) :=
  BlowupB.keevashPaddedSpec_perm σ keevashPaddedSpec_Ftriv

theorem keevashTypedSpec_perm_Ftriv (σ : Equiv.Perm (Fin 4)) :
    BlowupB.KeevashTypedSpec (BlowupB.permFam σ Ftriv) :=
  BlowupB.keevashTypedSpec_of_padded (BlowupB.card_three_perm σ Ftriv_card_three)
    (keevashPaddedSpec_perm_Ftriv σ)

/-- **Theorem B for every relabelling of `Ftriv`**, in the weighted form of
`teoremaB_of_keevash` (class sizes at least `γ n`, weights in `[ω₁, 1/ω₁]` nearly solving the
load equations of the complete blowup with the actual class sizes), unconditional. -/
theorem teoremaB_perm_Ftriv (σ : Equiv.Perm (Fin 4)) (γ ω₁ : ℝ) (hγ : 0 < γ) (hω₁ : 0 < ω₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → BlowupB.AllowedPair (BlowupB.permFam σ Ftriv) (p u) (p v)) →
        (∀ v, BlowupB.missDeg p (BlowupB.permFam σ Ftriv) G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        (∃ wt : Multiset (Fin 4) → ℝ, (∀ τ ∈ BlowupB.permFam σ Ftriv, ω₁ ≤ wt τ ∧ wt τ ≤ 1 / ω₁) ∧
          ∀ a b, BlowupB.AllowedPair (BlowupB.permFam σ Ftriv) a b →
            |(∑ τ ∈ BlowupB.permFam σ Ftriv, wt τ *
              ((∑ c ∈ univ.filter (fun c => c ::ₘ ({a, b} : Multiset (Fin 4)) = τ),
                BlowupB.nPrime (BlowupB.clsz p) {a, b} c) / Fintype.card V)) - 1| ≤ ε) →
        IsIntDiv p (BlowupB.permFam σ Ftriv) G.edgeFinset →
        HasDecomp p (BlowupB.permFam σ Ftriv) G.edgeFinset :=
  BlowupB.teoremaB_of_keevash (keevashTypedSpec_perm_Ftriv σ) γ ω₁ hγ hω₁

#print axioms completeInverseCert_Ftriv
#print axioms keevashPaddedSpec_Ftriv
#print axioms keevashPaddedSpec_perm_Ftriv
#print axioms teoremaB_perm_Ftriv

end PaddedTrivial
