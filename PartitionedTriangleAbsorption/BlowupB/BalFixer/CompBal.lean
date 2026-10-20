/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.CompL
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.Pot3

@[expose] public section

/-!
# The flexible component certificate for bipartite links

`componentCertFlexTL_of_bal`: a component with the lattice data (`LocalSol`, the scalar solution, the
side weights), rooted templates, the `3 ∣ |E|` mechanism (`M = 3` with templates of size `≡ 0 (mod 3)`,
or `M = 1` with a local potential) and a terminal of size `Cter` has the component certificate at
every scale `2^L` with `2^40 (30 Cter + 1)(g + 1)(m + 2)(t + 1) ≤ 2^L`. The numerical choices are
those of `bal_scales`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.VertexSplit
open PaddedGeneral.RealInverse

variable {t : ℕ}

theorem hasDecomp_empty_t' {V : Type*} [DecidableEq V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) : HasDecomp p F (∅ : Finset (Sym2 V)) :=
  ⟨∅, fun s hs => absurd hs (by simp), by simp, by simp⟩

/-- **The flexible component certificate for bipartite links.** -/
theorem componentCertFlexTL_of_bal (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hwalk : FinT.LocalWalk F c k)
    (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t)) (hloc : LocalSol F σc Bc)
    (hsol : ∀ u, BalScalarHyp F σc Bc (fun _ _ => 0) u → FinT.CountsInside c k u →
      ∃ w, FinT.LatEq F u w)
    (hkill : ∀ r ∈ Bc, ∀ τ ∈ F, r ∈ τ → ∑ i, σc r i * typeDegVec τ r i = 0)
    (hσodd : ∀ r ∈ Bc, ∀ j, (∃ l, Link F r j l) → Odd (σc r j))
    (hσ1 : ∀ r j, |σc r j| ≤ 1)
    {m g : ℕ} (TP TM : Fin t → RootedTemplate t m g)
    (M : ℕ) (hM3 : M ∣ 3)
    (hTP : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TP r) 2 M)
    (hTM : ∀ r ∈ Bc, c r = k → BalTemplate (fun i j => ∃ l, Link F i j l) c k σc r (TM r) (-2) M)
    (hloc3 : ∀ {W : Type} [Fintype W] [DecidableEq W] (q : W → Fin t) (E : Finset (Sym2 W)),
      (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F q E → (∀ e ∈ E, CompT.InsideE q c k e) →
      (∀ v, Even (incidentLoad E v)) → (∀ v, q v ∈ Bc → vcharge (σc (q v)) q v E = 0) →
      M ∣ E.card → 3 ∣ E.card)
    (hm : m + 1 ≤ 2 ^ 21)
    (Cter : ℕ) (hterm : TermHyp F (168 + g * 168) Cter) (L : ℕ)
    (hL : (2 : ℝ) ^ 40 * ((30 * Cter + 1) * (g + 1) * (m + 2) * (t + 1)) ≤ 2 ^ L) :
    ComponentCertFlexTL F c k L := by
  intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hX hXin
  classical
  by_cases hne : ∃ i, c i = k
  swap
  · -- an empty component
    push Not at hne
    have hX0 : X = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | _ a b => exact hne _ ((CompT.insideE_mk p c k a b).mp (hXin _ he)).1
    subst hX0
    have hD0 : (0 : ℝ) ≤ 2 * δ * Fintype.card V := by
      have := hfl.δ_pos; positivity
    refine ⟨∅, empty_subset _, disjoint_empty_left _, by simp, hasDecomp_empty_t' _ _,
      fun v => by simpa [incidentLoad] using hD0, fun L hL _ => ?_⟩
    rw [subset_empty.mp hL, empty_union]
    exact hasDecomp_empty_t' _ _
  obtain ⟨i0, hi0⟩ := hne
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set lam : ℝ := ω ^ 2 * δ / 2 ^ L with hlam
  set Q : ℝ := 2 ^ 15 * lam * n / ω with hQ
  set Λ0 : ℝ := 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hΛ0
  have hΛ0' : 0 ≤ 9 * Λ0 := by
    have := hfl.ω_pos; have := hfl.δ_pos; have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have : 0 ≤ lam := by rw [hlam]; positivity
    have : 0 ≤ Q := by rw [hQ]; positivity
    rw [hΛ0]; positivity
  set N : ℕ := ⌈9 * Λ0⌉₊ with hN
  have hN1 : 9 * Λ0 ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 9 * Λ0 + 1 := (Nat.ceil_lt_add_one hΛ0').le
  set θ : ℝ := 2 ^ 6 * (g + 1) * N / ω with hθ
  have hB := bal_scales L ω δ ρ n hfl g m Cter t hL lam Q Λ0 θ N rfl rfl rfl hN1 hN2 rfl
  have hW : 64 * lam * Fintype.card V ≤ (Fintype.card {v // c (p v) = k} : ℝ) := by
    have hcl := hs.class_card i0
    have hsub : (univ.filter fun w => p w = i0).card ≤ Fintype.card {v // c (p v) = k} := by
      rw [Fintype.card_subtype]
      exact card_le_card (fun w hw => mem_filter.mpr ⟨mem_univ _,
        by rw [(mem_filter.mp hw).2]; exact hi0⟩)
    have hsubR : ((univ.filter fun w => p w = i0).card : ℝ) ≤
        (Fintype.card {v // c (p v) = k} : ℝ) := by exact_mod_cast hsub
    have h1 : 64 * lam * n ≤ ω * n :=
      mul_le_mul_of_nonneg_right hB.lam_ω (Nat.cast_nonneg _)
    linarith
  exact component_bal_walk F c k hc hcard hwalk σc Bc hloc hsol hkill hσodd hσ1 TP TM M hM3 hTP
    hTM hloc3 hm Cter hterm p G ω lam ρ δ Q θ N hG hs hB.lam_pos hB.lam_le hB.rho_pos hB.scale
    hB.n1 hB.n2 hB.δ_pos hB.Q_pos hB.θ_pos hW hB.path hN1 hB.bud hB.embed hB.deg hB.count
    X hXG hX hXin

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.componentCertFlexTL_of_bal
