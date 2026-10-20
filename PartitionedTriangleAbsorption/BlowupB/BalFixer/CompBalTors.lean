/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.CompBal
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalComponentTors
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalScalesTors
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.PotQ6

@[expose] public section

/-!
# The flexible component certificate for bipartite links with a torsion layer

`componentCertFlexTL_of_bal_tors`: as `componentCertFlexTL_of_bal`, with a torsion class
`(charge ψ / g0) mod q` (`q ≤ 12`), a value-one template `Tq` and `ψ`-neutral vertex templates; the
numerical choices are those of `tors_scales` (`lamT = Λ0 / n`, `ρT = 2^11 ρ`,
`N = ⌈45 q Λ0⌉`), at every scale `2^L` with `2^46 (30 Cter + 1)(g + 1)(m + 2)(t + 1) ≤ 2^L`.
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

/-- **The flexible component certificate for bipartite links with a torsion layer.** -/
theorem componentCertFlexTL_of_bal_tors (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t)
    (k : Fin t) (hc : CompT.CompLabel F c) (hcard : ∀ τ ∈ F, Multiset.card τ = 3)
    (hwalk : FinT.LocalWalk F c k)
    (σc : Fin t → Fin t → ℤ) (Bc : Finset (Fin t)) (hloc : LocalSol F σc Bc)
    (ψ : Fin t → Fin t → ℤ) (g0 : ℤ) (q : ℕ) (hq : 0 < q) (hq12 : q ≤ 12) (hg0 : 0 < g0)
    (hsol : ∀ u, BalScalarHyp F σc Bc (fun _ _ => 0) u →
      g0 * q ∣ ∑ i, ∑ j, ψ i j * ((if i = j then 2 else 1) * u i j) →
      FinT.CountsInside c k u → ∃ w, FinT.LatEq F u w)
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
    (hψTP : ∀ r ∈ Bc, c r = k → TypedRefinerCharge.charge ψ (TP r).L (TP r).E = 0)
    (hψTM : ∀ r ∈ Bc, c r = k → TypedRefinerCharge.charge ψ (TM r).L (TM r).E = 0)
    (hKm : KillsMod (g0 * q) ψ F)
    (hg0dvd : ∀ {W : Type} [Fintype W] [DecidableEq W] (q' : W → Fin t) (E : Finset (Sym2 W)),
      (∀ e ∈ E, ¬ e.IsDiag) → ActiveEdges F q' E → (∀ e ∈ E, CompT.InsideE q' c k e) →
      (∀ v, Even (incidentLoad E v)) → 3 ∣ E.card → g0 ∣ TypedRefinerCharge.charge ψ q' E)
    (Tq : FinT.Template F c k) (hTq3 : 3 ∣ Tq.E.card)
    (hTqg : g0 ∣ TypedRefinerCharge.charge ψ Tq.L Tq.E)
    (hTqv : (TypedRefinerCharge.charge ψ Tq.L Tq.E / g0) % (q : ℤ) = 1)
    (hm : m + 1 ≤ 2 ^ 21)
    (Cter : ℕ) (hterm : TermHyp F ((168 + 3 * q * 6) + g * (168 + 3 * q * 6)) Cter) (L : ℕ)
    (hL : (2 : ℝ) ^ 46 * ((30 * Cter + 1) * (g + 1) * (m + 2) * (t + 1)) ≤ 2 ^ L) :
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
  have hΛ0' : 0 ≤ 9 * ((q : ℝ) * Λ0 + 4 * q * Λ0) := by
    have := hfl.ω_pos; have := hfl.δ_pos; have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have : 0 ≤ lam := by rw [hlam]; positivity
    have : 0 ≤ Q := by rw [hQ]; positivity
    rw [hΛ0]; positivity
  set N : ℕ := ⌈9 * ((q : ℝ) * Λ0 + 4 * q * Λ0)⌉₊ with hN
  have hN1 : 9 * ((q : ℝ) * Λ0 + 4 * q * Λ0) ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 9 * ((q : ℝ) * Λ0 + 4 * q * Λ0) + 1 := (Nat.ceil_lt_add_one hΛ0').le
  set θ : ℝ := 2 ^ 6 * (g + 1) * N / ω with hθ
  set lamT : ℝ := Λ0 / n with hlamT
  set ρT : ℝ := 2 ^ 11 * ρ with hρT
  have hT := tors_scales L ω δ ρ n hfl g m Cter t q hq hq12 hL lam Q Λ0 θ lamT ρT N rfl rfl rfl
    hN1 hN2 rfl rfl rfl
  have hW : 64 * lam * Fintype.card V ≤ (Fintype.card {v // c (p v) = k} : ℝ) := by
    have hcl := hs.class_card i0
    have hsub : (univ.filter fun w => p w = i0).card ≤ Fintype.card {v // c (p v) = k} := by
      rw [Fintype.card_subtype]
      exact card_le_card (fun w hw => mem_filter.mpr ⟨mem_univ _,
        by rw [(mem_filter.mp hw).2]; exact hi0⟩)
    have hsubR : ((univ.filter fun w => p w = i0).card : ℝ) ≤
        (Fintype.card {v // c (p v) = k} : ℝ) := by exact_mod_cast hsub
    have h1 : 64 * lam * n ≤ ω * n :=
      mul_le_mul_of_nonneg_right hT.lam_ω (Nat.cast_nonneg _)
    linarith
  exact component_bal_walk_tors F c k hc hcard hwalk σc Bc hloc ψ g0 q hq hg0 hsol hkill hσodd hσ1
    TP TM M hM3 hTP hTM hloc3 hψTP hψTM hKm hg0dvd Tq hTq3 hTqg hTqv hm Cter hterm p G ω lam ρ δ Q θ
    lamT ρT N hG hs hT.lam_pos hT.lam_le hT.rho_pos hT.scale hT.n1 hT.n2 hT.δ_pos hT.Q_pos
    hT.θ_pos hW hT.path hT.γ1 hT.lamT_pos hT.lamT_ω hT.ρT_pos hT.scT hT.nT hT.d6 hT.cT hT.NΛ
    hT.bud hT.embed hT.deg hT.count X hXG hX hXin

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.componentCertFlexTL_of_bal_tors
