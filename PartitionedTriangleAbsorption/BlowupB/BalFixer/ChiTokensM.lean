/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.ChiTokens
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.GuardedTemplatesM

@[expose] public section

/-!
# Balanced charge tokens from templates on `Fin (m + 1)` (`m + 1 ≤ 12`)

`TemplateM` is `FinT.Template` with `m + 1` positions; `host_chi_tokens_m` is `host_chi_tokens` for such
templates, through `guarded_template_family_scaled_m` (ledger degree `≤ 12 λ |V|`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.VertexSplit
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse

variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A template on `Fin (m + 1)`: loopless, allowed, even, at most `m + 1` edges, inside component `k`. -/
structure TemplateM (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t) (m : ℕ) where
  E : Finset (Sym2 (Fin (m + 1)))
  L : Fin (m + 1) → Fin t
  loop : ∀ e ∈ E, ¬ e.IsDiag
  act : ActiveEdges F L E
  even : ∀ w, Even (incidentLoad E w)
  card : E.card ≤ m + 1
  inside : ∀ w, c (L w) = k

/-- **Balanced charge tokens from templates on `Fin (m + 1)`.** -/
theorem host_chi_tokens_m {κ : Type*} (m : ℕ) (hm : m + 1 ≤ 12)
    (F : Finset (Multiset (Fin t))) (χ : Fin t → Fin t → ℤ)
    (c : Fin t → Fin t) (k : Fin t) (Tp Tm : TemplateM F c k m) (u : ℤ)
    (hplusCharge : charge χ Tp.L Tp.E = u) (hminusCharge : charge χ Tm.L Tm.E = -u)
    (σc : Fin t → Fin t → ℤ)
    (hbalP : ∀ j, vcharge (σc (Tp.L j)) Tp.L j Tp.E = 0)
    (hbalM : ∀ j, vcharge (σc (Tm.L j)) Tm.L j Tm.E = 0)
    (M : ℕ) (hMP : M ∣ Tp.E.card) (hMM : M ∣ Tm.E.card)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Tok κ)) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (m + 1) (ω * Fintype.card V))
    (hB : DegBounded B (12 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : Tok κ → Finset (Sym2 V), TokReal χ (fun _ _ => 0) p u (m + 1) B S tok ∧
      (∀ τ ∈ S, tok τ ⊆ G.edgeFinset) ∧
      (∀ v, ((∑ τ ∈ S, incidentLoad (tok τ) v : ℕ) : ℝ) ≤ lam * Fintype.card V) ∧
      (∀ τ ∈ S, ∀ e ∈ tok τ, CompT.InsideE p c k e) ∧
      (∀ τ ∈ S, ∀ y, vcharge (σc (p y)) p y (tok τ) = 0) ∧
      (∀ τ ∈ S, M ∣ (tok τ).card) := by
  classical
  let E : Tok κ → Finset (Sym2 (Fin (m + 1))) := fun τ => if τ.sign then Tp.E else Tm.E
  let label : Tok κ → Fin (m + 1) → Fin t := fun τ => if τ.sign then Tp.L else Tm.L
  have hdata (τ : Tok κ) : (∀ e ∈ E τ, ¬ e.IsDiag) ∧ ActiveEdges F (label τ) (E τ) ∧
      (∀ w, Even (incidentLoad (E τ) w)) ∧ (E τ).card ≤ m + 1 ∧
      charge χ (label τ) (E τ) = (if τ.sign then u else -u) ∧
      (∀ j, vcharge (σc (label τ j)) (label τ) j (E τ) = 0) ∧ M ∣ (E τ).card ∧
      ∀ w, c (label τ w) = k := by
    by_cases hτ : τ.sign = true
    · simp only [E, label, hτ, ite_true]
      exact ⟨Tp.loop, Tp.act, Tp.even, Tp.card, hplusCharge, hbalP, hMP, Tp.inside⟩
    · simp only [E, label, hτ]
      exact ⟨Tm.loop, Tm.act, Tm.even, Tm.card, hminusCharge, hbalM, hMM, Tm.inside⟩
  obtain ⟨f, hf, hload⟩ := GuardedTemplatesM.guarded_template_family_scaled_m (m + 1) hm p G (fun i j => ∃ k, Link F i j k)
    S E label (fun τ _ => (hdata τ).1) (fun τ _ => (hdata τ).2.1)
    (fun τ _ => (hdata τ).2.2.2.1) ω lam rho hs B hB hω hlam hlamω hrho hscale hn1 hcount
  let tok := fun τ => GuardedTemplatesM.mappedN (E τ) (f τ)
  have hloopT : ∀ τ ∈ S, ∀ e ∈ tok τ, ¬ e.IsDiag := fun τ hτ =>
    PaddedF12.loopless_image (f τ) (hf.injective τ hτ) (E τ) (hdata τ).1
  refine ⟨tok, ⟨hf.disjoint, hf.avoid, hloopT, ?_, ?_, ?_, ?_⟩, hf.subgraph, hload, ?_, ?_, ?_⟩
  · intro τ hτ
    exact PaddedF12.even_image (f τ) (hf.injective τ hτ) (E τ) (hdata τ).2.2.1
  · intro τ hτ
    change charge χ p ((E τ).image (Sym2.map (f τ))) = _
    rw [PaddedF12.charge_image (f τ) (hf.injective τ hτ) p (label τ) (hf.labels τ hτ)]
    exact (hdata τ).2.2.2.2.1
  · intro τ _
    simp [charge, pair]
  · intro τ hτ
    exact card_image_le.trans (hdata τ).2.2.2.1
  · intro τ hτ e he
    obtain ⟨e0, -, rfl⟩ := Finset.mem_image.mp he
    induction e0 using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, CompT.insideE_mk, hf.labels τ hτ x, hf.labels τ hτ y]
      exact ⟨(hdata τ).2.2.2.2.2.2.2 x, (hdata τ).2.2.2.2.2.2.2 y⟩
  · intro τ hτ y
    have hinj := hf.injective τ hτ
    have hl := hf.labels τ hτ
    rw [← vcharge_eq_charge _ p y _ (hloopT τ hτ)]
    by_cases hy : ∃ j, f τ j = y
    · obtain ⟨j, rfl⟩ := hy
      change charge (chiV (σc (p (f τ j)))) (relab p (f τ j)) ((E τ).image (Sym2.map (f τ))) = 0
      rw [PaddedF12.charge_image (f τ) hinj (relab p (f τ j)) (relab (label τ) j)
        (relab_comp_of_injective (m := m) p (label τ) (f τ) hinj hl j), hl j,
        vcharge_eq_charge _ _ _ _ (hdata τ).1]
      exact (hdata τ).2.2.2.2.2.1 j
    · push Not at hy
      change charge (chiV (σc (p y))) (relab p y) ((E τ).image (Sym2.map (f τ))) = 0
      rw [PaddedF12.charge_image (f τ) hinj (relab p y) (fun k => (label τ k).castSucc)
        (relab_comp_of_not_mem (m := m) p (label τ) (f τ) hl y hy)]
      exact charge_chiV_castSucc _ _ _
  · intro τ hτ
    change M ∣ ((E τ).image (Sym2.map (f τ))).card
    rw [card_image_of_injective _ (Sym2.map.injective (hf.injective τ hτ))]
    exact (hdata τ).2.2.2.2.2.2.1

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.host_chi_tokens_m
