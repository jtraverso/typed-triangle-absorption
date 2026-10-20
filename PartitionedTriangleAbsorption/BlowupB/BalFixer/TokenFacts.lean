/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.RootedTokens

@[expose] public section

/-!
# Rooted copies are tokens of the vertex layer

For rooted copies `f` of the templates `Tp, Tm` (root `x`), the realized edge sets
`mappedTok f τ = mappedM (tmpl Tp Tm τ).E (f τ)`:
* form a `TokReal` for the vertex charge at `x`, when the templates have signed degree `±2` at their
  root (`tokReal_of_rootedCopies`);
* have zero signed degree at every other vertex, when every non-root template vertex is balanced
  for the side weights of its class (`vcharge_mappedTok_eq_zero`);
* load a vertex `w ≠ x` only if `w ∉ Z`, and then by at most `g` in total (`load_mappedTok_*`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t m g : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {ι : Type*}

/-- The realized token. -/
def mappedTok (Tp Tm : RootedTemplate t m g) (f : Tok ι → Fin (m + 1) → W) (τ : Tok ι) :
    Finset (Sym2 W) :=
  mappedM (tmpl Tp Tm τ).E (f τ)

theorem relab_comp_of_injective (p : W → Fin t) (L : Fin (m + 1) → Fin t) (f : Fin (m + 1) → W)
    (hf : Function.Injective f) (hl : ∀ j, p (f j) = L j) (j : Fin (m + 1)) :
    ∀ k, relab p (f j) (f k) = relab L j k := by
  intro k
  by_cases hk : k = j
  · subst hk; simp [relab]
  · have : f k ≠ f j := fun h => hk (hf h)
    simp [relab, this, hk, hl k]

theorem relab_comp_of_not_mem (p : W → Fin t) (L : Fin (m + 1) → Fin t) (f : Fin (m + 1) → W)
    (hl : ∀ j, p (f j) = L j) (y : W) (hy : ∀ k, f k ≠ y) :
    ∀ k, relab p y (f k) = (L k).castSucc := by
  intro k
  simp [relab, hy k, hl k]

theorem charge_chiV_castSucc {V : Type*} [DecidableEq V] (σ : Fin t → ℤ) (q : V → Fin t)
    (E : Finset (Sym2 V)) : charge (chiV σ) (fun v => (q v).castSucc) E = 0 := by
  rw [charge_eq_sum]
  refine sum_eq_zero fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => rw [pair_pairVec_mk, chiV_castSucc, chiV_castSucc, add_zero]

/-- Signed degree of a realized token at a vertex `y ≠ x`. -/
theorem vcharge_mappedTok_eq_zero (σc : Fin t → Fin t → ℤ) (p : W → Fin t)
    (G : SimpleGraph W) [DecidableRel G.Adj] (B : Finset (Sym2 W)) (Z : Finset W) (x : W)
    (Tp Tm : RootedTemplate t m g) (S : Finset (Tok ι)) (f : Tok ι → Fin (m + 1) → W)
    (hf : RootedCopies p G B Z x (tmpl Tp Tm) S f)
    (hbal : ∀ τ : Tok ι, ∀ j, j ≠ 0 →
      vcharge (σc ((tmpl Tp Tm τ).L j)) (tmpl Tp Tm τ).L j (tmpl Tp Tm τ).E = 0)
    (τ : Tok ι) (hτ : τ ∈ S) (y : W) (hyx : y ≠ x) :
    vcharge (σc (p y)) p y (mappedTok Tp Tm f τ) = 0 := by
  have hinj := hf.injective τ hτ
  have hl := hf.labels τ hτ
  have hloop : ∀ e ∈ mappedTok Tp Tm f τ, ¬ e.IsDiag :=
    PaddedF12.loopless_image (f τ) hinj _ (tmpl Tp Tm τ).loop
  rw [← vcharge_eq_charge _ p y _ hloop]
  by_cases hy : ∃ j, f τ j = y
  · obtain ⟨j, rfl⟩ := hy
    have hj : j ≠ 0 := fun h => hyx (by rw [h, hf.root τ hτ])
    unfold mappedTok mappedM
    rw [PaddedF12.charge_image (f τ) hinj (relab p (f τ j)) (relab (tmpl Tp Tm τ).L j)
      (relab_comp_of_injective p _ (f τ) hinj hl j), hl j,
      vcharge_eq_charge _ _ _ _ (tmpl Tp Tm τ).loop]
    exact hbal τ j hj
  · push Not at hy
    unfold mappedTok mappedM
    rw [PaddedF12.charge_image (f τ) hinj (relab p y) (fun k => ((tmpl Tp Tm τ).L k).castSucc)
      (relab_comp_of_not_mem p _ (f τ) hl y hy)]
    exact charge_chiV_castSucc _ _ _

/-- **Rooted copies are tokens.** -/
theorem tokReal_of_rootedCopies (σ : Fin t → ℤ) (p : W → Fin t)
    (G : SimpleGraph W) [DecidableRel G.Adj] (B : Finset (Sym2 W)) (Z : Finset W) (x : W)
    (Tp Tm : RootedTemplate t m g) (S : Finset (Tok ι)) (f : Tok ι → Fin (m + 1) → W)
    (hf : RootedCopies p G B Z x (tmpl Tp Tm) S f)
    (hcP : charge (chiV σ) (relab Tp.L 0) Tp.E = 2)
    (hcM : charge (chiV σ) (relab Tm.L 0) Tm.E = -2) :
    TokReal (chiV σ) (fun _ _ => 0) (relab p x) 2 g B S (mappedTok Tp Tm f) := by
  refine ⟨hf.disjoint, hf.avoid, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_,
    fun τ hτ => ?_⟩
  · exact PaddedF12.loopless_image (f τ) (hf.injective τ hτ) _ (tmpl Tp Tm τ).loop
  · exact PaddedF12.even_image (f τ) (hf.injective τ hτ) _ (tmpl Tp Tm τ).even
  · have hinj := hf.injective τ hτ
    have h0 : f τ 0 = x := hf.root τ hτ
    unfold mappedTok mappedM
    rw [PaddedF12.charge_image (f τ) hinj (relab p x) (relab (tmpl Tp Tm τ).L 0)
      (by rw [← h0]; exact relab_comp_of_injective p _ (f τ) hinj (hf.labels τ hτ) 0)]
    unfold tmpl
    split_ifs with hs
    · exact hcP
    · exact hcM
  · simp [charge, pair]
  · exact card_image_le.trans (tmpl Tp Tm τ).card

/-- A vertex of `Z` other than the root carries no token edge. -/
theorem load_mappedTok_of_mem_Z (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (B : Finset (Sym2 W)) (Z : Finset W) (x : W) (Tp Tm : RootedTemplate t m g)
    (S : Finset (Tok ι)) (f : Tok ι → Fin (m + 1) → W) (hf : RootedCopies p G B Z x (tmpl Tp Tm) S f)
    (w : W) (hw : w ∈ Z) (hwx : w ≠ x) (τ : Tok ι) (hτ : τ ∈ S) :
    incidentLoad (mappedTok Tp Tm f τ) w = 0 := by
  apply ColouredHub.incidentLoad_image_of_notMem
  intro k hk
  by_cases hk0 : k = 0
  · exact hwx (by rw [← hk, hk0, hf.root τ hτ])
  · exact hf.outside τ hτ k hk0 (hk ▸ hw)

/-- A vertex other than the root is loaded by at most one token, hence by at most `g`. -/
theorem sum_load_mappedTok_le (p : W → Fin t) (G : SimpleGraph W) [DecidableRel G.Adj]
    (B : Finset (Sym2 W)) (Z : Finset W) (x : W) (Tp Tm : RootedTemplate t m g)
    (S : Finset (Tok ι)) (f : Tok ι → Fin (m + 1) → W) (hf : RootedCopies p G B Z x (tmpl Tp Tm) S f)
    (w : W) (hwx : w ≠ x) : ∑ τ ∈ S, incidentLoad (mappedTok Tp Tm f τ) w ≤ g := by
  classical
  by_cases h : ∃ τ ∈ S, ∃ k, f τ k = w
  · obtain ⟨τ, hτ, k, hk⟩ := h
    rw [← add_sum_erase S _ hτ]
    have hrest : ∑ τ' ∈ S.erase τ, incidentLoad (mappedTok Tp Tm f τ') w = 0 := by
      refine sum_eq_zero fun τ' hτ' => ?_
      obtain ⟨hne, hτ'S⟩ := mem_erase.mp hτ'
      apply ColouredHub.incidentLoad_image_of_notMem
      intro k' hk'
      have hk0 : k ≠ 0 := fun h0 => hwx (by rw [← hk, h0, hf.root τ hτ])
      exact hf.internal τ hτ τ' hτ'S (Ne.symm hne) k k' hk0 (hk.trans hk'.symm)
    rw [hrest, add_zero]
    exact incidentLoad_mapped_le _ (tmpl Tp Tm τ).card _ w
  · push Not at h
    have hz : ∀ τ ∈ S, incidentLoad (mappedTok Tp Tm f τ) w = 0 := fun τ hτ =>
      ColouredHub.incidentLoad_image_of_notMem _ _ _ (h τ hτ)
    rw [sum_eq_zero hz]
    exact Nat.zero_le _

/-- The root is loaded by at most `g` per token. -/
theorem sum_load_mappedTok_root_le (Tp Tm : RootedTemplate t m g) (S : Finset (Tok ι))
    (f : Tok ι → Fin (m + 1) → W) (w : W) :
    ∑ τ ∈ S, incidentLoad (mappedTok Tp Tm f τ) w ≤ g * S.card := by
  calc ∑ τ ∈ S, incidentLoad (mappedTok Tp Tm f τ) w ≤ ∑ _τ ∈ S, g :=
        sum_le_sum fun τ _ => incidentLoad_mapped_le _ (tmpl Tp Tm τ).card _ w
    _ = g * S.card := by rw [sum_const, smul_eq_mul, mul_comm]

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.tokReal_of_rootedCopies
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.vcharge_mappedTok_eq_zero
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.sum_load_mappedTok_le
