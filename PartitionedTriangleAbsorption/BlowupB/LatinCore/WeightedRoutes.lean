/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedEdgeLedger
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedPathStep

@[expose] public section

/-! Indexed physical path iteration with all endpoints precharged. The
construction is allowed to identify anchors, but never reuses a physical edge.
The catalogue-to-weight connection remains a separate obligation. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRoutes

open Finset AntiEdgeSelection StructuralF3General PaddedNoCommon WeightedEdgeLedger

variable {V I : Type} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq I]

def current (initial : V → ℝ) (weight : I → ℝ) (S : Finset I)
    (x y z : I → V) (r : V) : ℝ :=
  initial r + ∑ e ∈ S, interiorCharge (weight e) (x e) (y e) (z e) r

theorem exists_paths (p : V → Fin 3) (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset I) (u v : I → V) (i j k : I → Fin 3) (weight : I → ℝ)
    (X : Finset (Sym2 V)) (initial : V → ℝ) (a d T W M : ℝ)
    (hs : GuardedSupply p G (fun i j => i ≠ j) 2 a)
    (hd : 0 ≤ d) (hT : 0 < T) (hW : 0 ≤ W) (hX : DegBounded X d)
    (hi : ∀ r, 0 ≤ initial r) (hicap : ∀ r, initial r ≤ T + W)
    (himass : ∑ r, initial r ≤ M) (hwmass : 2 * (∑ e ∈ E, weight e) ≤ M)
    (hw : ∀ e ∈ E, 1 ≤ weight e ∧ weight e ≤ W)
    (hpre : ∀ r, (∑ e ∈ E, endpointCharge (weight e) (u e) (v e) r) ≤ initial r)
    (hu : ∀ e ∈ E, p (u e) = i e) (hv : ∀ e ∈ E, p (v e) = j e)
    (hij : ∀ e ∈ E, i e ≠ j e) (hik : ∀ e ∈ E, i e ≠ k e)
    (hjk : ∀ e ∈ E, j e ≠ k e)
    (hbudget : 4 * M / T + 4 + 2 * (d + T + 2 * W) < a) :
    ∃ x y z : I → V,
      (∀ e ∈ E, p (x e) = j e ∧ p (y e) = k e ∧ p (z e) = i e ∧
        IsPath4 G (u e) (x e) (y e) (z e) (v e)) ∧
      (∀ e ∈ E, Disjoint (pathEdges (u e) (x e) (y e) (z e) (v e)) X) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f →
        Disjoint (pathEdges (u e) (x e) (y e) (z e) (v e))
          (pathEdges (u f) (x f) (y f) (z f) (v f))) ∧
      (∀ r, current initial weight E x y z r ≤ T + 2 * W) ∧
      (∑ r, current initial weight E x y z r) ≤ 4 * M := by
  classical
  have hw0 : ∀ e ∈ E, 0 ≤ weight e := fun e he => by linarith [(hw e he).1]
  have huv : ∀ e ∈ E, u e ≠ v e := by
    intro e he h
    exact hij e he ((hu e he).symm.trans ((congrArg p h).trans (hv e he)))
  have hmain : ∀ S : Finset I, S ⊆ E → ∃ x y z : I → V,
      (∀ e ∈ S, p (x e) = j e ∧ p (y e) = k e ∧ p (z e) = i e ∧
        IsPath4 G (u e) (x e) (y e) (z e) (v e)) ∧
      (∀ e ∈ S, Disjoint (pathEdges (u e) (x e) (y e) (z e) (v e)) X) ∧
      (∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        Disjoint (pathEdges (u e) (x e) (y e) (z e) (v e))
          (pathEdges (u f) (x f) (y f) (z f) (v f))) ∧
      (∀ r, current initial weight S x y z r ≤ T + 2 * W) ∧
      (∑ r, current initial weight S x y z r) ≤ M + 6 * (∑ e ∈ S, weight e) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨fun _ => Classical.arbitrary V, fun _ => Classical.arbitrary V,
          fun _ => Classical.arbitrary V, by simp, by simp, by simp, ?_, ?_⟩
        · intro r
          simpa [current] using (by linarith [hicap r] : initial r ≤ T + 2 * W)
        · simpa [current] using himass
    | @insert e S he ih =>
        intro hSE
        have heE := hSE (mem_insert_self e S)
        have hS : S ⊆ E := (subset_insert e S).trans hSE
        obtain ⟨x,y,z,hpath,havoid,hdis,hcap,hmass⟩ := ih hS
        let B := X ∪ S.biUnion (fun f => pathEdges (u f) (x f) (y f) (z f) (v f))
        let q := current initial weight S x y z
        have hB : DegBounded B (d + T + 2 * W) :=
          degree_bound G X E S hS u v x y z weight (fun f hf => (hw f hf).1)
            (fun f hf => huv f (hS hf)) (fun f hf => (hpath f hf).2.2.2)
            initial hpre d T W hX hcap
        have hq : ∀ r, 0 ≤ q r := by
          intro r
          apply add_nonneg (hi r)
          apply sum_nonneg
          intro f hf
          unfold interiorCharge
          split_ifs <;> linarith [hw0 f (hS hf)]
        have hsumS : (∑ f ∈ S, weight f) ≤ ∑ f ∈ E, weight f :=
          sum_le_sum_of_subset_of_nonneg hS (fun f hf _ => hw0 f hf)
        have htotal : M + 6 * (∑ f ∈ S, weight f) ≤ 4 * M := by linarith
        have hdiv := div_le_div_of_nonneg_right htotal hT.le
        obtain ⟨a1,a2,a3,ha1,ha2,ha3,ha1u,ha1v,ha3u,ha3v,ha13,
          ha2u,ha2v,ha21,ha23,hua1,ha12,ha23adj,ha3vAdj,
          h1B,h2B,h3B,h4B,hnew0,hnewcap,hnewmass⟩ :=
          WeightedPathStep.exists_weighted_path p G a (d + T + 2 * W) T
            (M + 6 * (∑ f ∈ S, weight f)) (weight e) W (by linarith) hT
            (hw0 e heE) (hw e heE).2 hs B hB q hq hmass hcap (by linarith)
            (u e) (v e) (i e) (j e) (k e) (hu e heE) (hv e heE)
            (hij e heE) (hik e heE) (hjk e heE)
        let x' := Function.update x e a1
        let y' := Function.update y e a2
        let z' := Function.update z e a3
        have hnewpath : IsPath4 G (u e) a1 a2 a3 (v e) :=
          ⟨hua1,ha12,ha23adj,ha3vAdj,ha1v,ha3u,ha13,ha2u,ha2v⟩
        have hnewB : Disjoint (pathEdges (u e) a1 a2 a3 (v e)) B := by
          rw [disjoint_left]
          intro edge hedge hbad
          simp only [PaddedNoCommon.pathEdges, mem_insert, mem_singleton] at hedge
          rcases hedge with rfl | rfl | rfl | rfl
          · exact h1B hbad
          · exact h2B hbad
          · exact h3B hbad
          · exact h4B hbad
        have hXB : X ⊆ B := subset_union_left
        have hPB : ∀ f ∈ S, pathEdges (u f) (x f) (y f) (z f) (v f) ⊆ B := by
          intro f hf edge hedge
          exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨f,hf,hedge⟩))
        have hupdate : ∀ r, current initial weight (insert e S) x' y' z' r =
            WeightedPathStep.charge q (weight e) a1 a2 a3 r := by
          intro r
          have hsame : (∑ f ∈ S, interiorCharge (weight f) (x' f) (y' f) (z' f) r) =
              ∑ f ∈ S, interiorCharge (weight f) (x f) (y f) (z f) r := by
            apply sum_congr rfl
            intro f hf
            have hfe : f ≠ e := by intro h; subst f; exact he hf
            simp only [x',y',z',Function.update_of_ne hfe]
          simp only [current, sum_insert he]
          rw [hsame]
          simp [x',y',z',WeightedPathStep.charge, q, current, interiorCharge]
          ring
        refine ⟨x',y',z', ?_, ?_, ?_, ?_, ?_⟩
        · intro f hf
          rcases mem_insert.mp hf with rfl | hf
          · simpa [x',y',z'] using And.intro ha1 (And.intro ha2 (And.intro ha3 hnewpath))
          · have hfe : f ≠ e := by intro h; subst f; exact he hf
            simpa only [x',y',z',Function.update_of_ne hfe] using hpath f hf
        · intro f hf
          rcases mem_insert.mp hf with rfl | hf
          · simpa [x',y',z'] using hnewB.mono_right hXB
          · have hfe : f ≠ e := by intro h; subst f; exact he hf
            simpa only [x',y',z',Function.update_of_ne hfe] using havoid f hf
        · intro f hf g hg hfg
          by_cases hfe : f = e
          · subst f
            have hge : g ≠ e := Ne.symm hfg
            have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hge
            simpa only [x',y',z',Function.update_self,Function.update_of_ne hge] using
              hnewB.mono_right (hPB g hgS)
          · have hfS : f ∈ S := (mem_insert.mp hf).resolve_left hfe
            by_cases hge : g = e
            · subst g
              simpa only [x',y',z',Function.update_self,Function.update_of_ne hfe] using
                (hnewB.mono_right (hPB f hfS)).symm
            · have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hge
              simpa only [x',y',z',Function.update_of_ne hfe,Function.update_of_ne hge] using
                hdis f hfS g hgS hfg
        · intro r
          rw [hupdate r]
          exact hnewcap r
        · simp_rw [hupdate]
          rw [sum_insert he]
          linarith
  obtain ⟨x,y,z,hp,ha,hdis,hcap,hmass⟩ := hmain E subset_rfl
  exact ⟨x,y,z,hp,ha,hdis,hcap,hmass.trans (by linarith)⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRoutes

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRoutes.exists_paths
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.WeightedRoutes.exists_paths
