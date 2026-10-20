/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueAnchors

@[expose] public section

/-! The actual split input pays for the prescribed-root loads: there is
one port for each original incidence, and at most1257 catalogue incidences
at each port. Thus the root budget is1257 times the input degree. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootAnchorBudget

open Finset Cycles

variable {V P J U : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem port_degree (X : Finset (V × V)) (p : SplitPorts.Port X) :
    deg (SplitPorts.arcs X) p = 1 := by
  rcases p with ⟨e, i⟩
  change inDeg (SplitPorts.arcsOf X X) (e,i) +
    outDeg (SplitPorts.arcsOf X X) (e,i) = 1
  rw [SplitPorts.in_count, SplitPorts.out_count]
  fin_cases i <;> simp [e.property]

omit [Fintype V] in
theorem root_fibre_card (X : Finset (V × V)) (r : V) :
    (univ.filter (fun p : SplitPorts.Port X => SplitPorts.root X p = r)).card =
      deg X r := by
  have h := deg_arcImage (SplitPorts.arcs X) (SplitPorts.root X)
    (SplitPorts.root_injective X X) r
  have himage : (SplitPorts.arcs X).image (arcImage (SplitPorts.root X)) = X :=
    SplitPorts.root_image X X subset_rfl
  rw [himage] at h
  simp_rw [port_degree] at h
  simpa using h.symm

def pin (root : P → V) : (P ⊕ J) ⊕ U → Option V
  | Sum.inl (Sum.inl p) => some (root p)
  | _ => none

theorem network_degree [Fintype P] [DecidableEq P] (root : P → V)
    (σ : RootChannels.Perms root) :
    MaxDegLE (RootPaths.arcs (RootChannels.src root σ) (RootChannels.dst root σ)) 16 := by
  intro v
  rcases v with p | ⟨e,i⟩
  · unfold deg inDeg outDeg
    rw [RootPaths.arcs, RootPaths.card_in_port, RootPaths.card_out_port]
    have hi := RootChannels.in_degree_le root σ p
    have ho := RootChannels.out_degree_le root σ p
    omega
  · unfold deg inDeg outDeg
    rw [RootPaths.arcs, RootPaths.card_in_aux, RootPaths.card_out_aux]
    simp

theorem old_load_cap {A : Type} [DecidableEq A]
    (Y N : Finset (A × A)) (lib : Finset (Finset (((A ⊕ U) × (A ⊕ U)))))
    [DecidableEq U] (hY : MaxDegLE Y 17) (hN : MaxDegLE N 16)
    (hload : ∀ a, catalogLoad lib (Sum.inl a) ≤ 73 * deg Y a + deg N a) :
    ∀ a, catalogLoad lib (Sum.inl a) ≤ 1257 := by
  intro a
  have hy := hY a
  have hn := hN a
  have hl := hload a
  omega

omit [Fintype V] in
theorem pinned_load_eq [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J]
    [Fintype U] [DecidableEq U] (root : P → V) (weight : (P ⊕ J) ⊕ U → ℝ) (r : V) :
    CatalogueAnchors.pinnedLoad (pin root) weight r =
      ∑ p : P, if root p = r then weight (Sum.inl (Sum.inl p)) else 0 := by
  simp [CatalogueAnchors.pinnedLoad, pin, Fintype.sum_sum_type]

omit [Fintype V] in
theorem pinned_load_le [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
    (X : Finset (V × V)) (weight : (SplitPorts.Port X ⊕ J) ⊕ U → ℝ)
    (hcap : ∀ p, weight (Sum.inl (Sum.inl p)) ≤ 1257) (r : V) :
    CatalogueAnchors.pinnedLoad (pin (SplitPorts.root X)) weight r ≤
      1257 * (deg X r : ℝ) := by
  rw [pinned_load_eq]
  calc
    _ ≤ ∑ p : SplitPorts.Port X, if SplitPorts.root X p = r then (1257 : ℝ) else 0 := by
      apply sum_le_sum
      intro p _
      by_cases h : SplitPorts.root X p = r
      · simpa only [h, ite_true] using hcap p
      · simp [h]
    _ = 1257 * (deg X r : ℝ) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, root_fibre_card]
      ring

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootAnchorBudget

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootAnchorBudget.root_fibre_card
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootAnchorBudget.network_degree
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootAnchorBudget.pinned_load_le
