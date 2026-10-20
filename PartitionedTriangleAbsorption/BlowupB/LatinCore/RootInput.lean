/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.SplitPorts

@[expose] public section

/-! The actual input X produces the degree17 routing graph. Its fixed network
is chosen before every balanced physical L contained in X. Physical embedding
of this graph is not asserted in this module. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootInput

open Finset Cycles

set_option maxHeartbeats 1000000

variable {V : Type} [Fintype V] [DecidableEq V]

def Completed {P : Type} [Fintype P] [DecidableEq P]
    (root : P → V) (σ : RootChannels.Perms root) (L : Finset (P × P)) : Prop :=
  ∃ A ⊆ RootPaths.arcs (RootChannels.src root σ) (RootChannels.dst root σ),
    Balanced (A ∪ L.map (liftArc P (RootChannels.Channel root σ × Fin 2)))

/-- Elaborate the finite unions with an abstract port type, before specialising
to the dependent split-port representation. The channel equality is the same
structural instance as in RootLift. -/
def LiftSpec {P : Type} [Fintype P] [DecidableEq P]
    (root : P → V) (c : V → ZMod 3) (S : Finset (P × P))
    (bound : ℕ) (σ : RootChannels.Perms root) : Prop :=
  let s := RootChannels.src root σ
  let d := RootChannels.dst root σ
  let I := S.map (liftArc P (RootChannels.Channel root σ × Fin 2))
  let N := RootPaths.arcs s d
  Disjoint N I ∧ IsCyc (RootPaths.colour s (c ∘ root)) (N ∪ I) ∧
  MaxDegLE (N ∪ I) 17 ∧ (N ∪ I).card ≤ bound ∧
  ∀ L ⊆ S, (∀ v, ∑ p : RootChannels.Fibre root v,
    ((outDeg L p.val : ℤ) - (inDeg L p.val : ℤ)) = 0) →
    Completed root σ L

theorem root_balance (X L : Finset (V × V)) (hL : L ⊆ X) (hb : Balanced L) (v : V) :
    ∑ p : RootChannels.Fibre (SplitPorts.root X) v,
      ((outDeg (SplitPorts.arcsOf X L) p.val : ℤ) -
        (inDeg (SplitPorts.arcsOf X L) p.val : ℤ)) = 0 := by
  classical
  have hi := degree_fiber (SplitPorts.arcsOf X L) (SplitPorts.root X)
    (SplitPorts.root_injective X L) Prod.snd Prod.snd (fun _ => rfl) v
  have ho := degree_fiber (SplitPorts.arcsOf X L) (SplitPorts.root X)
    (SplitPorts.root_injective X L) Prod.fst Prod.fst (fun _ => rfl) v
  rw [SplitPorts.root_image X L hL] at hi ho
  have hiFib : inDeg L v = ∑ p : RootChannels.Fibre (SplitPorts.root X) v,
      inDeg (SplitPorts.arcsOf X L) p.val := by
    calc _ = ∑ p ∈ univ.filter (fun p => SplitPorts.root X p = v),
        inDeg (SplitPorts.arcsOf X L) p := hi
      _ = _ := Finset.sum_subtype _ (by simp) _
  have hoFib : outDeg L v = ∑ p : RootChannels.Fibre (SplitPorts.root X) v,
      outDeg (SplitPorts.arcsOf X L) p.val := by
    calc _ = ∑ p ∈ univ.filter (fun p => SplitPorts.root X p = v),
        outDeg (SplitPorts.arcsOf X L) p := ho
      _ = _ := Finset.sum_subtype _ (by simp) _
  have hiInt : (inDeg L v : ℤ) = ∑ p : RootChannels.Fibre (SplitPorts.root X) v,
      (inDeg (SplitPorts.arcsOf X L) p.val : ℤ) := by exact_mod_cast hiFib
  have hoInt : (outDeg L v : ℤ) = ∑ p : RootChannels.Fibre (SplitPorts.root X) v,
      (outDeg (SplitPorts.arcsOf X L) p.val : ℤ) := by exact_mod_cast hoFib
  rw [sum_sub_distrib, ← hoInt, ← hiInt, hb v, sub_self]

/-- No routing, matching or degree17 producer is an external premise. -/
theorem exists_input_lift (X : Finset (V × V)) (c : V → ZMod 3) (hc : IsCyc c X) :
    ∃ σ : RootChannels.Perms (SplitPorts.root X),
      LiftSpec (SplitPorts.root X) c (SplitPorts.arcs X) (49 * X.card) σ ∧
      ∀ L ⊆ X, Balanced L →
        Completed (SplitPorts.root X) σ (SplitPorts.arcsOf X L) := by
  obtain ⟨σ, hdis, hcyc, hdeg, hsize, hroute⟩ :=
    RootLift.exists_degree17_lift (SplitPorts.root X) c (SplitPorts.arcs X)
      (SplitPorts.cyclic X c hc) (SplitPorts.matching X X)
  refine ⟨σ, ⟨hdis, hcyc, hdeg, ?_, hroute⟩, ?_⟩
  · have hp := SplitPorts.port_card X
    have hI : (SplitPorts.arcs X).card = X.card := SplitPorts.arcsOf_card X X subset_rfl
    omega
  · intro L hLX hbal
    exact hroute (SplitPorts.arcsOf X L) (SplitPorts.arcsOf_subset X L)
      (root_balance X L hLX hbal)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootInput

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.RootInput.exists_input_lift
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootInput.exists_input_lift
