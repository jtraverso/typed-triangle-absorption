/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLiftCore

@[expose] public section

/-! Insert the original matching of split input arcs into the fixed root network.
This gives a genuine cyclic degree17 graph, with every root-balanced input
subset completed to a balanced subset of that graph. Physical host embedding
and the construction of the split matching from X remain separate. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift

open Finset Cycles

set_option maxHeartbeats 1000000

variable {P : Type} [DecidableEq P]
variable {V : Type} [Fintype P] [Fintype V] [DecidableEq V]

/-- Fix equality on the dependent channel type before constructing its sums
and products. This keeps every finite union on the same instance. -/
noncomputable instance channelDecidableEq (root : P → V) (σ : RootChannels.Perms root) :
    DecidableEq (RootChannels.Channel root σ) :=
  fun a b => Sigma.instDecidableEqSigma a b

theorem exists_degree17_lift (root : P → V) (c : V → ZMod 3)
    (S : Finset (P × P)) (hS : IsCyc (c ∘ root) S) (hdeg : MaxDegLE S 1) :
    ∃ σ : RootChannels.Perms root,
      let s := RootChannels.src root σ
      let d := RootChannels.dst root σ
      let I := S.map (liftArc P (RootChannels.Channel root σ × Fin 2))
      let N := RootPaths.arcs s d
      Disjoint N I ∧ IsCyc (RootPaths.colour s (c ∘ root)) (N ∪ I) ∧
      MaxDegLE (N ∪ I) 17 ∧ (N ∪ I).card ≤ 24 * Fintype.card P + S.card ∧
      ∀ L ⊆ S,
        (∀ v, ∑ p : RootChannels.Fibre root v,
          ((outDeg L p.val : ℤ) - (inDeg L p.val : ℤ)) = 0) →
        ∃ A ⊆ N, Balanced (A ∪ L.map
          (liftArc P (RootChannels.Channel root σ × Fin 2))) := by
  obtain ⟨σ, hcyc, h16, hsize, hroute⟩ := RootPaths.exists_root_paths root c
  refine ⟨σ, ?_⟩
  dsimp only
  have h := network_lift root c (RootChannels.src root σ) (RootChannels.dst root σ)
    S hS hdeg hcyc h16 hsize hroute
  dsimp only at h
  exact h

/-- The split-port set has exactly two ports per original input edge. -/
theorem size49 {portCount inputCount netCount : ℕ}
    (hp : portCount = 2 * inputCount) (hnet : netCount ≤ 24 * portCount + inputCount) :
    netCount ≤ 49 * inputCount := by omega

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift.exists_degree17_lift
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift.exists_degree17_lift
