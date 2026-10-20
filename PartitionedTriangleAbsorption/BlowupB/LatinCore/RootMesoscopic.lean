/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootInput
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.DenseProducer.Rooted

@[expose] public section

/-! Connect the actual split input and the SAME fixed routing network to the
proved rooted mesoscopic producer. This still asserts no physical embedding. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootMesoscopic

open Finset Cycles Cycles.DenseRed

set_option maxHeartbeats 1000000

def MesoscopicSpec {P V : Type} [Fintype P] [DecidableEq P]
    [Fintype V] [DecidableEq V] (root : P → V) (c : V → ZMod 3)
    (S : Finset (P × P)) (σ : RootChannels.Perms root) : Prop :=
  let s := RootChannels.src root σ
  let d := RootChannels.dst root σ
  let I := S.map (liftArc P (RootChannels.Channel root σ × Fin 2))
  let N := RootPaths.arcs s d
  RootedMesoscopicFor (denseConst DenseProducer.Cdense Greedy.goodConst) 20
    (RootPaths.colour s (c ∘ root)) (N ∪ I)

theorem mesoscopic_of_lift {P V : Type} [Fintype P] [DecidableEq P]
    [Fintype V] [DecidableEq V] (root : P → V) (c : V → ZMod 3)
    (S : Finset (P × P)) (bound : ℕ) (σ : RootChannels.Perms root)
    (h : RootInput.LiftSpec root c S bound σ) : MesoscopicSpec root c S σ := by
  obtain ⟨-, hcY, hdY, -, -⟩ := h
  exact DenseProducer.rootedMesoscopicFor _ _ _ hcY hdY

theorem exists_refined_input {V : Type} [Fintype V] [DecidableEq V]
    (X : Finset (V × V)) (c : V → ZMod 3) (hc : IsCyc c X) :
    ∃ σ : RootChannels.Perms (SplitPorts.root X),
      RootInput.LiftSpec (SplitPorts.root X) c (SplitPorts.arcs X) (49 * X.card) σ ∧
      MesoscopicSpec (SplitPorts.root X) c (SplitPorts.arcs X) σ ∧
      ∀ L ⊆ X, Balanced L →
        RootInput.Completed (SplitPorts.root X) σ (SplitPorts.arcsOf X L) := by
  obtain ⟨σ, hlift, hroute⟩ := RootInput.exists_input_lift X c hc
  exact ⟨σ, hlift, mesoscopic_of_lift _ _ _ _ _ hlift, hroute⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootMesoscopic

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.RootMesoscopic.exists_refined_input
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootMesoscopic.exists_refined_input
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootMesoscopic.mesoscopic_of_lift
