/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Defs

@[expose] public section

/-! OPEN reduced target. No inhabitant is asserted. Balanced bounded pieces
are sufficient; they need not be triangles or simple cycles. The reserve's
size is redundant, since its fixed baseline is covered by the catalogue. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

def catalogLoad {W : Type*} [DecidableEq W]
    (lib : Finset (Finset (W × W))) (v : W) : ℕ := ∑ P ∈ lib, deg P v

def MesoscopicRefinerWith (C K : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3)
    (Y : Finset (V × V)), IsCyc c Y → MaxDegLE Y 17 →
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (cU : U → ZMod 3)
      (R : Finset ((V ⊕ U) × (V ⊕ U)))
      (lib : Finset (Finset ((V ⊕ U) × (V ⊕ U)))),
      IsCyc (Sum.elim c cU) R ∧ Disjoint R (Y.map (liftArc V U)) ∧
      (∀ P ∈ lib, P.Nonempty ∧ P ⊆ R ∪ Y.map (liftArc V U) ∧
        P.card ≤ K ∧ Balanced P) ∧
      lib.card ≤ C * Y.card ∧
      (∀ v, catalogLoad lib v ^ 2 ≤ C ^ 2 * Y.card) ∧
      ∀ L ⊆ Y, Balanced L →
        ∃ Q ⊆ lib, (Q : Set (Finset ((V ⊕ U) × (V ⊕ U)))).PairwiseDisjoint id ∧
          Q.biUnion id = R ∪ L.map (liftArc V U)

/-- The mesoscopic alternative to CycleShortener: deliberately OPEN. -/
def MesoscopicRefiner : Prop := ∃ C K : ℕ, 1 ≤ C ∧ 3 ≤ K ∧ MesoscopicRefinerWith C K

/-- A baseline inside the catalogue already bounds the reserve size.
No producer or universal quantification is hidden in the hypotheses. -/
theorem reserve_card_of_baseline {E : Type*} [DecidableEq E]
    (lib Q : Finset (Finset E)) (R : Finset E) (K : ℕ)
    (hQ : Q ⊆ lib) (hcover : Q.biUnion id = R)
    (hK : ∀ P ∈ lib, P.card ≤ K) : R.card ≤ K * lib.card := by
  calc
    R.card = (Q.biUnion id).card := by rw [hcover]
    _ ≤ ∑ P ∈ Q, P.card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ Q, K := Finset.sum_le_sum (fun P hP => hK P (hQ hP))
    _ = K * Q.card := by simp [mul_comm]
    _ ≤ K * lib.card := Nat.mul_le_mul_left K (Finset.card_le_card hQ)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.reserve_card_of_baseline
