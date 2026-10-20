/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Filling

@[expose] public section

/-! Insert a matching into a fixed network with an abstract channel type.
Keeping the channel type as a parameter prevents elaboration from expanding
the dependent permutation/fibre representation throughout the balance proof. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift

open Finset Cycles
open scoped Classical

variable {P E V : Type} [DecidableEq P] [Fintype E] [DecidableEq E]
  [Fintype P] [Fintype V] [DecidableEq V]

omit [Fintype P] in
theorem no_old_arc (src dst : E → P) (p q : P) :
    (Sum.inl p, Sum.inl q) ∉ RootPaths.arcs src dst := by
  simp [RootPaths.arcs, RootPaths.arcsOf, RootPaths.pathArcs]

theorem disjoint_input (src dst : E → P) (S : Finset (P × P)) :
    Disjoint (RootPaths.arcs src dst) (S.map (liftArc P (E × Fin 2))) := by
  rw [disjoint_left]
  intro e he heS
  obtain ⟨a, -, rfl⟩ := mem_map.mp heS
  exact no_old_arc src dst a.1 a.2 he

theorem inDeg_union_eq {W : Type} [DecidableEq W] (A B : Finset (W × W))
    (h : Disjoint A B) (v : W) : inDeg (A ∪ B) v = inDeg A v + inDeg B v := by
  unfold inDeg
  rw [filter_union, card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _))]

theorem outDeg_union_eq {W : Type} [DecidableEq W] (A B : Finset (W × W))
    (h : Disjoint A B) (v : W) : outDeg (A ∪ B) v = outDeg A v + outDeg B v := by
  unfold outDeg
  rw [filter_union, card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _))]

theorem degree_mono {W : Type} [DecidableEq W] {A B : Finset (W × W)}
    (h : A ⊆ B) (v : W) : deg A v ≤ deg B v := by
  have hi : inDeg A v ≤ inDeg B v := card_le_card (filter_subset_filter _ h)
  have ho : outDeg A v ≤ outDeg B v := card_le_card (filter_subset_filter _ h)
  exact Nat.add_le_add hi ho

theorem network_lift (root : P → V) (c : V → ZMod 3) (s d : E → P)
    (S : Finset (P × P)) (hS : IsCyc (c ∘ root) S) (hdeg : MaxDegLE S 1)
    (hcyc : IsCyc (RootPaths.colour s (c ∘ root)) (RootPaths.arcs s d))
    (h16 : MaxDegLE (RootPaths.arcs s d) 16)
    (hsize : (RootPaths.arcs s d).card ≤ 24 * Fintype.card P)
    (hroute : ∀ b : P → ℤ,
      (∀ v, ∑ p : RootChannels.Fibre root v, b p.val = 0) →
      (∀ p, |b p| ≤ 1) → ∃ A ⊆ RootPaths.arcs s d,
        (∀ p, ((A.filter (fun e => e.2 = Sum.inl p)).card : ℤ) -
          ((A.filter (fun e => e.1 = Sum.inl p)).card : ℤ) = b p) ∧
        ∀ e i, (A.filter (fun a => a.2 = Sum.inr (e,i))).card =
          (A.filter (fun a => a.1 = Sum.inr (e,i))).card) :
    let I := S.map (liftArc P (E × Fin 2))
    let N := RootPaths.arcs s d
    Disjoint N I ∧ IsCyc (RootPaths.colour s (c ∘ root)) (N ∪ I) ∧
      MaxDegLE (N ∪ I) 17 ∧ (N ∪ I).card ≤ 24 * Fintype.card P + S.card ∧
      ∀ L ⊆ S,
        (∀ v, ∑ p : RootChannels.Fibre root v,
          ((outDeg L p.val : ℤ) - (inDeg L p.val : ℤ)) = 0) →
        ∃ A ⊆ N, Balanced (A ∪ L.map (liftArc P (E × Fin 2))) := by
  classical
  let U := E × Fin 2
  let N := RootPaths.arcs s d
  let I := S.map (liftArc P U)
  have hinput : IsCyc (RootPaths.colour s (c ∘ root)) I := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := mem_map.mp he
    exact hS a ha
  have h17 : MaxDegLE (N ∪ I) 17 := maxDegLE_union h16 (maxDegLE_map_liftArc hdeg)
  refine ⟨disjoint_input s d S, hcyc.union hinput, h17, ?_, ?_⟩
  · calc (N ∪ I).card ≤ N.card + I.card := card_union_le N I
      _ = N.card + S.card := by simp only [I, card_map]
      _ ≤ 24 * Fintype.card P + S.card := Nat.add_le_add_right hsize S.card
  · intro L hLS hroot
    let b : P → ℤ := fun p => (outDeg L p : ℤ) - (inDeg L p : ℤ)
    have hb : ∀ p, |b p| ≤ 1 := by
      intro p
      have hh : deg L p ≤ 1 := (degree_mono hLS p).trans (hdeg p)
      unfold deg at hh
      dsimp [b]
      rw [abs_le]
      omega
    obtain ⟨A, hAN, hport, haux⟩ := hroute b hroot hb
    have hdis : Disjoint A (L.map (liftArc P U)) :=
      (disjoint_input s d S).mono hAN (map_subset_map.mpr hLS)
    refine ⟨A, hAN, ?_⟩
    intro x
    rw [inDeg_union_eq A _ hdis x, outDeg_union_eq A _ hdis x,
      inDeg_map_liftArc, outDeg_map_liftArc]
    rcases x with p | ⟨e,i⟩
    · simp only [Sum.elim_inl]
      have hh := hport p
      change (inDeg A (Sum.inl p) : ℤ) - (outDeg A (Sum.inl p) : ℤ) =
        (outDeg L p : ℤ) - (inDeg L p : ℤ) at hh
      omega
    · simp only [Sum.elim_inr, Nat.add_zero]
      exact haux e i

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootLift.network_lift
