/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.VertexCharge

@[expose] public section

/-!
# One vertex layer of the balance fixer

`vertex_layer` applies `token_layer_struct` to the signed degree at one vertex `x`
(`vcharge σ p x`, read as the class-pair charge `charge (chiV σ) (relab p x)`). The new refiner
refines the leftovers with `Q L ∧ vcharge σ p x L = 0`, every new piece has zero signed degree at `x`,
and every new piece is a union of tokens, alone or with one old piece.

`charge_newPiece` turns the shape into the identity used to stack layers: the charge of a new piece
is the charge of its old piece (or `0`) plus the charges of its tokens.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open PartitionedTriangleAbsorption.AntiEdgeSelection

variable {t : ℕ} {W : Type*} [DecidableEq W]

/-- A refiner for `Q1` refines every leftover satisfying a stronger predicate. -/
def _root_.PartitionedTriangleAbsorption.StructuralF3General.PredRefiner.mono {κ : Type*} {X0 : Finset (Sym2 W)} {Q1 Q2 : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q1) (h : ∀ L ⊆ X0, Q2 L → Q1 L) : PredRefiner κ X0 Q2 :=
  { E with refines := fun L hL hq => E.refines L hL (h L hL hq) }

/-- **One vertex layer.** -/
theorem vertex_layer {κ : Type*} {X0 : Finset (Sym2 W)} {Q : Finset (Sym2 W) → Prop}
    (E : PredRefiner κ X0 Q) (hQ0 : Q ∅) (hX0 : ∀ e ∈ X0, ¬ e.IsDiag)
    (σ : Fin t → ℤ) (p : W → Fin t) (x : W)
    (hdvd : ∀ i ∈ E.lib, (2 : ℤ) ∣ vcharge σ p x (E.P i)) (g : ℕ)
    (Extra : Finset (Tok κ) → (Tok κ → Finset (Sym2 W)) → Prop)
    (hsupply : ∀ S : Finset (Tok κ),
      S.card ≤ 9 * ∑ i ∈ E.lib, (vcharge σ p x (E.P i) / 2).natAbs →
      ∃ tokE, TokReal (chiV σ) (fun _ _ => 0) (relab p x) 2 g (E.R0 ∪ X0) S tokE ∧
        Extra S tokE) :
    ∃ (S : Finset (Tok κ)) (tokE : Tok κ → Finset (Sym2 W))
      (E' : PredRefiner (JIdx κ) X0 (fun L => Q L ∧ vcharge σ p x L = 0)),
      TokReal (chiV σ) (fun _ _ => 0) (relab p x) 2 g (E.R0 ∪ X0) S tokE ∧ Extra S tokE ∧
      S.card ≤ 9 * ∑ i ∈ E.lib, (vcharge σ p x (E.P i) / 2).natAbs ∧
      E'.R0 = E.R0 ∪ S.biUnion tokE ∧
      (∀ j ∈ E'.lib, vcharge σ p x (E'.P j) = 0) ∧
      (∀ j ∈ E'.lib, (E'.P j).card ≤ 2 * g ∨
        ∃ i ∈ E.lib, (E'.P j).card ≤ (E.P i).card + g * (vcharge σ p x (E.P i) / 2).natAbs) ∧
      (∀ w, ∑ j ∈ E'.lib, incidentLoad (E'.P j) w ≤
        ∑ i ∈ E.lib, incidentLoad (E.P i) w + 44 * ∑ τ ∈ S, incidentLoad (tokE τ) w) ∧
      E'.lib.card ≤ E.lib.card + 97 * ∑ i ∈ E.lib, (vcharge σ p x (E.P i) / 2).natAbs ∧
      (∀ j ∈ E'.lib, ∃ S1 ⊆ S,
        (E'.P j = S1.biUnion tokE ∧ (∀ i, j ≠ Sum.inl i) ∧ (E'.P j).card ≤ 2 * g) ∨
        ∃ i ∈ E.lib, j = Sum.inl i ∧ E'.P j = E.P i ∪ S1.biUnion tokE ∧
          (E'.P j).card ≤ (E.P i).card + g * (vcharge σ p x (E.P i) / 2).natAbs) := by
  have hc : ∀ i ∈ E.lib, charge (chiV σ) (relab p x) (E.P i) = vcharge σ p x (E.P i) :=
    fun i hi => vcharge_eq_charge σ p x (E.P i) (E.loopP i hi)
  have hsum : ∑ i ∈ E.lib, (charge (chiV σ) (relab p x) (E.P i) / 2).natAbs =
      ∑ i ∈ E.lib, (vcharge σ p x (E.P i) / 2).natAbs :=
    sum_congr rfl fun i hi => by rw [hc i hi]
  obtain ⟨S, tokE, E', hreal, hextra, hcard, hR0, hzero, -, hsize, hload, hlib, hstruct⟩ :=
    token_layer_struct E hQ0 (chiV σ) (fun _ _ => 0) (relab p x) 2 (by norm_num)
      (fun i hi => by rw [hc i hi]; exact hdvd i hi) g Extra
      (fun S hS => hsupply S (by rw [← hsum]; exact hS))
  refine ⟨S, tokE, E'.mono (fun L hL ⟨hq, hv⟩ =>
      ⟨hq, by rw [vcharge_eq_charge σ p x L (fun e he => hX0 e (hL he))]; exact hv⟩),
    hreal, hextra, hsum ▸ hcard, hR0, ?_, ?_, hload, hsum ▸ hlib, ?_⟩
  · intro j hj
    show vcharge σ p x (E'.P j) = 0
    rw [← vcharge_eq_charge σ p x _ (E'.loopP j hj)]
    exact hzero j hj
  · intro j hj
    rcases hsize j hj with h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, by rw [← hc i hi]; exact h⟩
  · intro j hj
    obtain ⟨S1, hS1, h⟩ := hstruct j hj
    refine ⟨S1, hS1, ?_⟩
    rcases h with h | ⟨i, hi, hji, hP, hcd⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, hji, hP, by rw [← hc i hi]; exact hcd⟩

/-- **Charges of the new pieces.** For a token layer whose pieces have the shape of
`token_layer_struct`, any class-pair charge of a new piece is the charge of its old piece
(or zero) plus the charges of its tokens. -/
theorem charge_newPiece {κ : Type*} {s : ℕ} (χ : Fin s → Fin s → ℤ) (q : W → Fin s)
    {S : Finset (Tok κ)} {tokE : Tok κ → Finset (Sym2 W)} {A : Finset (Sym2 W)}
    {t' : ℕ} {χ0 χ1 : Fin t' → Fin t' → ℤ} {p0 : W → Fin t'} {u : ℤ} {g : ℕ}
    (hreal : TokReal χ0 χ1 p0 u g A S tokE) {P O : Finset (Sym2 W)} {S1 : Finset (Tok κ)}
    (hS1 : S1 ⊆ S) (hOA : O ⊆ A)
    (hshape : P = S1.biUnion tokE ∨ P = O ∪ S1.biUnion tokE) :
    charge χ q P = (if P = S1.biUnion tokE then 0 else charge χ q O) +
      ∑ τ ∈ S1, charge χ q (tokE τ) := by
  have hdis : (S1 : Set (Tok κ)).PairwiseDisjoint tokE := hreal.disj.subset hS1
  rcases hshape with h | h
  · rw [if_pos h, zero_add, h, charge_biUnion χ q S1 tokE hdis]
  · by_cases h' : P = S1.biUnion tokE
    · rw [if_pos h', zero_add, h', charge_biUnion χ q S1 tokE hdis]
    · rw [if_neg h', h, charge_union χ q ((hreal.avoid_biUnion hS1).mono_right hOA).symm,
        charge_biUnion χ q S1 tokE hdis]

/-- A charge vanishing on the old piece and on every token vanishes on the new piece. -/
theorem charge_newPiece_eq_zero {κ : Type*} {s : ℕ} (χ : Fin s → Fin s → ℤ) (q : W → Fin s)
    {S : Finset (Tok κ)} {tokE : Tok κ → Finset (Sym2 W)} {A : Finset (Sym2 W)}
    {t' : ℕ} {χ0 χ1 : Fin t' → Fin t' → ℤ} {p0 : W → Fin t'} {u : ℤ} {g : ℕ}
    (hreal : TokReal χ0 χ1 p0 u g A S tokE) {P O : Finset (Sym2 W)} {S1 : Finset (Tok κ)}
    (hS1 : S1 ⊆ S) (hOA : O ⊆ A)
    (hshape : P = S1.biUnion tokE ∨ P = O ∪ S1.biUnion tokE)
    (hO : charge χ q O = 0) (htok : ∀ τ ∈ S1, charge χ q (tokE τ) = 0) :
    charge χ q P = 0 := by
  rw [charge_newPiece χ q hreal hS1 hOA hshape, sum_eq_zero htok, add_zero]
  split_ifs <;> simp [hO]

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.vertex_layer
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.charge_newPiece_eq_zero
