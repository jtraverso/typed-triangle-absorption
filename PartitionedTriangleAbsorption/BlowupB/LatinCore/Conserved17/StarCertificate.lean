/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.CompBal

@[expose] public section

/-! A checked collection of BAL ingredients gives an actual component certificate.
The terminal is constructed by the existing finite certificate theorem, not assumed. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open VertexSplit BalFixer

structure StarCertificateData {t : ℕ} (F : Finset (Multiset (Fin t)))
    (c : Fin t → Fin t) (k : Fin t) where
  comp : CompT.CompLabel F c
  card : ∀ τ ∈ F, τ.card = 3
  walk : FinT.LocalWalk F c k
  σ : Fin t → Fin t → ℤ
  balanced : Finset (Fin t)
  local_sol : LocalSol F σ balanced
  scalar : ∀ u, BalScalarHyp F σ balanced (fun _ _ => 0) u →
    FinT.CountsInside c k u → ∃ w, FinT.LatEq F u w
  kill : ∀ r ∈ balanced, ∀ τ ∈ F, r ∈ τ → ∑ i, σ r i * typeDegVec τ r i = 0
  odd : ∀ r ∈ balanced, ∀ j, (∃ l, Link F r j l) → Odd (σ r j)
  bound : ∀ r j, |σ r j| ≤ 1
  m : ℕ
  g : ℕ
  plus : Fin t → RootedTemplate t m g
  minus : Fin t → RootedTemplate t m g
  modulus : ℕ
  modulus_three : modulus ∣ 3
  plus_ok : ∀ r ∈ balanced, c r = k →
    BalTemplate (fun i j => ∃ l, Link F i j l) c k σ r (plus r) 2 modulus
  minus_ok : ∀ r ∈ balanced, c r = k →
    BalTemplate (fun i j => ∃ l, Link F i j l) c k σ r (minus r) (-2) modulus
  three : ∀ {W : Type} [Fintype W] [DecidableEq W] (q : W → Fin t)
    (E : Finset (Sym2 W)), (∀ e ∈ E, ¬ e.IsDiag) →
    TypedDivisibilityCollapse.ActiveEdges F q E →
    (∀ e ∈ E, CompT.InsideE q c k e) →
    (∀ v, Even (AntiEdgeSelection.incidentLoad E v)) →
    (∀ v, q v ∈ balanced → vcharge (σ (q v)) q v E = 0) →
    modulus ∣ E.card → 3 ∣ E.card
  small : m + 1 ≤ 2 ^ 21

theorem StarCertificateData.exists_certificate {t : ℕ}
    {F : Finset (Multiset (Fin t))} {c : Fin t → Fin t} {k : Fin t}
    (d : StarCertificateData F c k) :
    ∃ L, ComponentCertFlexTL F c k L := by
  classical
  obtain ⟨C, hC⟩ := termHyp_of_cert F d.card (168 + d.g * 168)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt
    ((2 : ℝ) ^ 40 * ((30 * C + 1) * (d.g + 1) * (d.m + 2) * (t + 1)))
    (by norm_num : (1 : ℝ) < 2)
  exact ⟨L, componentCertFlexTL_of_bal F c k d.comp d.card d.walk d.σ d.balanced
    d.local_sol d.scalar d.kill d.odd d.bound d.plus d.minus d.modulus
    d.modulus_three d.plus_ok d.minus_ok d.three d.small C hC L hL.le⟩

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.StarCertificateData.exists_certificate

