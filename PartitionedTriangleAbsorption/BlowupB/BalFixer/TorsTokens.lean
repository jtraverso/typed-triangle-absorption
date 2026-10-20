/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.BalFixer.ChiTokens
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.TorsInside
public import PartitionedTriangleAbsorption.BlowupB.TorsionQ.Refiner

@[expose] public section

/-!
# The torsion value and its tokens

For a class-pair weight `ψ`, a divisor `g0` and a modulus `q`, the good sets are the loopless even edge
sets with `3 ∣ |A|` and `g0 ∣ charge ψ p A`; the value is `(charge ψ p A / g0) mod q`. This is a
`TorsionQ.QEvaluation`, so `TorsionQ.torsion_layerQ` applies. `host_tors_tokens` realizes value-one
tokens from one template by guarded embeddings.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.BlowupB.VertexSplit

variable {t : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- The good sets of the torsion layer. -/
abbrev TGood (p : V → Fin t) (ψ : Fin t → Fin t → ℤ) (g0 : ℤ) (A : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ A, ¬ e.IsDiag) ∧ (∀ v, Even (incidentLoad A v)) ∧ 3 ∣ A.card ∧ g0 ∣ charge ψ p A

/-- The torsion value. -/
def tval (p : V → Fin t) (ψ : Fin t → Fin t → ℤ) (g0 : ℤ) (q : ℕ) (A : Finset (Sym2 V)) : ℕ :=
  ((charge ψ p A / g0) % (q : ℤ)).toNat

theorem toNat_add_emod (q : ℕ) (X Y : ℤ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ((X + Y) % (q : ℤ)).toNat = (X.toNat + Y.toNat) % q := by
  have h : (((X.toNat + Y.toNat) % q : ℕ) : ℤ) = (X + Y) % (q : ℤ) := by
    rw [Int.natCast_emod, Nat.cast_add, Int.toNat_of_nonneg hX, Int.toNat_of_nonneg hY]
  rw [← h, Int.toNat_natCast]

/-- **The torsion evaluation.** -/
def tEval (p : V → Fin t) (ψ : Fin t → Fin t → ℤ) (g0 : ℤ) (q : ℕ) (hq : 0 < q) :
    TorsionQ.QEvaluation q (TGood p ψ g0) where
  empty_good := ⟨by simp, fun v => by simp [incidentLoad], by simp, by simp [charge_empty]⟩
  union_good := by
    intro A B hAB hA hB
    refine ⟨fun e he => ?_, fun v => ?_, ?_, ?_⟩
    · rcases mem_union.mp he with h | h
      · exact hA.1 e h
      · exact hB.1 e h
    · rw [incidentLoad_union_of_disjoint hAB]; exact (hA.2.1 v).add (hB.2.1 v)
    · rw [card_union_of_disjoint hAB]; exact dvd_add hA.2.2.1 hB.2.2.1
    · rw [charge_union ψ p hAB]; exact dvd_add hA.2.2.2 hB.2.2.2
  value := tval p ψ g0 q
  value_lt := by
    intro A _
    unfold tval
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    rw [Int.toNat_lt (Int.emod_nonneg _ hq'.ne')]
    exact Int.emod_lt_of_pos _ hq'
  empty_value := by simp [tval, charge_empty]
  union_value := by
    intro A B hAB hA hB
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    unfold tval
    rw [charge_union ψ p hAB, Int.add_ediv_of_dvd_left hA.2.2.2, Int.add_emod,
      toNat_add_emod q _ _ (Int.emod_nonneg _ hq'.ne') (Int.emod_nonneg _ hq'.ne')]

theorem tval_eq_zero_of_dvd (p : V → Fin t) (ψ : Fin t → Fin t → ℤ) {g0 : ℤ} (hg0 : g0 ≠ 0)
    (q : ℕ) {A : Finset (Sym2 V)} (h : g0 * q ∣ charge ψ p A) : tval p ψ g0 q A = 0 := by
  obtain ⟨m, hm⟩ := h
  unfold tval
  rw [hm, mul_assoc, Int.mul_ediv_cancel_left _ hg0, Int.mul_emod_right]
  rfl

theorem dvd_of_tval_eq_zero (p : V → Fin t) (ψ : Fin t → Fin t → ℤ) {g0 : ℤ} (q : ℕ) (hq : 0 < q)
    {A : Finset (Sym2 V)} (hg : g0 ∣ charge ψ p A) (h : tval p ψ g0 q A = 0) :
    g0 * q ∣ charge ψ p A := by
  unfold tval at h
  obtain ⟨m, hm⟩ := hg
  rcases eq_or_ne g0 0 with h0 | h0
  · subst h0; exact ⟨0, by rw [hm]; ring⟩
  have h1 : (charge ψ p A / g0) = m := by rw [hm, Int.mul_ediv_cancel_left _ h0]
  rw [h1] at h
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have h2 : m % (q : ℤ) = 0 := by
    have := Int.emod_nonneg m hq0
    omega
  obtain ⟨r, hr⟩ := Int.dvd_of_emod_eq_zero h2
  exact ⟨r, by rw [hm, hr]; ring⟩

/-- **Value-one torsion tokens.** -/
theorem host_tors_tokens (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t)
    (Tq : FinT.Template F c k) (ψ : Fin t → Fin t → ℤ) (g0 : ℤ) (q : ℕ) (hq : 0 < q)
    (h3 : 3 ∣ Tq.E.card) (hg : g0 ∣ charge ψ Tq.L Tq.E)
    (hv : (charge ψ Tq.L Tq.E / g0) % (q : ℤ) = 1)
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset TorsionQ.Atom) (B : Finset (Sym2 V)) (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 6 (ω * Fintype.card V))
    (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (S.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ tok : TorsionQ.Atom → Finset (Sym2 V), TorsionQ.QTokenReal (tEval p ψ g0 q hq) B S tok ∧
      (∀ a ∈ S, (tok a).card ≤ 6) ∧ (∀ a ∈ S, tok a ⊆ G.edgeFinset) ∧
      (∀ v, ((∑ a ∈ S, incidentLoad (tok a) v : ℕ) : ℝ) ≤ lam * Fintype.card V) ∧
      ∀ a ∈ S, ∀ e ∈ tok a, CompT.InsideE p c k e := by
  obtain ⟨f, hf, hload⟩ := guarded_template_family_scaled p G (fun i j => ∃ k, Link F i j k)
    S (fun _ => Tq.E) (fun _ => Tq.L) (fun _ _ => Tq.loop) (fun _ _ => Tq.act) (fun _ _ => Tq.card)
    ω lam rho hs B hB hω hlam hlamω hrho hscale hn1 hcount
  have hch : ∀ a ∈ S, charge ψ p (mapped Tq.E (f a)) = charge ψ Tq.L Tq.E := fun a ha => by
    change charge ψ p (Tq.E.image (Sym2.map (f a))) = _
    exact PaddedF12.charge_image (f a) (hf.injective a ha) p Tq.L (hf.labels a ha) Tq.E ψ
  refine ⟨fun a => mapped Tq.E (f a), ⟨hf.disjoint, hf.avoid, fun a ha => ?_, fun a ha => ?_⟩,
    fun a _ => card_image_le.trans Tq.card, hf.subgraph, hload, ?_⟩
  · refine ⟨PaddedF12.loopless_image (f a) (hf.injective a ha) Tq.E Tq.loop,
      PaddedF12.even_image (f a) (hf.injective a ha) Tq.E Tq.even, ?_, by rw [hch a ha]; exact hg⟩
    change 3 ∣ (Tq.E.image (Sym2.map (f a))).card
    rw [card_image_of_injective _ (Sym2.map.injective (hf.injective a ha))]
    exact h3
  · change tval p ψ g0 q (mapped Tq.E (f a)) = 1
    unfold tval
    rw [hch a ha, hv]
    rfl
  · intro a ha e he
    obtain ⟨e0, -, rfl⟩ := Finset.mem_image.mp he
    induction e0 using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, CompT.insideE_mk, hf.labels a ha x, hf.labels a ha y]
      exact ⟨Tq.inside x, Tq.inside y⟩

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.tEval
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.host_tors_tokens
