/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Library
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Target A forces a linear bounded-geometry filling

`cycleShortener_linearFilling`: if target A holds with constants `C0, K`, then for every `Y`
(cyclically tripartite, maximum degree `≤ 17`) there is a supergraph `Z ⊇ Y` of maximum degree
`≤ C0 + 17` and at most `C1 |Y|` arcs, and a family `𝒞` of at most `C1 |Y|` directed simple cycles
of `Z` of length `≤ K`, such that every balanced `L ⊆ Y` is an integer combination, with
coefficients in `{-1, 0, 1}`, of the cycles of `𝒞` (as arc indicator vectors). Here
`C1 = (C0 + 1) 2 ^ ((C0+17)(C0+18)^K)` depends only on `C0` and `K`.

So target A contains, as a purely homological shadow, a *linear-size bounded-geometry filling*
of all directed cycles of every bounded-degree cyclically tripartite digraph (for strongly
connected `Y` these span its whole integral cycle space). The one-hub shortener
(`HubShortener.lean`) shows that this shadow is trivial once a single vertex of unbounded degree
is allowed (a cone).

The library `𝒞` is the family of *all* short directed cycles of `Z`, so this file is also the
formal version of section B of the crux file: a separate library producer is unnecessary.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

section Aux

variable {W : Type*} [DecidableEq W]

lemma inDeg_union_le (A B : Finset (W × W)) (v : W) : inDeg (A ∪ B) v ≤ inDeg A v + inDeg B v := by
  unfold inDeg; rw [Finset.filter_union]; exact Finset.card_union_le _ _

lemma outDeg_union_le (A B : Finset (W × W)) (v : W) :
    outDeg (A ∪ B) v ≤ outDeg A v + outDeg B v := by
  unfold outDeg; rw [Finset.filter_union]; exact Finset.card_union_le _ _

lemma maxDegLE_union {A B : Finset (W × W)} {a b : ℕ} (hA : MaxDegLE A a) (hB : MaxDegLE B b) :
    MaxDegLE (A ∪ B) (a + b) := by
  intro v
  have h1 := inDeg_union_le A B v
  have h2 := outDeg_union_le A B v
  have h3 := hA v
  have h4 := hB v
  unfold deg at *
  omega

/-- In a partition, every arc of the partitioned set lies in exactly one piece. -/
lemma IsCyclePartition.count {K : ℕ} {P : Finset (Finset (W × W))} {E : Finset (W × W)}
    (hP : IsCyclePartition K P E) (a : W × W) :
    ∑ p ∈ P, (if a ∈ p then (1 : ℤ) else 0) = if a ∈ E then 1 else 0 := by
  obtain ⟨-, hdisj, hunion⟩ := hP
  rw [Finset.sum_boole]
  split_ifs with ha
  · rw [← hunion] at ha
    obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.1 ha
    have : P.filter (fun q => a ∈ q) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, haq⟩
        by_contra hne
        exact Finset.disjoint_left.1 (hdisj hq hp hne) haq hap
      · rintro rfl; exact ⟨hp, hap⟩
    rw [this]; simp
  · have : P.filter (fun q => a ∈ q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq haq
      exact ha (hunion ▸ Finset.mem_biUnion.2 ⟨q, hq, haq⟩)
    rw [this]; simp

end Aux

lemma inDeg_map_liftArc {V U : Type*} [DecidableEq V] [DecidableEq U] (Y : Finset (V × V))
    (x : V ⊕ U) : inDeg (Y.map (liftArc V U)) x = Sum.elim (inDeg Y) (fun _ => 0) x := by
  unfold inDeg
  rw [Finset.filter_map, Finset.card_map]
  rcases x with v | u
  · congr 1
    ext e
    simp only [Finset.mem_filter, Function.comp_apply]
    change (e ∈ Y ∧ (Sum.inl e.2 : V ⊕ U) = Sum.inl v) ↔ (e ∈ Y ∧ e.2 = v)
    simp only [Sum.inl.injEq]
  · simp [liftArc, Function.comp_def]

lemma outDeg_map_liftArc {V U : Type*} [DecidableEq V] [DecidableEq U] (Y : Finset (V × V))
    (x : V ⊕ U) : outDeg (Y.map (liftArc V U)) x = Sum.elim (outDeg Y) (fun _ => 0) x := by
  unfold outDeg
  rw [Finset.filter_map, Finset.card_map]
  rcases x with v | u
  · congr 1
    ext e
    simp only [Finset.mem_filter, Function.comp_apply]
    change (e ∈ Y ∧ (Sum.inl e.1 : V ⊕ U) = Sum.inl v) ↔ (e ∈ Y ∧ e.1 = v)
    simp only [Sum.inl.injEq]
  · simp [liftArc, Function.comp_def]

lemma maxDegLE_map_liftArc {V U : Type*} [DecidableEq V] [DecidableEq U] {Y : Finset (V × V)}
    {d : ℕ} (hY : MaxDegLE Y d) : MaxDegLE (Y.map (liftArc V U)) d := by
  intro x
  unfold deg
  rw [inDeg_map_liftArc, outDeg_map_liftArc]
  rcases x with v | u
  · exact hY v
  · simp

/-- **Linear bounded-geometry filling** with constants `C1` (size), `D` (degree), `K` (cell
length): the homological shadow of target A. -/
def LinearFillingWith (C1 D K : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → ZMod 3) (Y : Finset (V × V)),
    IsCyc c Y → MaxDegLE Y 17 →
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (Z : Finset ((V ⊕ U) × (V ⊕ U)))
      (𝒞 : Finset (Finset ((V ⊕ U) × (V ⊕ U)))),
      Y.map (liftArc V U) ⊆ Z ∧ MaxDegLE Z D ∧ Z.card ≤ C1 * Y.card ∧
      𝒞.card ≤ C1 * Y.card ∧ (∀ p ∈ 𝒞, IsDirCycle p ∧ p ⊆ Z ∧ p.card ≤ K) ∧
      ∀ L ⊆ Y, Balanced L → ∃ x : Finset ((V ⊕ U) × (V ⊕ U)) → ℤ,
        (∀ p, x p = -1 ∨ x p = 0 ∨ x p = 1) ∧
        ∀ a, (if a ∈ L.map (liftArc V U) then (1 : ℤ) else 0) =
          ∑ p ∈ 𝒞, x p * (if a ∈ p then 1 else 0)

/-- **Target A implies a linear bounded-geometry filling.** -/
theorem cycleShortener_linearFilling {C0 K : ℕ} (hA : CycleShortenerWith C0 K) :
    LinearFillingWith ((C0 + 1) * 2 ^ ((C0 + 17) * (C0 + 17 + 1) ^ K)) (C0 + 17) K := by
  classical
  intro V _ _ c Y hY hYdeg
  obtain ⟨U, _, _, cU, R, -, hRY, hRcard, hRdeg, hpart⟩ := hA V c Y hY hYdeg
  set Ym := Y.map (liftArc V U) with hYm
  set Z := R ∪ Ym with hZ
  have hZdeg : MaxDegLE Z (C0 + 17) := maxDegLE_union hRdeg (maxDegLE_map_liftArc hYdeg)
  have hZcard : Z.card ≤ (C0 + 1) * Y.card := by
    calc Z.card ≤ R.card + Ym.card := Finset.card_union_le _ _
      _ ≤ C0 * Y.card + Y.card := by rw [hYm, Finset.card_map]; omega
      _ = (C0 + 1) * Y.card := by ring
  set 𝒞 := Z.powerset.filter (fun p => IsDirCycle p ∧ p.card ≤ K) with h𝒞
  have h𝒞prop : ∀ p ∈ 𝒞, IsDirCycle p ∧ p ⊆ Z ∧ p.card ≤ K := by
    intro p hp
    obtain ⟨hpZ, hcyc, hK⟩ := by simpa [h𝒞] using hp
    exact ⟨hcyc, hpZ, hK⟩
  have hpos : 1 ≤ 2 ^ ((C0 + 17) * (C0 + 17 + 1) ^ K) := Nat.one_le_two_pow
  refine ⟨U, inferInstance, inferInstance, Z, 𝒞, Finset.subset_union_right, hZdeg, ?_, ?_,
    h𝒞prop, ?_⟩
  · calc Z.card ≤ (C0 + 1) * Y.card := hZcard
      _ ≤ (C0 + 1) * 2 ^ ((C0 + 17) * (C0 + 17 + 1) ^ K) * Y.card := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpos)
  · calc 𝒞.card ≤ 2 ^ ((C0 + 17) * (C0 + 17 + 1) ^ K) * Z.card :=
          card_cycles_le hZdeg 𝒞 h𝒞prop
      _ ≤ 2 ^ ((C0 + 17) * (C0 + 17 + 1) ^ K) * ((C0 + 1) * Y.card) :=
          Nat.mul_le_mul_left _ hZcard
      _ = (C0 + 1) * 2 ^ ((C0 + 17) * (C0 + 17 + 1) ^ K) * Y.card := by ring
  · intro L hLY hLb
    obtain ⟨PL, hPL⟩ := hpart L hLY hLb
    obtain ⟨P0, hP0⟩ := hpart ∅ (Finset.empty_subset _) balanced_empty
    have hsub : ∀ {P : Finset (Finset ((V ⊕ U) × (V ⊕ U)))} {E : Finset (V × V)}, E ⊆ Y →
        IsCyclePartition K P (R ∪ E.map (liftArc V U)) → P ⊆ 𝒞 := by
      intro P E hE hP p hp
      have hpE : p ⊆ R ∪ E.map (liftArc V U) := by
        rw [← hP.2.2]; exact Finset.subset_biUnion_of_mem id hp
      have hpZ : p ⊆ Z := hpE.trans (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.map_subset_map.2 hE))
      simp only [h𝒞, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hpZ, (hP.1 p hp).1, (hP.1 p hp).2⟩
    have hPL𝒞 := hsub hLY hPL
    have hP0𝒞 := hsub (Finset.empty_subset _) hP0
    refine ⟨fun p => (if p ∈ PL then 1 else 0) - (if p ∈ P0 then 1 else 0), ?_, ?_⟩
    · intro p
      dsimp only
      split_ifs <;> simp
    · intro a
      have hcount : ∀ {P : Finset (Finset ((V ⊕ U) × (V ⊕ U)))} {E}, P ⊆ 𝒞 →
          IsCyclePartition K P E →
          ∑ p ∈ 𝒞, (if p ∈ P then (1 : ℤ) else 0) * (if a ∈ p then 1 else 0) =
            if a ∈ E then 1 else 0 := by
        intro P E hP𝒞 hP
        rw [← hP.count a]
        simp only [ite_mul, one_mul, zero_mul]
        rw [← Finset.sum_filter]
        congr 1
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hP𝒞 h, h⟩⟩
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [hcount hPL𝒞 hPL, hcount hP0𝒞 hP0]
      have hdisj : a ∈ L.map (liftArc V U) → a ∉ R := fun ha haR =>
        Finset.disjoint_left.1 hRY haR (Finset.map_subset_map.2 hLY ha)
      by_cases haL : a ∈ L.map (liftArc V U)
      · simp [haL, hdisj haL]
      · by_cases haR : a ∈ R <;> simp [haL, haR]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
