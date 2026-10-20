/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RefinerSpec

@[expose] public section

/-! Palette-generic finite-library absorption. The producer is an explicit
balanced-refiner premise; this module supplies the universal absorber consumer,
also for a native three-colour core, without an empty fourth class. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RefinerAbsorber

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedGeneral.RealInverse

def BalancedRefiner {t : ℕ} (F : Finset (Multiset (Fin t))) : Prop :=
  ∃ K M L0 : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω lam rho : ℝ),
    0 < ω → ω ≤ 1 → 0 < lam → 2 ^ L0 * lam ≤ ω ^ 3 → 0 < rho → 2 ^ 24 * rho ≤ lam ^ 2 →
    1 ≤ rho * Fintype.card V →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * rho * Fintype.card V) →
      ∃ (ι : Type) (lib : Finset ι) (B : ι → Finset (Sym2 V)) (R : Finset (Sym2 V)),
        R ⊆ G.edgeFinset ∧ Disjoint R X ∧
        DegBounded R (M * lam * Fintype.card V / ω) ∧
        RefinerAssembly.RefinesReserve (p := p) (F := F) lib B X R ∧
        (∀ i ∈ lib, B i ⊆ X ∪ R ∧ (B i).card ≤ K ∧ IsIntDiv p F (B i)) ∧
        ((lib.card : ℝ) ≤ M * lam * (Fintype.card V : ℝ) ^ 2 / ω) ∧
        ∀ v, ((∑ i ∈ lib, incidentLoad (B i) v : ℕ) : ℝ) ≤ M * lam * Fintype.card V / ω


def UniversalFamilyCert {t : ℕ} (F : Finset (Multiset (Fin t))) (L : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω δ ρ : ℝ),
    FlexScalesL L ω δ ρ (Fintype.card V) →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    UniversalAbsorbers p F G ρ δ

/-- The private step for pieces of size `≤ K` from the terminal hypothesis. -/
theorem privateStep_of_termHyp {t : ℕ} (F : Finset (Multiset (Fin t))) {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (K Cter : ℕ) (hterm : BalFixer.TermHyp F K Cter)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (a T : ℝ) (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a)
    (hT : 0 < T) (hbig : (2 * K + 5 * t : ℝ) + 9 * Cter + 8 * T < a / 2) :
    PrivateStep p F G K (30 * Cter) T (2 * T) a := by
  classical
  intro L hL hLc P hPG hmP hdiv
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ a / 2 := by
    have hc := card_highLoad_le L T
    change (High.card : ℝ) * T ≤ 2 * L.card at hc
    have h1 : (High.card : ℝ) * T ≤ T * a / 2 := by linarith
    have h2 : (High.card : ℝ) * T ≤ (a / 2) * T := by linarith
    exact le_of_mul_le_mul_right h2 hT
  obtain ⟨A, hAG, hAL, -, hAdec, hAPdec, hAcard, hAv, -⟩ :=
    hterm p G a (2 * T) L High hG (hs.mono (by norm_num) le_rfl) hL (by positivity)
      (by push_cast at hbig ⊢; linarith) P hPG hmP hdiv
  refine ⟨A, hAG, hAL, hAdec, hAPdec, hAcard, ?_⟩
  intro v hv
  rcases hAv v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

set_option maxHeartbeats 2000000 in
-- The numerical bookkeeping below uses many `nlinarith` calls in one large context.
/-- **`LatinTarget` from the balanced refiner.** -/
theorem universalCert_of_balancedRefiner {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (h : BalancedRefiner F) :
    ∃ L, UniversalFamilyCert F L := by
  obtain ⟨K, M, L0, href⟩ := h
  obtain ⟨Cter, hterm⟩ := BalFixer.termHyp_of_cert F hF3 K
  set B : ℕ := 2 * K + 5 * t + 129 * Cter + 240 * Cter * M + 8 * M + 8 with hB
  refine ⟨L0 + B, ?_⟩
  intro V _ _ p G _ ω δ ρ hfl hG hs X hXG hX
  obtain ⟨hω, hω1, hδ, hδω, hρsq, hn0, hρn⟩ := hfl
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set L : ℕ := L0 + B with hL
  -- powers of two
  have hBlt : (B : ℝ) < 2 ^ L := by
    have h1 : B < 2 ^ B := Nat.lt_two_pow_self
    have h2 : 2 ^ B ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast lt_of_lt_of_le h1 h2
  have h2L0 : (2 : ℝ) ^ L0 ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2Lpos : (0 : ℝ) < 2 ^ L := by positivity
  have h2L1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  -- basic positivity
  have hρ : 0 < ρ := by
    by_contra hc; push_neg at hc; nlinarith
  have hnpos : 0 < n := by
    by_contra hc; push_neg at hc; nlinarith
  have hδ1 : δ ≤ 1 := by nlinarith
  have hδω' : δ ≤ ω := by nlinarith
  set lam : ℝ := ω ^ 2 * δ / 2 ^ L with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamδ : lam * 2 ^ L ≤ δ := by
    rw [hlam, div_mul_cancel₀ _ h2Lpos.ne']
    have : ω ^ 2 ≤ 1 := pow_le_one₀ hω.le hω1
    nlinarith
  have hlamL0 : 2 ^ L0 * lam ≤ ω ^ 3 := by
    have h1 : 2 ^ L0 * lam ≤ 2 ^ L * lam := mul_le_mul_of_nonneg_right h2L0 hlam0.le
    have h2 : 2 ^ L * lam = ω ^ 2 * δ := by rw [hlam]; field_simp
    have h3 : ω ^ 2 * δ ≤ ω ^ 2 * ω := mul_le_mul_of_nonneg_left hδω' (by positivity)
    nlinarith
  have hscale : 2 ^ 24 * ρ ≤ lam ^ 2 := hρsq
  -- `n` is large: `δ n ≥ 2^L` (indeed `≥ 2^(2L)`)
  have hlamn : 2 ^ 24 ≤ lam ^ 2 * n := by nlinarith
  have hδn : (2 : ℝ) ^ L ≤ δ * n := by
    -- `δ n ≥ 2^L lam n` and `lam n ≥ 2^24 / lam ≥ 1`
    have hlam1 : lam ≤ 1 := by nlinarith
    have hln : 1 ≤ lam * n := by nlinarith
    have : 2 ^ L * (lam * n) ≤ δ * n := by nlinarith
    nlinarith
  have hωn : δ * n ≤ ω * n := by nlinarith
  -- the refiner
  obtain ⟨ι, lib, Bp, R, hRG, hRX, hRdeg, hrefines, hpieces, hlibcard, hload⟩ :=
    href V p G ω lam ρ hω hω1 hlam0 hlamL0 hρ hscale hρn hG hs X hXG hX
  set D0 : ℝ := M * lam * n / ω with hD0
  have hD0nn : 0 ≤ D0 := by positivity
  -- the private step
  have hstep : PrivateStep p F G K (30 * Cter) (δ * n) (2 * δ * n) (ω * n) := by
    have h := privateStep_of_termHyp F p G K Cter hterm hG (ω * n) (δ * n) hs (by positivity) ?_
    · simpa only [mul_assoc] using h
    have hK : (2 * K + 5 * t : ℝ) + 9 * Cter < 2 ^ L := by
      have : ((2 * K + 5 * t + 9 * Cter : ℕ) : ℝ) ≤ B := by
        exact_mod_cast (show 2 * K + 5 * t + 9 * Cter ≤ B by omega)
      push_cast at this; linarith
    have h8 : 8 * (δ * n) ≤ ω * n / 4 := by nlinarith
    have : (2 : ℝ) ^ L ≤ ω * n / 4 := by nlinarith
    linarith
  -- numerical facts about `D0`
  have hc8 : (8 * (M * (1 + 30 * Cter)) : ℝ) < 2 ^ L := by
    have : ((8 * M + 240 * Cter * M : ℕ) : ℝ) ≤ B := by
      exact_mod_cast (show 8 * M + 240 * Cter * M ≤ B by omega)
    push_cast at this; nlinarith
  have hD0eq : D0 * 2 ^ L = M * ω * (δ * n) := by
    rw [hD0, hlam]; field_simp
  have hD0small : D0 * (1 + 30 * Cter) ≤ ω * (δ * n) / 8 := by
    have hCnn : (0 : ℝ) ≤ Cter := Nat.cast_nonneg _
    have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hωδn : 0 ≤ ω * (δ * n) := by positivity
    have h1 : D0 * (1 + 30 * Cter) * 2 ^ L = (M * (1 + 30 * Cter)) * (ω * (δ * n)) := by
      rw [show D0 * (1 + 30 * Cter) * 2 ^ L = D0 * 2 ^ L * (1 + 30 * Cter) by ring, hD0eq]; ring
    have h2 : (M * (1 + 30 * Cter)) * (ω * (δ * n)) * 8 ≤ 2 ^ L * (ω * (δ * n)) :=
      by nlinarith
    have h3 : D0 * (1 + 30 * Cter) * 2 ^ L * 8 ≤ (ω * (δ * n)) * 2 ^ L := by nlinarith
    nlinarith
  have hCter : (30 * Cter : ℝ) ≤ δ * n / 4 := by
    have : ((120 * Cter : ℕ) : ℝ) ≤ B := by
      exact_mod_cast (show 120 * Cter ≤ B by omega)
    push_cast at this; linarith
  have hρδ : ρ * 2 ^ 24 ≤ ω * δ := by
    have h1 : (ω ^ 2 * δ / 2 ^ L) ^ 2 ≤ ω * δ := by
      have ha : 0 ≤ ω ^ 2 * δ / 2 ^ L := by positivity
      have hb : ω ^ 2 * δ / 2 ^ L ≤ ω * δ := by
        rw [div_le_iff₀ h2Lpos]
        have h1 : ω ^ 2 * δ ≤ ω * δ := by
          have hωδ : 0 ≤ ω * δ := by positivity
          calc ω ^ 2 * δ = ω * (ω * δ) := by ring
            _ ≤ 1 * (ω * δ) := mul_le_mul_of_nonneg_right hω1 hωδ
            _ = ω * δ := one_mul _
        have h2 : ω * δ ≤ ω * δ * 2 ^ L := le_mul_of_one_le_right (by positivity) h2L1
        linarith
      have hc : ω * δ ≤ 1 := by nlinarith
      nlinarith
    linarith
  -- the assembly
  have hRdeg' : DegBounded R D0 := hRdeg
  have hledger : DegBounded (X ∪ R) (2 * ρ * n + D0) := degBounded_union hX hRdeg'
  have hD : max (2 * ρ * n + D0) (δ * n + ((30 * Cter : ℕ) : ℝ)) +
      ((30 * Cter : ℕ) : ℝ) * D0 ≤ 2 * δ * n := by
    push_cast
    have hρn' : 2 * ρ * n ≤ δ * n / 4 := by nlinarith
    have hD0' : D0 ≤ δ * n / 8 := by nlinarith
    have hCD : 30 * Cter * D0 ≤ δ * n / 8 := by nlinarith
    rcases le_total (2 * ρ * n + D0) (δ * n + 30 * Cter) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hcount : 4 * (((X ∪ R).card : ℝ) + lib.card * ((30 * Cter : ℕ) : ℝ)) ≤
      (δ * n) * (ω * n) := by
    have hXR := FiniteLibrary.card_le_order_mul_degree (X ∪ R) _ hledger
    rw [← hn] at hXR
    have hlib : (lib.card : ℝ) ≤ n * D0 := by
      rw [hD0]; rw [← hn] at hlibcard
      calc (lib.card : ℝ) ≤ M * lam * n ^ 2 / ω := hlibcard
        _ = n * (M * lam * n / ω) := by ring
    push_cast
    have hCnn : (0 : ℝ) ≤ Cter := Nat.cast_nonneg _
    have h1 : (lib.card : ℝ) * (30 * Cter) ≤ n * D0 * (30 * Cter) :=
      mul_le_mul_of_nonneg_right hlib (by positivity)
    have h2 : n * (2 * ρ * n + D0) + n * D0 * (30 * Cter) =
        n * (2 * ρ * n + D0 * (1 + 30 * Cter)) := by ring
    have h3 : 2 * ρ * n + D0 * (1 + 30 * Cter) ≤ ω * (δ * n) / 4 := by nlinarith
    have h4 : n * (2 * ρ * n + D0 * (1 + 30 * Cter)) ≤ n * (ω * (δ * n) / 4) :=
      mul_le_mul_of_nonneg_left h3 hnpos.le
    nlinarith
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩ :=
    FiniteLibrary.universal_from_finite_library p F G K (30 * Cter) (δ * n) (2 * δ * n) D0
      (2 * ρ * n + D0) (ω * n) hstep X R hRX hXG hRG hledger hD lib Bp hrefines
      (fun i hi => (hpieces i hi).1) (fun i hi => (hpieces i hi).2.1)
      (fun i hi => (hpieces i hi).2.2) hload hcount
  exact ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩


end PartitionedTriangleAbsorption.BlowupB.LatinCore.RefinerAbsorber

