/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.ParAssembly2
public import PartitionedTriangleAbsorption.BlowupB.BalFixer.BalScales

@[expose] public section

set_option exponentiation.threshold 512

/-!
# Split families at the scale `2^L`

* `ComponentCertFlexTL K c k L`: the component certificate on `Fin t` at the scales `FlexScalesL L`.
* `compScalesL`: the scales of a split host with `n ≤ n' ≤ t' n` vertices (`t' ≤ 8`) lose `11` in the
  exponent: `FlexScalesL (L + 11) ω δ ρ n → FlexScalesL L (ωn/n') (δn/t'/n') (ρn/n') n'`.
* `universalCertFlexL_of_split`: the direct branch of `Flex.universalCert_of_split2`, at flexible
  scales: component certificates at `L` give `UniversalCertFlexL F (L + 11)`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.BalFixer

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral VertexSplit
open PaddedGeneral.RealInverse
open PartitionedTriangleAbsorption.BlowupB.Flex

variable {t : ℕ}

/-- The component certificate on `Fin t` at the scale `2^L`. -/
def ComponentCertFlexTL (F : Finset (Multiset (Fin t))) (c : Fin t → Fin t) (k : Fin t) (L : ℕ) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin t)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω δ ρ : ℝ),
    FlexScalesL L ω δ ρ (Fintype.card V) →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
      DegBounded X (2 * ρ * Fintype.card V) → (∀ e ∈ X, VertexSplit.CompT.InsideE p c k e) →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
        (∀ e ∈ A, VertexSplit.CompT.InsideE p c k e) ∧
        HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)

/-- **Scale transfer to a split host.** -/
theorem compScalesL (L : ℕ) (ω δ ρ n n' t' : ℝ) (hfl : FlexScalesL (L + 11) ω δ ρ n)
    (ht1 : 1 ≤ t') (ht8 : t' ≤ 8) (hnn' : n ≤ n') (hn't : n' ≤ t' * n) :
    FlexScalesL L (ω * n / n') (δ * n / t' / n') (ρ * n / n') n' := by
  obtain ⟨hω, hω1, hδ, hδω, hρsq, hn0, hρn⟩ := hfl
  have hρ : 0 < ρ := by
    by_contra h; push Not at h; nlinarith
  have hn : 0 < n := by
    by_contra h; push Not at h; nlinarith
  have hn' : 0 < n' := lt_of_lt_of_le hn hnn'
  set x : ℝ := n / n' with hx
  have hx0 : 0 < x := div_pos hn hn'
  have hx1 : x ≤ 1 := (div_le_one hn').mpr hnn'
  have hx8 : 1 / 8 ≤ x := by
    rw [hx, le_div_iff₀ hn']
    nlinarith
  have e1 : ω * n / n' = ω * x := by rw [hx]; ring
  have e2 : δ * n / t' / n' = δ * x / t' := by rw [hx]; field_simp
  have e3 : ρ * n / n' = ρ * x := by rw [hx]; ring
  rw [e1, e2, e3]
  refine ⟨by positivity, by nlinarith, by positivity, ?_, ?_, hn'.le, ?_⟩
  · -- 2^63 δ' ≤ ω'
    rw [show 2 ^ 63 * (δ * x / t') = (2 ^ 63 * δ) * x / t' by ring, div_le_iff₀ (by linarith)]
    have h1 := mul_le_mul_of_nonneg_right hδω hx0.le
    have h2 : ω * x ≤ ω * x * t' := le_mul_of_one_le_right (by positivity) ht1
    linarith
  · -- the reserve scale
    set P : ℝ := (ω ^ 2 * δ / 2 ^ L) ^ 2 with hP
    have hP0 : 0 ≤ P := sq_nonneg _
    have hA : 2 ^ 24 * ρ ≤ P / 2 ^ 22 := by
      have : (ω ^ 2 * δ / 2 ^ (L + 11)) ^ 2 = P / 2 ^ 22 := by
        rw [hP, pow_add]; field_simp <;> ring
      rw [← this]; exact hρsq
    have hrhs : ((ω * x) ^ 2 * (δ * x / t') / 2 ^ L) ^ 2 = P * x ^ 6 / t' ^ 2 := by
      rw [hP]; field_simp <;> ring
    rw [hrhs]
    have hx5 : (1 / 8 : ℝ) ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx8 5
    have ht2 : t' ^ 2 ≤ 2 ^ 22 * x ^ 5 := by nlinarith
    have hstep : P / 2 ^ 22 * x ≤ P * x ^ 6 / t' ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : P / 2 ^ 22 * x * t' ^ 2 ≤ P / 2 ^ 22 * x * (2 ^ 22 * x ^ 5) :=
        mul_le_mul_of_nonneg_left ht2 (by positivity)
      have e : P / 2 ^ 22 * x * (2 ^ 22 * x ^ 5) = P * x ^ 6 := by field_simp <;> ring
      linarith
    calc 2 ^ 24 * (ρ * x) = (2 ^ 24 * ρ) * x := by ring
      _ ≤ P / 2 ^ 22 * x := mul_le_mul_of_nonneg_right hA hx0.le
      _ ≤ _ := hstep
  · -- ρ' n' = ρ n
    have : ρ * x * n' = ρ * n := by rw [hx]; field_simp
    linarith

set_option maxHeartbeats 4000000 in
/-- **Universal certificate of a split family at flexible scales** (direct components). -/
theorem universalCertFlexL_of_split {t' : ℕ} (F : Finset (Multiset (Fin 4))) (S : SplitData F t')
    (hC : S.Compat) (ht' : 0 < t') (ht'8 : t' ≤ 8)
    (hpair : ∀ i' j' : Fin t', (∃ k', Link S.F' i' j' k') →
      S.cls (S.π i') (S.π j') = i' ∧ S.cls (S.π j') (S.π i') = j')
    (hsurj : ∀ j' : Fin t', ∃ s, S.cls (S.π j') s = j')
    (c' : Fin t' → Fin t') (hc' : CompT.CompLabel S.F' c') (hτ' : CompT.TypesInside S.F' c')
    (L : ℕ)
    (hcomp : ∀ k : Fin t', (∀ i, c' i ≠ k) ∨
      ∃ K : Finset (Multiset (Fin t')), K ⊆ S.F' ∧ (∀ τ ∈ K, ∀ i ∈ τ, c' i = k) ∧
        (∀ τ ∈ S.F', (∀ i ∈ τ, c' i = k) → τ ∈ K) ∧ ComponentCertFlexTL K c' k L) :
    UniversalCertFlexL F (L + 11) := by
  intro V _ _ p G _ ω δ ρ hflL hG hs
  classical
  have hflL' := hflL
  obtain ⟨hω, hω1, hδ, hδω, hρsq, hn0', hρn⟩ := hflL'
  set n : ℝ := (Fintype.card V : ℝ) with hnset
  have hn0 : 0 < n := by
    by_contra h; push Not at h
    have hρ0 : 0 < ρ := by by_contra h'; push Not at h'; nlinarith
    nlinarith
  have ht'R : (0 : ℝ) < t' := by exact_mod_cast ht'
  have ht'8R : (t' : ℝ) ≤ 8 := by exact_mod_cast ht'8
  -- the split host
  have hG' := splitG_allowed S p G hG
  have hs' := guardedSupply_split S p G (2 ^ 21) (ω * n) hs hpair hsurj
  set n' : ℝ := (Fintype.card (SV S p) : ℝ) with hn'set
  have hnn' : n ≤ n' := by rw [hnset, hn'set]; exact_mod_cast card_V_le S p
  have hn'0 : 0 < n' := lt_of_lt_of_le hn0 hnn'
  set R : ℝ := 2 * ρ * n with hR
  set D : ℝ := 2 * δ * n / t' with hD
  have hD0 : 0 ≤ D := by positivity
  -- componentwise absorbers in the split host
  have hk : ∀ k : Fin t', ∀ X : Finset (Sym2 (SV S p)), X ⊆ (splitG S p G).edgeFinset →
      DegBounded X R → (∀ e ∈ X, CompT.InsideE (VertexSplit.sp S p) c' k e) →
      ∃ A : Finset (Sym2 (SV S p)), A ⊆ (splitG S p G).edgeFinset ∧ Disjoint A X ∧
        (∀ e ∈ A, CompT.InsideE (VertexSplit.sp S p) c' k e) ∧ HasDecomp (VertexSplit.sp S p) S.F' A ∧
        DegBounded A D ∧ ∀ L ⊆ X, IsIntDiv (VertexSplit.sp S p) S.F' L → HasDecomp (VertexSplit.sp S p) S.F' (A ∪ L) := by
    intro k X hXG hX hXin
    by_cases hne : ∃ i, c' i = k
    swap
    · -- an empty component
      push Not at hne
      have hX0 : X = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        induction e using Sym2.ind with
        | _ a b => exact hne _ ((CompT.insideE_mk (VertexSplit.sp S p) c' k a b).mp (hXin _ he)).1
      subst hX0
      refine ⟨∅, empty_subset _, disjoint_empty_left _, by simp, hasDecomp_empty_gen _ _,
        fun v => by simpa using hD0, fun L hL _ => ?_⟩
      rw [subset_empty.mp hL, empty_union]
      exact hasDecomp_empty_gen _ _
    obtain ⟨i0, hi0⟩ := hne
    rcases hcomp k with hempty | ⟨K, hKsub, hKin, hKall, hcertK⟩
    · exact absurd hi0 (hempty i0)
    have hn'ne : n' ≠ 0 := hn'0.ne'
    have hSV : n' ≤ t' * n := by
      have h := card_SV_le S p
      have h' : ((Fintype.card (SV S p) : ℕ) : ℝ) ≤ ((t' * Fintype.card V : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at h'
      rw [← hn'set, ← hnset] at h'
      exact h'
    have hn'9 : n' ≤ 9 * n := by nlinarith
    have hωn' : ω * n ≤ n' := by
      have : ω * n ≤ 1 * n := mul_le_mul_of_nonneg_right hω1 hn0.le
      linarith
    have ht1 : (1 : ℝ) ≤ t' := by exact_mod_cast ht'
    have hfl := compScalesL L ω δ ρ n n' t' hflL ht1 ht'8R hnn' hSV
    let Gk : SimpleGraph (SV S p) := SimpleGraph.fromRel fun x y =>
      (splitG S p G).Adj x y ∧ c' (VertexSplit.sp S p x) = k ∧ c' (VertexSplit.sp S p y) = k
    have hGk : ∀ x y, Gk.Adj x y ↔
        (splitG S p G).Adj x y ∧ c' (VertexSplit.sp S p x) = k ∧ c' (VertexSplit.sp S p y) = k := by
      intro x y
      simp only [Gk, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨-, h | ⟨h1, h2, h3⟩⟩
        · exact h
        · exact ⟨h1.symm, h3, h2⟩
      · intro h
        exact ⟨(splitG S p G).ne_of_adj h.1, Or.inl h⟩
    have hGkG : Gk.edgeFinset ⊆ (splitG S p G).edgeFinset := by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact ((hGk x y).mp he).1
    have hinK : ∀ a b l : Fin t', Link S.F' a b l → c' a = k → Link K a b l := by
      intro a b l hl ha
      refine hKall _ hl fun j hj => ?_
      rw [← ha]
      exact hτ' _ hl j a (Multiset.count_pos.mpr hj) (Multiset.count_pos.mpr (by simp))
    have hKcls : ∀ a b l : Fin t', Link K a b l → c' a = k ∧ c' b = k :=
      fun a b l hl => ⟨hKin _ hl a (by simp), hKin _ hl b (by simp)⟩
    have hGK : ∀ u v, Gk.Adj u v → ∃ l, Link K (VertexSplit.sp S p u) (VertexSplit.sp S p v) l := by
      intro u v huv
      obtain ⟨hadj, hu, -⟩ := (hGk u v).mp huv
      obtain ⟨l, hl⟩ := hG' u v hadj
      exact ⟨l, hinK _ _ _ hl hu⟩
    have hsK : GuardedSupply (VertexSplit.sp S p) Gk (fun i j => ∃ l, Link K i j l) (2 ^ 21)
        (ω * n / n' * Fintype.card (SV S p)) := by
      intro T hT i hguard
      have hg' : ∀ u ∈ T, ∃ l, Link S.F' (VertexSplit.sp S p u) i l := by
        intro u hu
        obtain ⟨l, hl⟩ := hguard u hu
        exact ⟨l, hKsub hl⟩
      have h1 := hs' T hT i hg'
      have hsub : guardedNeighbours (VertexSplit.sp S p) (splitG S p G) T i ⊆
          guardedNeighbours (VertexSplit.sp S p) Gk T i := by
        intro w hw
        obtain ⟨hwi, hadj⟩ := (mem_filter.mp hw).2
        refine mem_filter.mpr ⟨mem_univ _, hwi, fun u hu => ?_⟩
        obtain ⟨l, hl⟩ := hguard u hu
        obtain ⟨hu', hi'⟩ := hKcls _ _ _ hl
        exact (hGk u w).mpr ⟨hadj u hu, hu', by rw [hwi]; exact hi'⟩
      have h2 : ((guardedNeighbours (VertexSplit.sp S p) (splitG S p G) T i).card : ℝ) ≤
          (guardedNeighbours (VertexSplit.sp S p) Gk T i).card := by exact_mod_cast card_le_card hsub
      have e : ω * n / n' * Fintype.card (SV S p) = ω * n := by
        rw [← hn'set]; field_simp
      rw [e]
      exact h1.trans h2
    have hXk : X ⊆ Gk.edgeFinset := by
      intro e he
      have heG := hXG he
      have hin := hXin e he
      induction e using Sym2.ind with
      | _ x y =>
        obtain ⟨hx, hy⟩ := (CompT.insideE_mk (VertexSplit.sp S p) c' k x y).mp hin
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heG ⊢
        exact (hGk x y).mpr ⟨heG, hx, hy⟩
    have hXd : DegBounded X (2 * (ρ * n / n') * Fintype.card (SV S p)) := by
      have e : 2 * (ρ * n / n') * Fintype.card (SV S p) = R := by
        rw [← hn'set, hR]; field_simp
      rw [e]; exact hX
    obtain ⟨A, hAk, hAX, hAin, hAdec, hAdeg, hAL⟩ :=
      hcertK (SV S p) (VertexSplit.sp S p) Gk (ω * n / n') (δ * n / t' / n') (ρ * n / n') hfl hGK hsK
        X hXk hXd hXin
    have eD : 2 * (δ * n / t' / n') * Fintype.card (SV S p) = D := by
      rw [← hn'set, hD]; field_simp
    rw [eD] at hAdeg
    refine ⟨A, hAk.trans hGkG, hAX, hAin, hasDecomp_mono (VertexSplit.sp S p) hKsub hAdec, hAdeg, ?_⟩
    intro L hLX hL
    have hLK := isIntDiv_restrict (VertexSplit.sp S p) S.F' K c' k hτ' hKsub hKin hKall L
      (fun e he => hXin e (hLX he)) hL
    exact hasDecomp_mono (VertexSplit.sp S p) hKsub (hAL L hLX hLK)
  -- the union over components, then Theorem B
  have hUA := CompT.universalAbsorbers_of_components S.F' c' hc' hτ' (VertexSplit.sp S p) (splitG S p G) hG'
    (ρ * n / n') (δ * n / t' / n') (by
      intro k X hXG hX hXin
      have e1 : 2 * (ρ * n / n') * n' = R := by rw [hR]; field_simp
      have e2 : 2 * (δ * n / t' / n') * n' = D := by rw [hD]; field_simp
      rw [e1] at hX
      rw [e2]
      exact hk k X hXG hX hXin)
  have hU : ∀ X' : Finset (Sym2 (SV S p)), X' ⊆ (splitG S p G).edgeFinset → DegBounded X' R →
      ∃ A' : Finset (Sym2 (SV S p)), A' ⊆ (splitG S p G).edgeFinset ∧ Disjoint A' X' ∧
        HasDecomp (VertexSplit.sp S p) S.F' A' ∧ DegBounded A' D ∧
        ∀ L' ⊆ X', IsIntDiv (VertexSplit.sp S p) S.F' L' → HasDecomp (VertexSplit.sp S p) S.F' (A' ∪ L') := by
    intro X' hX'G hX'
    have e1 : 2 * (ρ * n / n') * n' = R := by rw [hR]; field_simp
    have e2 : 2 * (δ * n / t' / n') * n' = D := by rw [hD]; field_simp
    obtain ⟨A', h1, h2, h3, h4, h5⟩ := hUA X' hX'G (by rw [e1]; exact hX')
    exact ⟨A', h1, h2, h3, by rw [← e2]; exact h4, h5⟩
  intro X hXG hX
  obtain ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩ := absorbers_of_split_abs S p hC G R D hD0 hU X hXG hX
  have e3 : (t' : ℝ) * D = 2 * δ * n := by rw [hD]; field_simp
  rw [e3] at hAdeg
  exact ⟨A, hAG, hAX, hAdec, hAdeg, hAL⟩

end PartitionedTriangleAbsorption.BlowupB.BalFixer

#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.compScalesL
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.universalCertFlexL_of_split
