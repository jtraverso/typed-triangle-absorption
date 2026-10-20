/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.ParAssembly
public import PartitionedTriangleAbsorption.BlowupB.Flex.Restrict
public import PartitionedTriangleAbsorption.BlowupB.FinT.Cert

@[expose] public section

set_option exponentiation.threshold 512

/-!
# Universal certificates for split families with components on more than four classes

`universalCert_of_split2`: as `universalCert_of_split`, where a component of the split family may also
be served by a direct flexible certificate on `Fin t'` for its subfamily `K` (types inside the
component), applied in the split host restricted to the edges inside the component.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral VertexSplit

/-- **Universal certificate of a split family** (components covered by a family on `Fin 4`, or with a
direct certificate on `Fin t'`). -/
theorem universalCert_of_split2 {t' : ℕ} (F : Finset (Multiset (Fin 4))) (S : SplitData F t')
    (hC : S.Compat) (ht' : 0 < t') (ht'8 : t' ≤ 8)
    (hpair : ∀ i' j' : Fin t', (∃ k', Link S.F' i' j' k') →
      S.cls (S.π i') (S.π j') = i' ∧ S.cls (S.π j') (S.π i') = j')
    (hsurj : ∀ j' : Fin t', ∃ s, S.cls (S.π j') s = j')
    (c' : Fin t' → Fin t') (hc' : CompT.CompLabel S.F' c') (hτ' : CompT.TypesInside S.F' c')
    (hcomp : ∀ k : Fin t', (∀ i, c' i ≠ k) ∨
      (∃ (Fc : Finset (Multiset (Fin 4))) (cc : Fin 4 → Fin 4) (kc : Fin 4),
        PaddedComponents.CompLabel Fc cc ∧ PaddedComponents.TypesInside Fc cc ∧
        Nonempty (CompIso S.F' c' k Fc cc kc) ∧ ComponentUniversalCertFlex Fc cc kc) ∨
      ∃ K : Finset (Multiset (Fin t')), K ⊆ S.F' ∧ (∀ τ ∈ K, ∀ i ∈ τ, c' i = k) ∧
        (∀ τ ∈ S.F', (∀ i ∈ τ, c' i = k) → τ ∈ K) ∧ FinT.ComponentUniversalCertFlexT K c' k) :
    UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  classical
  have hδdef : paddedAbsDelta ω = ω ^ 12 / 2 ^ 63 := by
    unfold paddedAbsDelta paddedKappa; ring
  have hρdef : paddedRho ω = ω ^ 26 / 2 ^ 262 := rfl
  set ρ := paddedRho ω with hρset
  set δ := paddedAbsDelta ω with hδset
  set n : ℝ := (Fintype.card V : ℝ) with hnset
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hω26 : ω ^ 26 ≤ 1 := pow_le_one₀ hω.le hω1
  have hnbig : 2 ^ 262 ≤ n := by
    have h1 : ρ * n ≤ n / 2 ^ 262 := by
      rw [hρdef]
      have hn0 : 0 ≤ n := Nat.cast_nonneg _
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have h2 := hn.trans h1
    rwa [le_div_iff₀ (by positivity), one_mul] at h2
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hnbig
  have ht'R : (0 : ℝ) < t' := by exact_mod_cast ht'
  have ht'8R : (t' : ℝ) ≤ 8 := by exact_mod_cast ht'8
  have h12 : ω ^ 12 ≤ ω := pow_le_of_le_one hω.le hω1 (by norm_num)
  have hsqρ : (ω * δ / 2 ^ 48) ^ 2 = 2 ^ 40 * ρ := by rw [hδdef, hρdef]; ring
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
    rcases hcomp k with hempty | hrest
    · exact absurd hi0 (hempty i0)
    rcases hrest with ⟨Fc, cc, kc, hcc, hτc, ⟨I⟩, hcert⟩ | ⟨K, hKsub, hKin, hKall, hcertK⟩
    swap
    · -- a component with a direct certificate on `Fin t'`
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
      have hfl := par_component_scales ω n n' t' ρ δ hω hω1 hδdef hρdef ht1 ht'8R hn hn0 hωn' hn'9
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
    set M : ℕ := Fintype.card V + 2 ^ 21 with hM
    have hMR : (M : ℝ) = n + 2 ^ 21 := by rw [hM, hnset]; push_cast; ring
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ,
        (Fintype.card (WC cc kc M (W := {x : SV S p // c' (VertexSplit.sp S p x) = k})) : ℝ) = N := ⟨_, rfl⟩
    -- size of the completed component host
    have hNsum : N = (Fintype.card {x : SV S p // c' (VertexSplit.sp S p x) = k} : ℝ) +
        (Fintype.card (Fake cc kc M) : ℝ) := by
      rw [← hNdef, Fintype.card_sum]; push_cast; ring
    have hW4 : (Fintype.card {x : SV S p // c' (VertexSplit.sp S p x) = k} : ℝ) ≤ 4 * n := by
      have h := Fintype.card_le_of_injective
        (fun x : {x : SV S p // c' (VertexSplit.sp S p x) = k} => (fstV S p x.1, I.φ (VertexSplit.sp S p x.1)))
        (by
          rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨h1, h2⟩ := hxy
          have h3 : VertexSplit.sp S p x = VertexSplit.sp S p y := by
            rw [← I.ψφ _ hx, ← I.ψφ _ hy, h2]
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext h1 h3)
      rw [Fintype.card_prod, Fintype.card_fin] at h
      have h' : ((Fintype.card {x : SV S p // c' (VertexSplit.sp S p x) = k} : ℕ) : ℝ) ≤
          ((Fintype.card V * 4 : ℕ) : ℝ) := by exact_mod_cast h
      have e : ((Fintype.card V * 4 : ℕ) : ℝ) = 4 * n := by rw [hnset]; push_cast; ring
      rw [e] at h'
      exact h'
    have hF4 : (Fintype.card (Fake cc kc M) : ℝ) ≤ 4 * (n + 2 ^ 21) := by
      have h := Fintype.card_subtype_le (fun x : Fin 4 × Fin M => cc x.1 ≠ kc)
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
      have h' : ((Fintype.card (Fake cc kc M) : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast h
      rw [hMR] at h'
      exact h'
    have hN9 : N ≤ 9 * n := by
      rw [hNsum]
      have : (2 : ℝ) ^ 23 ≤ n := le_trans (by norm_num) hnbig
      linarith
    -- the component has supply `ω n`, hence `ω n ≤ N`
    have hWlow : ω * n ≤ (Fintype.card {x : SV S p // c' (VertexSplit.sp S p x) = k} : ℝ) := by
      have h1 := hs' ∅ (by simp) i0 (by simp)
      have h2 : (guardedNeighbours (VertexSplit.sp S p) (splitG S p G) ∅ i0).card ≤
          Fintype.card {x : SV S p // c' (VertexSplit.sp S p x) = k} := by
        have hsub : guardedNeighbours (VertexSplit.sp S p) (splitG S p G) ∅ i0 ⊆
            (univ : Finset {x : SV S p // c' (VertexSplit.sp S p x) = k}).map (Function.Embedding.subtype _) := by
          intro x hx
          have hxi : VertexSplit.sp S p x = i0 := (mem_filter.mp hx).2.1
          exact mem_map.mpr ⟨⟨x, by rw [hxi]; exact hi0⟩, mem_univ _, rfl⟩
        have := card_le_card hsub
        rwa [card_map, card_univ] at this
      have h2' : ((guardedNeighbours (VertexSplit.sp S p) (splitG S p G) ∅ i0).card : ℝ) ≤
          Fintype.card {x : SV S p // c' (VertexSplit.sp S p x) = k} := by exact_mod_cast h2
      exact h1.trans h2'
    have hFake0 : (0 : ℝ) ≤ Fintype.card (Fake cc kc M) := Nat.cast_nonneg _
    have hωn : ω * n ≤ N := by rw [hNsum]; linarith
    have hN0 : 0 < N := lt_of_lt_of_le (mul_pos hω hn0) hωn
    have hNne : N ≠ 0 := hN0.ne'
    have ht1 : (1 : ℝ) ≤ t' := by exact_mod_cast ht'
    have hfl := par_component_scales ω n N t' ρ δ hω hω1 hδdef hρdef ht1 ht'8R hn hn0 hωn hN9
    have ha : ω * n / N * N ≤ ω * n := le_of_eq (div_mul_cancel₀ _ hNne)
    have hMb : ω * n / N * N + 2 ^ 21 ≤ (M : ℝ) := by
      rw [div_mul_cancel₀ _ hNne, hMR]
      have : ω * n ≤ n := calc ω * n ≤ 1 * n := mul_le_mul_of_nonneg_right hω1 hn0.le
        _ = n := one_mul n
      linarith
    have hRb : R ≤ 2 * (ρ * n / N) * N := by
      have : 2 * (ρ * n / N) * N = R := by rw [hR]; field_simp
      exact this.ge
    have hDb : 2 * (δ * n / t' / N) * N ≤ D := by
      have : 2 * (δ * n / t' / N) * N = D := by rw [hD]; field_simp
      exact this.le
    rw [← hNdef] at hfl ha hMb hRb hDb
    exact componentAbsorbers_via hτ' hcc hτc I hcert (VertexSplit.sp S p) (splitG S p G) hG' (ω * n)
      (fun T hT i hi hguard => hs' T hT i hguard) M (ω * n / _) (δ * n / t' / _) (ρ * n / _) R D
      hfl ha hMb hRb hDb X hXG hX hXin
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

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.universalCert_of_split2
