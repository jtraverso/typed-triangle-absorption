/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.Component
public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Transport

@[expose] public section

/-!
# Re-using a component certificate in an arbitrary component host

`absorbers_of_componentFlex`: let `kc` be a component of a covered family `Fc` (labelling `cc`)
with a flexible component certificate. Let `H` be a host on `W` all of whose vertices carry labels
of component `kc`, with allowed edges and the guarded supply `a` inside the component. Complete `H`
by a fake part: for every class `i` of the OTHER components, `M` fake vertices, joined completely
along the allowed pairs. In the completed host `H'` (on `W ⊕ Fake`, `N` vertices) the edges inside
component `kc` are exactly those of `H`, the supply is `≥ min(a, M − 2²¹)` in every class, and the
flexible certificate at `(ω, δ, ρ)` with `ω N ≤ a`, `ω N + 2²¹ ≤ M` gives absorbers, which are pulled
back to `H` (`hasDecomp_comap`, `isIntDiv_map`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.PhysicalHingeSupply
open PaddedF12 PaddedGeneral PaddedComponents PrivateTemplateStage69

variable (Fc : Finset (Multiset (Fin 4))) (cc : Fin 4 → Fin 4) (kc : Fin 4) (M : ℕ)

/-- Fake vertices: `M` per class of the other components. -/
abbrev Fake := {x : Fin 4 × Fin M // cc x.1 ≠ kc}

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The completed vertex type. -/
abbrev WC := W ⊕ Fake cc kc M

/-- Labels of the completed host. -/
def qC (q : W → Fin 4) : WC cc kc M (W := W) → Fin 4 := Sum.elim q fun x => x.1.1

/-- The relation of the completed host. -/
def RC (H : SimpleGraph W) : WC cc kc M (W := W) → WC cc kc M (W := W) → Prop
  | Sum.inl u, Sum.inl v => H.Adj u v
  | Sum.inr x, Sum.inr y => ∃ k, Link Fc x.1.1 y.1.1 k
  | _, _ => False

/-- The completed host. -/
def HC (H : SimpleGraph W) : SimpleGraph (WC cc kc M (W := W)) := SimpleGraph.fromRel (RC Fc cc kc M H)

noncomputable instance (H : SimpleGraph W) : DecidableRel (HC Fc cc kc M H).Adj := by
  classical infer_instance

theorem hc_inl (H : SimpleGraph W) (u v : W) :
    (HC Fc cc kc M H).Adj (Sum.inl u) (Sum.inl v) ↔ H.Adj u v := by
  simp only [HC, SimpleGraph.fromRel_adj, RC, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨H.ne_of_adj h, Or.inl h⟩

theorem hc_inr (H : SimpleGraph W) (x y : Fake cc kc M) :
    (HC Fc cc kc M H).Adj (Sum.inr x) (Sum.inr y) ↔ x ≠ y ∧ ∃ k, Link Fc x.1.1 y.1.1 k := by
  simp only [HC, SimpleGraph.fromRel_adj, RC, ne_eq, Sum.inr.injEq]
  constructor
  · rintro ⟨hxy, h | ⟨k, hk⟩⟩
    · exact ⟨hxy, h⟩
    · exact ⟨hxy, k, (link_root_swap Fc _ _ _).mp hk⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, Or.inl h⟩

theorem hc_mixed (H : SimpleGraph W) (u : W) (x : Fake cc kc M) :
    ¬ (HC Fc cc kc M H).Adj (Sum.inl u) (Sum.inr x) := by
  simp [HC, SimpleGraph.fromRel_adj, RC]

/-- The real part as an embedding. -/
def ιW : W ↪ WC cc kc M (W := W) := ⟨Sum.inl, Sum.inl_injective⟩

theorem card_filter_map_inl (E : Finset (Sym2 W)) (w : W) :
    ((E.map (edgeEmb (ιW cc kc M (W := W)))).filter (fun e => Sum.inl w ∈ e)).card =
      (E.filter (fun e => w ∈ e)).card := by
  rw [filter_map, card_map]
  congr 1
  refine filter_congr fun e _ => ?_
  show Sum.inl w ∈ Sym2.map Sum.inl e ↔ w ∈ e
  constructor
  · intro hw
    obtain ⟨a, ha, hwa⟩ := Sym2.mem_map.mp hw
    cases hwa; exact ha
  · intro hw
    exact Sym2.mem_map.mpr ⟨w, hw, rfl⟩

theorem card_filter_map_inr (E : Finset (Sym2 W)) (x : Fake cc kc M) :
    ((E.map (edgeEmb (ιW cc kc M (W := W)))).filter (fun e => Sum.inr x ∈ e)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hx
  obtain ⟨e', -, rfl⟩ := mem_map.mp he
  simp only [edgeEmb, Function.Embedding.coeFn_mk] at hx
  obtain ⟨a, -, ha⟩ := Sym2.mem_map.mp hx
  simp [ιW] at ha

/-- **Re-use of a flexible component certificate.** -/
theorem absorbers_of_componentFlex (hcc : CompLabel Fc cc) (hcert : ComponentUniversalCertFlex Fc cc kc)
    (q : W → Fin 4) (hq : ∀ w, cc (q w) = kc)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hH : ∀ u v, H.Adj u v → ∃ k, Link Fc (q u) (q v) k)
    (a : ℝ) (hsupp : ∀ S : Finset W, S.card ≤ 2 ^ 21 → ∀ i, cc i = kc →
      (∀ u ∈ S, ∃ k, Link Fc (q u) i k) →
        a ≤ ((univ.filter fun w => q w = i ∧ ∀ u ∈ S, H.Adj u w).card : ℝ))
    (ω δ ρ : ℝ) (hfl : FlexScales ω δ ρ (Fintype.card (WC cc kc M (W := W))))
    (ha : ω * Fintype.card (WC cc kc M (W := W)) ≤ a)
    (hM : ω * Fintype.card (WC cc kc M (W := W)) + 2 ^ 21 ≤ M) :
    ∀ X : Finset (Sym2 W), X ⊆ H.edgeFinset →
      DegBounded X (2 * ρ * Fintype.card (WC cc kc M (W := W))) →
      ∃ A : Finset (Sym2 W), A ⊆ H.edgeFinset ∧ Disjoint A X ∧ HasDecomp q Fc A ∧
        DegBounded A (2 * δ * Fintype.card (WC cc kc M (W := W))) ∧
        ∀ L ⊆ X, IsIntDiv q Fc L → HasDecomp q Fc (A ∪ L) := by
  classical
  intro X hXH hX
  have hq' : ∀ w, qC cc kc M q (ιW cc kc M (W := W) w) = q w := fun _ => rfl
  -- edges of the real part
  have hmapH : ∀ E : Finset (Sym2 W), E ⊆ H.edgeFinset → E.map (edgeEmb (ιW cc kc M (W := W))) ⊆ (HC Fc cc kc M H).edgeFinset := by
    intro E hE f hf
    obtain ⟨e, he, rfl⟩ := mem_map.mp hf
    induction e using Sym2.ind with
    | _ u v =>
      have := SimpleGraph.mem_edgeFinset.mp (hE he)
      show s(Sum.inl u, Sum.inl v) ∈ (HC Fc cc kc M H).edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (hc_inl Fc cc kc M H u v).mpr this
  have hdeg_map : ∀ (E : Finset (Sym2 W)) (D : ℝ), DegBounded E D → 0 ≤ D →
      DegBounded (E.map (edgeEmb (ιW cc kc M (W := W)))) D := by
    intro E D hE hD x
    rcases x with w | y
    · rw [card_filter_map_inl]; exact hE w
    · rw [card_filter_map_inr]; simpa using hD
  -- allowed edges of the completed host
  have hH' : ∀ u v, (HC Fc cc kc M H).Adj u v → ∃ k, Link Fc (qC cc kc M q u) (qC cc kc M q v) k := by
    rintro (u | x) (v | y) h
    · exact hH u v ((hc_inl Fc cc kc M H u v).mp h)
    · exact absurd h (hc_mixed Fc cc kc M H u y)
    · exact absurd h.symm (hc_mixed Fc cc kc M H v x)
    · exact ((hc_inr Fc cc kc M H x y).mp h).2
  -- supply of the completed host
  have hs' : GuardedSupply (qC cc kc M q) (HC Fc cc kc M H) (fun i j => ∃ k, Link Fc i j k) (2 ^ 21) (ω * Fintype.card (WC cc kc M (W := W))) := by
    intro S' hS' i hguard
    by_cases hi : cc i = kc
    · -- real class: `S'` is real
      have hreal : ∀ u ∈ S', ∃ w, u = Sum.inl w := by
        rintro (w | x) hu
        · exact ⟨w, rfl⟩
        · exfalso
          obtain ⟨k, hk⟩ := hguard _ hu
          have := hcc _ _ ⟨k, hk⟩
          exact x.2 (this.trans hi)
      let S : Finset W := univ.filter fun w => (Sum.inl w : WC cc kc M (W := W)) ∈ S'
      have hS : S.card ≤ 2 ^ 21 :=
        (card_le_card_of_injOn Sum.inl (fun w hw => (mem_filter.mp hw).2)
          Sum.inl_injective.injOn).trans hS'
      have hSg : ∀ u ∈ S, ∃ k, Link Fc (q u) i k := fun u hu => hguard _ (mem_filter.mp hu).2
      have h1 := hsupp S hS i hi hSg
      have hsub : ((univ.filter fun w => q w = i ∧ ∀ u ∈ S, H.Adj u w).map (ιW cc kc M (W := W))) ⊆
          guardedNeighbours (qC cc kc M q) (HC Fc cc kc M H) S' i := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
        obtain ⟨hwi, hwS⟩ := (mem_filter.mp hw).2
        refine mem_filter.mpr ⟨mem_univ _, hwi, fun u hu => ?_⟩
        obtain ⟨u', rfl⟩ := hreal u hu
        exact (hc_inl Fc cc kc M H u' w).mpr (hwS u' (mem_filter.mpr ⟨mem_univ _, hu⟩))
      have h2 := card_le_card hsub
      rw [card_map] at h2
      have h2' : ((univ.filter fun w => q w = i ∧ ∀ u ∈ S, H.Adj u w).card : ℝ) ≤
          (guardedNeighbours (qC cc kc M q) (HC Fc cc kc M H) S' i).card := by exact_mod_cast h2
      linarith
    · -- fake class: the fake vertices of class `i` outside `S'`
      have hfake : ∀ u ∈ S', ∃ y : Fake cc kc M, u = Sum.inr y := by
        rintro (w | y) hu
        · exfalso
          obtain ⟨k, hk⟩ := hguard _ hu
          exact hi ((hcc _ _ ⟨k, hk⟩).symm.trans (hq w))
        · exact ⟨y, rfl⟩
      let T : Finset (WC cc kc M (W := W)) :=
        (univ.image fun m : Fin M => (Sum.inr ⟨(i, m), hi⟩ : WC cc kc M (W := W))) \ S'
      have hT : T ⊆ guardedNeighbours (qC cc kc M q) (HC Fc cc kc M H) S' i := by
        intro z hz
        obtain ⟨hzim, hzS⟩ := mem_sdiff.mp hz
        obtain ⟨m, -, rfl⟩ := mem_image.mp hzim
        refine mem_filter.mpr ⟨mem_univ _, rfl, fun u hu => ?_⟩
        obtain ⟨y, rfl⟩ := hfake u hu
        refine (hc_inr Fc cc kc M H y ⟨(i, m), hi⟩).mpr ⟨fun h => hzS (h ▸ hu), ?_⟩
        exact hguard _ hu
      have hTcard : (M : ℝ) - 2 ^ 21 ≤ T.card := by
        have h1 : #(univ.image fun m : Fin M => (Sum.inr ⟨(i, m), hi⟩ : WC cc kc M (W := W))) = M := by
          rw [card_image_of_injective _ (fun m m' h => by
            simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h; exact h.2)]
          simp
        have h2 := le_card_sdiff S' (univ.image fun m : Fin M =>
          (Sum.inr ⟨(i, m), hi⟩ : WC cc kc M (W := W)))
        rw [h1] at h2
        have h3 : M ≤ T.card + S'.card := Nat.sub_le_iff_le_add.mp h2
        have h3' : (M : ℝ) ≤ T.card + S'.card := by exact_mod_cast h3
        have h4 : (S'.card : ℝ) ≤ 2 ^ 21 := by exact_mod_cast hS'
        linarith
      have h5 : (T.card : ℝ) ≤ (guardedNeighbours (qC cc kc M q) (HC Fc cc kc M H) S' i).card := by
        exact_mod_cast card_le_card hT
      linarith
  -- apply the flexible certificate
  have hX' := hdeg_map X _ hX (by have := hfl.ρn; have := hfl.n_nonneg; nlinarith)
  have hXin : ∀ e ∈ X.map (edgeEmb (ιW cc kc M (W := W))), InsideE (qC cc kc M q) cc kc e := by
    intro f hf
    obtain ⟨e, -, rfl⟩ := mem_map.mp hf
    induction e using Sym2.ind with
    | _ u v =>
      show InsideE (qC cc kc M q) cc kc s(Sum.inl u, Sum.inl v)
      exact (insideE_mk (qC cc kc M q) cc kc (Sum.inl u) (Sum.inl v)).mpr ⟨hq u, hq v⟩
  obtain ⟨A', hA'H, hA'X, hA'in, hA'dec, hA'deg, hA'L⟩ :=
    hcert (WC cc kc M (W := W)) (qC cc kc M q) (HC Fc cc kc M H) ω δ ρ hfl hH' hs' (X.map (edgeEmb (ιW cc kc M (W := W)))) (hmapH X hXH) hX' hXin
  -- every edge of `A'` is real
  have hreal : ∀ f ∈ A', ∃ e : Sym2 W, edgeEmb (ιW cc kc M (W := W)) e = f := by
    intro f hf
    have hin := hA'in f hf
    induction f using Sym2.ind with
    | _ x y =>
      obtain ⟨hx, hy⟩ := (insideE_mk (qC cc kc M q) cc kc x y).mp hin
      rcases x with u | x
      · rcases y with v | y
        · exact ⟨s(u, v), rfl⟩
        · exact absurd hy y.2
      · exact absurd hx x.2
  set A : Finset (Sym2 W) := univ.filter fun e => edgeEmb (ιW cc kc M (W := W)) e ∈ A'
  have hAmap : A.map (edgeEmb (ιW cc kc M (W := W))) = A' := by
    ext f
    constructor
    · intro hf
      obtain ⟨e, he, rfl⟩ := mem_map.mp hf
      exact (mem_filter.mp he).2
    · intro hf
      obtain ⟨e, rfl⟩ := hreal f hf
      exact mem_map_of_mem _ (mem_filter.mpr ⟨mem_univ _, hf⟩)
  have hAH : A ⊆ H.edgeFinset := by
    intro e he
    have h1 := hA'H (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ u v =>
      have h2 : (HC Fc cc kc M H).Adj (Sum.inl u) (Sum.inl v) := by
        have : s(Sum.inl u, Sum.inl v) ∈ (HC Fc cc kc M H).edgeFinset := h1
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (hc_inl Fc cc kc M H u v).mp h2
  refine ⟨A, hAH, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro e heA heX
    exact disjoint_left.mp hA'X (mem_filter.mp heA).2 (mem_map_of_mem _ heX)
  · exact hasDecomp_comap (ιW cc kc M (W := W)) (by rw [hAmap]; exact hA'dec)
  · intro w
    have := hA'deg (Sum.inl w)
    rw [← hAmap, card_filter_map_inl] at this
    exact this
  · intro L hLX hL
    have hL' : L.map (edgeEmb (ιW cc kc M (W := W))) ⊆ X.map (edgeEmb (ιW cc kc M (W := W))) := map_subset_map.mpr hLX
    have h1 := hA'L _ hL' (isIntDiv_map (ιW cc kc M (W := W)) hq' hL)
    rw [← hAmap, ← map_union] at h1
    exact hasDecomp_comap (ιW cc kc M (W := W)) h1

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.absorbers_of_componentFlex
