/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.CertTerminal.FromIntDiv
public import PartitionedTriangleAbsorption.BlowupB.CertAbsorber.Host
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply
public import PartitionedTriangleAbsorption.PrivateTemplateStage69.Transport

@[expose] public section

/-!
# A terminal absorber for EVERY family (no `KappaLinks`, no `ThreeStepLinks`)

`cert_terminal`: for every family `F` of triangles and every piece size `K` there is `C` such
that, in any host `G` whose edges are allowed and which has the guarded supply of common
neighbours (four roots) with margin `a > |Z| + 2K + 5t + 9C + 4d`, every allowed `IsIntDiv` piece
`P ⊆ E(G)` with `|P| ≤ K` has an absorber `A ⊆ E(G)` avoiding a ledger `L` of maximum degree `d`:
`A` and `A ∪ P` decompose, `|A| ≤ 30 C`, new vertices avoid `Z`, and no edge of `A` joins two
vertices of `P`.

Route: `5` fresh representatives per class outside `Z ∪ V(P)` (from the supply with `S = ∅`);
`exists_signedCert_complete` on `W = V(P) ∪ reps` gives a signed certificate of length `≤ C`;
the certificate absorber `host_certificate_absorber` (Aristotle 52daa09e, ported) realises it.
This replaces the `KappaLinks`-terminal of the component pipeline except for the exact root-load
identity `TerminalAbsorber.root_load`, which no consumer uses.
-/

namespace PartitionedTriangleAbsorption.BlowupB.CertTerminal

open Finset PartitionedTriangleAbsorption PaperII.CertAbsorber
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.PairMoveSelectionStage85
open PartitionedTriangleAbsorption.TypedEmbeddingSelection
open PartitionedTriangleAbsorption.AntiEdgeSelection PartitionedTriangleAbsorption.TypedTransformer

variable {t : ℕ}

theorem allowedPair_of_link {F : Finset (Multiset (Fin t))} (hF3 : ∀ τ ∈ F, Multiset.card τ = 3)
    {i j k : Fin t} (h : Link F i j k) : AllowedPair F i j :=
  ⟨{i, j, k}, h, hF3 _ h, by
    show i ::ₘ j ::ₘ 0 ≤ i ::ₘ j ::ₘ k ::ₘ 0
    exact Multiset.cons_le_cons i (Multiset.cons_le_cons j (Multiset.zero_le _))⟩

theorem vertSet_card_le_two {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) :
    (vertSet E).card ≤ 2 * E.card := by
  classical
  have hsub : vertSet E ⊆ E.biUnion fun e => univ.filter (· ∈ e) := by
    intro v hv
    obtain ⟨e, he, hve⟩ := (mem_filter.mp hv).2
    exact mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ _, hve⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have : ∀ e : Sym2 V, (univ.filter (· ∈ e)).card ≤ 2 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      have : univ.filter (· ∈ s(a, b)) ⊆ {a, b} := by
        intro v hv
        rcases Sym2.mem_iff.mp (mem_filter.mp hv).2 with rfl | rfl <;> simp
      exact (card_le_card this).trans (card_le_two)
  calc ∑ e ∈ E, (univ.filter (· ∈ e)).card ≤ ∑ _e ∈ E, 2 := sum_le_sum fun e _ => this e
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The guarded supply with four roots gives the compatible supply of the certificate absorber. -/
theorem compatibleSupply_of_guarded {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Multiset (Fin t))} {p : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {a : ℝ} (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 a) :
    CompatibleSupply p F G a := by
  intro S hS i hcomp
  have h := hs S hS i (fun u hu => by
    obtain ⟨k, hk⟩ := hcomp u hu
    exact ⟨k, (link_root_swap F _ _ _).mp hk⟩)
  simpa [guardedNeighbours, typedNeighbours] using h

/-- **The certificate terminal absorber, for every family.** -/
theorem cert_terminal (F : Finset (Multiset (Fin t))) (hF3 : ∀ τ ∈ F, Multiset.card τ = 3)
    (K : ℕ) : ∃ C : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin t)
      (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V),
      (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 a →
      DegBounded L d → 0 ≤ d →
      (Z.card : ℝ) + (2 * K + 5 * t) + 9 * C + 4 * d < a →
      ∀ P : Finset (Sym2 V), P ⊆ G.edgeFinset → P.card ≤ K → IsIntDiv p F P →
        ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A L ∧ Disjoint A P ∧
          HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧ A.card ≤ 30 * C ∧
          (∀ v ∈ vertSet A, v ∈ vertSet P ∨ v ∉ Z) ∧
          (∀ v ∈ vertSet P, ∀ w ∈ vertSet P, s(v, w) ∉ A) := by
  classical
  obtain ⟨C, hC⟩ := exists_signedCert_complete F hF3 K
  refine ⟨C, ?_⟩
  intro V _ _ p G _ a d L Z hG hs hL hd hbud P hPG hPK hdiv
  -- the roots of the piece
  set VP := vertSet P with hVP
  have hVPcard : VP.card ≤ 2 * K := (vertSet_card_le_two P).trans (by omega)
  -- five fresh representatives per class
  have hclass : ∀ i : Fin t, 5 ≤ ((univ.filter fun v => p v = i) \ (Z ∪ VP)).card := by
    intro i
    have h0 := hs ∅ (by simp) i (by simp)
    have hcl : (guardedNeighbours p G ∅ i) = univ.filter fun v => p v = i := by
      ext v; simp [guardedNeighbours]
    rw [hcl] at h0
    have h1 : ((univ.filter fun v => p v = i).card : ℝ) ≤
        ((univ.filter fun v => p v = i) \ (Z ∪ VP)).card + (Z ∪ VP).card := by
      have := card_le_card_sdiff_add_card (s := univ.filter fun v => p v = i) (t := Z ∪ VP)
      exact_mod_cast this
    have h2 : ((Z ∪ VP).card : ℝ) ≤ Z.card + 2 * K := by
      have := (card_union_le Z VP).trans (Nat.add_le_add_left hVPcard _)
      exact_mod_cast this
    have ht : (5 : ℝ) ≤ 5 * t := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
        intro h0; subst h0; exact Fin.elim0 i))
      linarith
    have hC0 : (0 : ℝ) ≤ 9 * C := by positivity
    have h3 : (5 : ℝ) ≤ ((univ.filter fun v => p v = i) \ (Z ∪ VP)).card := by linarith
    exact_mod_cast h3
  choose Q hQsub hQcard using fun i => exists_subset_card_eq (hclass i)
  let RS : Finset V := univ.biUnion Q
  let WS : Finset V := VP ∪ RS
  let W := {v // v ∈ WS}
  let ρ : W ↪ V := Function.Embedding.subtype _
  have hQcls : ∀ i, ∀ v ∈ Q i, p v = i := fun i v hv =>
    (mem_filter.mp (mem_sdiff.mp (hQsub i hv)).1).2
  have hQout : ∀ i, ∀ v ∈ Q i, v ∉ Z ∪ VP := fun i v hv => (mem_sdiff.mp (hQsub i hv)).2
  -- representatives in `W`
  let e : ∀ i, {v // v ∈ Q i} ≃ Fin 5 := fun i =>
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hQcard i)
  let R : Reps (p ∘ ρ) 5 :=
    { rep := fun i a => ⟨((e i).symm a).1,
        mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, ((e i).symm a).2⟩)⟩
      inj := by
        intro i a i' a' h
        have hv : ((e i).symm a).1 = ((e i').symm a').1 := congrArg Subtype.val h
        have hii : i = i' := by
          rw [← hQcls i _ ((e i).symm a).2, hv, hQcls i' _ ((e i').symm a').2]
        subst hii
        exact ⟨rfl, (e i).symm.injective (Subtype.ext hv)⟩
      cls := fun i a => hQcls i _ ((e i).symm a).2 }
  -- the piece on `W`
  have hmemW : ∀ x ∈ VP, x ∈ WS := fun x hx => mem_union_left _ hx
  let P' : Finset (Sym2 W) := univ.filter fun e => Sym2.map ρ e ∈ P
  have hP'map : P'.map (PhysicalHingeSupply.edgeEmb ρ) = P := by
    ext f
    simp only [mem_map, P', mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨e', he', rfl⟩; exact he'
    · intro hf
      induction f using Sym2.ind with
      | _ u v =>
        have hu : u ∈ WS := hmemW u (mem_filter.mpr ⟨mem_univ _, _, hf, Sym2.mem_mk_left u v⟩)
        have hv : v ∈ WS := hmemW v (mem_filter.mpr ⟨mem_univ _, _, hf, Sym2.mem_mk_right u v⟩)
        exact ⟨s(⟨u, hu⟩, ⟨v, hv⟩), hf, rfl⟩
  have hP'img : P'.image (Sym2.map ρ) = P := by
    rw [← hP'map, map_eq_image]; rfl
  have hdiv' : IsIntDiv (p ∘ ρ) F P' :=
    PrivateTemplateStage69.isIntDiv_comap ρ (by rw [hP'map]; exact hdiv)
  have hloop' : ∀ e ∈ P', ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have h := (mem_filter.mp he).2
      have hne := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp (hPG h))
      intro hd
      rw [Sym2.mk_isDiag_iff] at hd
      exact hne (by simp [Sym2.map_mk, hd])
  have hall' : ∀ u v, s(u, v) ∈ P' → AllowedPair F ((p ∘ ρ) u) ((p ∘ ρ) v) := by
    intro u v huv
    have h := (mem_filter.mp huv).2
    have hadj := SimpleGraph.mem_edgeFinset.mp (hPG h)
    obtain ⟨k, hk⟩ := hG _ _ hadj
    exact allowedPair_of_link hF3 hk
  have hK' : P'.card ≤ K := by
    have := card_map (PhysicalHingeSupply.edgeEmb ρ) (s := P')
    rw [hP'map] at this
    omega
  obtain ⟨c, hck⟩ := hC (p ∘ ρ) R P' hloop' hall' hdiv' hK'
  -- size of `W`
  have hWcard : (Fintype.card W : ℝ) ≤ 2 * K + 5 * t := by
    have h1 : Fintype.card W = WS.card := Fintype.card_coe WS
    have h2 : RS.card ≤ 5 * t := by
      refine card_biUnion_le.trans (le_of_eq ?_)
      calc ∑ i, (Q i).card = ∑ _i : Fin t, 5 := sum_congr rfl fun i _ => hQcard i
        _ = 5 * t := by simp [mul_comm]
    have h3 : WS.card ≤ 2 * K + 5 * t := (card_union_le VP RS).trans (by omega)
    rw [h1]; exact_mod_cast h3
  have hbud' : (Z.card : ℝ) + Fintype.card W + 9 * c.k + 4 * d < a := by
    have : (c.k : ℝ) ≤ C := by exact_mod_cast hck
    linarith
  obtain ⟨A, hAG, hAL, hdec, hdecU, hAP, -, hAcard, ⟨N, -, hNdis, hAv, hAN⟩, -⟩ :=
    host_certificate_absorber p G ρ c a d (compatibleSupply_of_guarded hs) L hL hd Z hbud'
  rw [hP'img] at hdecU hAP
  have hroot : ∀ x, x ∈ univ.image ρ → x ∈ VP ∨ x ∉ Z := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := mem_image.mp hx
    rcases mem_union.mp w.2 with h | h
    · exact Or.inl h
    · right
      obtain ⟨i, -, hi⟩ := mem_biUnion.mp h
      exact fun hz => hQout i _ hi (mem_union_left _ hz)
  refine ⟨A, hAG, hAL, hAP, hdec, hdecU, hAcard.trans (by have := hck; omega), ?_, ?_⟩
  · intro v hv
    obtain ⟨f, hf, hvf⟩ := (mem_filter.mp hv).2
    rcases hAv f hf v hvf with h | h
    · exact hroot v h
    · exact Or.inr fun hz => (disjoint_left.mp hNdis h) (mem_union_left _ hz)
  · intro v hv w hw hvw
    obtain ⟨x, hx, hxN⟩ := hAN _ hvw
    have hxr : x ∈ univ.image ρ := by
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact mem_image.mpr ⟨⟨x, hmemW x hv⟩, mem_univ _, rfl⟩
      · exact mem_image.mpr ⟨⟨x, hmemW x hw⟩, mem_univ _, rfl⟩
    exact disjoint_left.mp hNdis hxN (mem_union_right _ hxr)

end PartitionedTriangleAbsorption.BlowupB.CertTerminal

#print axioms PartitionedTriangleAbsorption.BlowupB.CertTerminal.cert_terminal
