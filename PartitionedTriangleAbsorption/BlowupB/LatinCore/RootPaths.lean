/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.RootChannels
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.Defs

@[expose] public section

/-! Private paths for the globally glued root network. This producer fixes the
network before all root-balanced unit demands, with total port degree16 and
at most24 times as many arcs as ports. No original input arcs are inserted yet. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths

open Finset
open Cycles

variable {P E : Type} [DecidableEq P] [Fintype E] [DecidableEq E]

abbrev Vert (P E : Type) := P ⊕ (E × Fin 2)

variable (src dst : E → P)

def colour (c : P → ZMod 3) : Vert P E → ZMod 3
  | Sum.inl p => c p
  | Sum.inr (e,i) => c (src e) + (i.val : ZMod 3) + 1

def pathArcs (e : E) : Finset (Vert P E × Vert P E) :=
  {(Sum.inl (src e), Sum.inr (e,0)), (Sum.inr (e,0), Sum.inr (e,1)),
    (Sum.inr (e,1), Sum.inl (dst e))}

def arcsOf (T : Finset E) : Finset (Vert P E × Vert P E) :=
  T.biUnion (pathArcs src dst)

def arcs : Finset (Vert P E × Vert P E) := arcsOf src dst univ

theorem arcsOf_subset (T : Finset E) : arcsOf src dst T ⊆ arcs src dst :=
  biUnion_subset_biUnion_of_subset_left _ (subset_univ T)

theorem isCyc_arcs (c : P → ZMod 3) (hcol : ∀ e, c (src e) = c (dst e)) :
    IsCyc (colour src c) (arcs src dst) := by
  intro a ha
  obtain ⟨e, -, he⟩ := mem_biUnion.mp ha
  simp only [pathArcs, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · simp [colour]
  · simp [colour]
  · simp only [colour, Fin.val_one, Nat.cast_one]
    rw [← hcol e]
    have hthree : (3 : ZMod 3) = 0 := by decide
    calc c (src e) = c (src e) + 0 := by ring
      _ = c (src e) + 3 := by rw [hthree]
      _ = (c (src e) + 1 + 1) + 1 := by ring

theorem in_port (T : Finset (E)) (v : P) :
    (arcsOf src dst T).filter (fun a => a.2 = Sum.inl v)
      = (T.filter (fun e => dst e = v)).image (fun e => (Sum.inr (e, 1), Sum.inl v)) := by
  ext ⟨x, y⟩
  simp only [arcsOf, pathArcs, mem_filter, mem_biUnion, mem_insert, mem_singleton,
    mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨e, he, h⟩, rfl⟩
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨rfl, h⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact ⟨e, ⟨he, (Sum.inl.inj h).symm⟩, rfl, rfl⟩
  · rintro ⟨e, ⟨he, hd⟩, rfl, rfl⟩
    exact ⟨⟨e, he, Or.inr (Or.inr ⟨rfl, by rw [hd]⟩)⟩, rfl⟩

theorem out_port (T : Finset (E)) (v : P) :
    (arcsOf src dst T).filter (fun a => a.1 = Sum.inl v)
      = (T.filter (fun e => src e = v)).image (fun e => (Sum.inl v, Sum.inr (e, 0))) := by
  ext ⟨x, y⟩
  simp only [arcsOf, pathArcs, mem_filter, mem_biUnion, mem_insert, mem_singleton,
    mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨e, he, h⟩, rfl⟩
    rcases h with ⟨h, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨e, ⟨he, (Sum.inl.inj h).symm⟩, rfl, rfl⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro ⟨e, ⟨he, hd⟩, rfl, rfl⟩
    exact ⟨⟨e, he, Or.inl ⟨by rw [hd], rfl⟩⟩, rfl⟩

theorem card_in_port (T : Finset (E)) (v : P) :
    ((arcsOf src dst T).filter (fun a => a.2 = Sum.inl v)).card
      = (T.filter (fun e => dst e = v)).card := by
  rw [in_port, card_image_of_injective]
  intro e e' h
  simp only [Prod.mk.injEq, Sum.inr.injEq, and_true] at h
  exact h

theorem card_out_port (T : Finset (E)) (v : P) :
    ((arcsOf src dst T).filter (fun a => a.1 = Sum.inl v)).card
      = (T.filter (fun e => src e = v)).card := by
  rw [out_port, card_image_of_injective]
  intro e e' h
  simp only [Prod.mk.injEq, Sum.inr.injEq, and_true, true_and] at h
  exact h

theorem card_in_aux (T : Finset (E)) (e : E) (i : Fin 2) :
    ((arcsOf src dst T).filter (fun a => a.2 = Sum.inr (e, i))).card = if e ∈ T then 1 else 0 := by
  by_cases he : e ∈ T
  · rw [if_pos he, card_eq_one]
    fin_cases i
    · refine ⟨(Sum.inl (src e), Sum.inr (e, 0)), ?_⟩
      ext ⟨x, y⟩
      simp only [arcsOf, pathArcs, mem_filter, mem_biUnion, mem_insert, mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨e', he', h⟩, rfl⟩
        aesop
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨e, he, by simp⟩, rfl⟩
    · refine ⟨(Sum.inr (e, 0), Sum.inr (e, 1)), ?_⟩
      ext ⟨x, y⟩
      simp only [arcsOf, pathArcs, mem_filter, mem_biUnion, mem_insert, mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨e', he', h⟩, rfl⟩
        aesop
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨e, he, by simp⟩, rfl⟩
  · rw [if_neg he, card_eq_zero, filter_eq_empty_iff]
    intro a ha hae
    obtain ⟨e', he', h⟩ := mem_biUnion.1 ha
    simp only [pathArcs, mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> simp_all

theorem card_out_aux (T : Finset (E)) (e : E) (i : Fin 2) :
    ((arcsOf src dst T).filter (fun a => a.1 = Sum.inr (e, i))).card = if e ∈ T then 1 else 0 := by
  by_cases he : e ∈ T
  · rw [if_pos he, card_eq_one]
    fin_cases i
    · refine ⟨(Sum.inr (e, 0), Sum.inr (e, 1)), ?_⟩
      ext ⟨x, y⟩
      simp only [arcsOf, pathArcs, mem_filter, mem_biUnion, mem_insert, mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨e', he', h⟩, rfl⟩
        aesop
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨e, he, by simp⟩, rfl⟩
    · refine ⟨(Sum.inr (e, 1), Sum.inl (dst e)), ?_⟩
      ext ⟨x, y⟩
      simp only [arcsOf, pathArcs, mem_filter, mem_biUnion, mem_insert, mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨e', he', h⟩, rfl⟩
        aesop
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨e, he, by simp⟩, rfl⟩
  · rw [if_neg he, card_eq_zero, filter_eq_empty_iff]
    intro a ha hae
    obtain ⟨e', he', h⟩ := mem_biUnion.1 ha
    simp only [pathArcs, mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> simp_all


theorem card_arcs_le : (arcs src dst).card ≤ 3 * Fintype.card E := by
  classical
  calc (arcs src dst).card ≤ ∑ e : E, (pathArcs src dst e).card := card_biUnion_le
    _ ≤ ∑ _e : E, 3 := sum_le_sum fun e _ => by
      have h1 := card_insert_le (Sum.inl (src e), Sum.inr (e,0))
        ({(Sum.inr (e,0), Sum.inr (e,1)), (Sum.inr (e,1), Sum.inl (dst e))} :
          Finset (Vert P E × Vert P E))
      have h2 := card_insert_le (Sum.inr (e,0), Sum.inr (e,1))
        ({(Sum.inr (e,1), Sum.inl (dst e))} : Finset (Vert P E × Vert P E))
      simp only [card_singleton] at h2
      change _ ≤ 3
      unfold pathArcs
      omega
    _ = _ := by simp [mul_comm]

variable {V : Type} [Fintype P] [Fintype V] [DecidableEq V]

/-- A single globally glued private-path network serves every balanced unit demand. -/
theorem exists_root_paths (root : P → V) (c : V → ZMod 3) :
    ∃ σ : RootChannels.Perms root,
      let s := RootChannels.src root σ
      let d := RootChannels.dst root σ
      IsCyc (colour s (c ∘ root)) (arcs s d) ∧
      MaxDegLE (arcs s d) 16 ∧
      (arcs s d).card ≤ 24 * Fintype.card P ∧
      ∀ b : P → ℤ, (∀ v, ∑ p : RootChannels.Fibre root v, b p.val = 0) →
        (∀ p, |b p| ≤ 1) →
        ∃ A ⊆ arcs s d,
          (∀ p, ((A.filter (fun e => e.2 = Sum.inl p)).card : ℤ) -
            ((A.filter (fun e => e.1 = Sum.inl p)).card : ℤ) = b p) ∧
          ∀ e i, (A.filter (fun a => a.2 = Sum.inr (e,i))).card =
            (A.filter (fun a => a.1 = Sum.inr (e,i))).card := by
  classical
  obtain ⟨σ, hroots, hout, hin, hcard, hroute⟩ := RootChannels.exists_network root
  let s := RootChannels.src root σ
  let d := RootChannels.dst root σ
  refine ⟨σ, isCyc_arcs s d (c ∘ root) (fun e => congrArg c (hroots e).1), ?_, ?_, ?_⟩
  · intro x
    rcases x with p | ⟨e,i⟩
    · unfold deg inDeg outDeg
      rw [arcs, card_in_port, card_out_port]
      have h1 := hin p
      have h2 := hout p
      omega
    · unfold deg inDeg outDeg
      rw [arcs, card_in_aux, card_out_aux]
      simp
  · exact (card_arcs_le s d).trans (by omega)
  · intro b hz hb
    obtain ⟨T, hT⟩ := hroute b hz hb
    refine ⟨arcsOf s d T, arcsOf_subset s d T, ?_, ?_⟩
    · intro p
      rw [card_in_port, card_out_port]
      exact hT p
    · intro e i
      rw [card_in_aux, card_out_aux]

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths.exists_root_paths
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootPaths.exists_root_paths

