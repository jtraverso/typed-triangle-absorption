/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.EightPermChannels

@[expose] public section

/-! One fixed indexed channel network on every fibre of the physical-root map.
The family is chosen before all demands. Parallel channels remain distinct.
No routing or expander oracle is a premise of exists_network. -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.RootChannels

open Finset

variable {P V : Type} [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

abbrev Fibre (root : P → V) (v : V) := {p : P // root p = v}

def index (root : P → V) (v : V) : Fibre root v ≃ Fin (Fintype.card (Fibre root v)) :=
  Fintype.equivFin _

def node (root : P → V) (v : V) : Fin (Fintype.card (Fibre root v)) ↪ P where
  toFun a := ((index root v).symm a).val
  inj' := fun a b h => (index root v).symm.injective (Subtype.ext h)

theorem node_root (root : P → V) (v : V) (a : Fin (Fintype.card (Fibre root v))) :
    root (node root v a) = v := ((index root v).symm a).property

abbrev Perms (root : P → V) :=
  ∀ v : V, Fin 8 → Equiv.Perm (Fin (Fintype.card (Fibre root v)))

abbrev Channel (root : P → V) (σ : Perms root) :=
  Σ v : V, EightPermChannels.Channel (σ v)

def src (root : P → V) (σ : Perms root) (e : Channel root σ) : P :=
  node root e.1 (EightPermChannels.src (σ e.1) e.2)

def dst (root : P → V) (σ : Perms root) (e : Channel root σ) : P :=
  node root e.1 (EightPermChannels.dst (σ e.1) e.2)

theorem src_root (root : P → V) (σ : Perms root) (e : Channel root σ) :
    root (src root σ e) = e.1 := node_root _ _ _

theorem dst_root (root : P → V) (σ : Perms root) (e : Channel root σ) :
    root (dst root σ e) = e.1 := node_root _ _ _

def embed (root : P → V) (σ : Perms root) (v : V) :
    EightPermChannels.Channel (σ v) ↪ Channel root σ where
  toFun e := ⟨v, e⟩
  inj' := by intro a b h; simpa using h

def selected (root : P → V) (σ : Perms root)
    (T : ∀ v, Finset (EightPermChannels.Channel (σ v))) : Finset (Channel root σ) :=
  univ.filter fun e => e.2 ∈ T e.1

theorem selected_univ (root : P → V) (σ : Perms root) :
    selected root σ (fun _ => univ) = univ := by
  classical
  ext e
  simp [selected]

theorem endpoint_count (root : P → V) (σ : Perms root)
    (T : ∀ v, Finset (EightPermChannels.Channel (σ v)))
    (endpoint : Channel root σ → P) (he : ∀ e, root (endpoint e) = e.1)
    (v : V) (p : P) (hp : root p = v) :
    ((selected root σ T).filter (fun e => endpoint e = p)).card =
      ((T v).filter (fun e => endpoint ⟨v,e⟩ = p)).card := by
  classical
  have hset : (selected root σ T).filter (fun e => endpoint e = p) =
      ((T v).filter (fun e => endpoint ⟨v,e⟩ = p)).map (embed root σ v) := by
    ext e
    constructor
    · intro hh
      obtain ⟨hh, hhp⟩ := mem_filter.mp hh
      have hmem := (mem_filter.mp hh).2
      rcases e with ⟨v',e⟩
      have hv : v' = v := (he ⟨v',e⟩).symm.trans ((congrArg root hhp).trans hp)
      subst v'
      exact mem_map.mpr ⟨e, mem_filter.mpr ⟨hmem, hhp⟩, rfl⟩
    · intro hh
      rcases mem_map.mp hh with ⟨a, ha, heq⟩
      rw [← heq]
      obtain ⟨heT, hep⟩ := mem_filter.mp ha
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, heT⟩, hep⟩
  rw [hset, card_map]

theorem out_degree_le (root : P → V) (σ : Perms root) (p : P) :
    (univ.filter (fun e : Channel root σ => src root σ e = p)).card ≤ 8 := by
  classical
  let v := root p
  let a := index root v ⟨p,rfl⟩
  have ha : node root v a = p := by
    change ((index root v).symm ((index root v) ⟨p,rfl⟩)).val = p
    rw [Equiv.symm_apply_apply]
  rw [← selected_univ root σ,
    endpoint_count root σ (fun _ => univ) (src root σ) (src_root root σ) v p rfl, ← ha]
  simpa only [src, (node root v).injective.eq_iff] using
    EightPermChannels.out_degree_le (σ v) a

theorem in_degree_le (root : P → V) (σ : Perms root) (p : P) :
    (univ.filter (fun e : Channel root σ => dst root σ e = p)).card ≤ 8 := by
  classical
  let v := root p
  let a := index root v ⟨p,rfl⟩
  have ha : node root v a = p := by
    change ((index root v).symm ((index root v) ⟨p,rfl⟩)).val = p
    rw [Equiv.symm_apply_apply]
  rw [← selected_univ root σ,
    endpoint_count root σ (fun _ => univ) (dst root σ) (dst_root root σ) v p rfl, ← ha]
  simpa only [dst, (node root v).injective.eq_iff] using
    EightPermChannels.in_degree_le (σ v) a

theorem card_channels_le (root : P → V) (σ : Perms root) :
    Fintype.card (Channel root σ) ≤ 8 * Fintype.card P := by
  classical
  let encode : Channel root σ → Fin 8 × P := fun e => (e.2.val.1, src root σ e)
  have hinj : Function.Injective encode := by
    rintro ⟨v,e⟩ ⟨v',e'⟩ h
    have hpair := Prod.mk.inj h
    have hv : v = v' := by
      have hh := congrArg root hpair.2
      simpa only [src_root] using hh
    subst v'
    have he : e = e' := Subtype.ext (Prod.ext hpair.1 ((node root v).injective hpair.2))
    subst e'
    rfl
  simpa using Fintype.card_le_of_injective encode hinj

theorem route (root : P → V) (σ : Perms root)
    (hσ : ∀ v, ∀ S : Finset (Fin (Fintype.card (Fibre root v))),
      min S.card Sᶜ.card ≤ ∑ j : Fin 8, (S.filter (fun a => σ v j a ∉ S)).card)
    (b : P → ℤ) (hsum : ∀ v, ∑ p : Fibre root v, b p.val = 0)
    (hb : ∀ p, |b p| ≤ 1) :
    ∃ T : Finset (Channel root σ), ∀ p,
      ((T.filter (fun e => dst root σ e = p)).card : ℤ) -
        ((T.filter (fun e => src root σ e = p)).card : ℤ) = b p := by
  classical
  have hloc : ∀ v : V, ∃ T : Finset (EightPermChannels.Channel (σ v)), ∀ a,
      ((T.filter (fun e => EightPermChannels.dst (σ v) e = a)).card : ℤ) -
        ((T.filter (fun e => EightPermChannels.src (σ v) e = a)).card : ℤ) =
          b (node root v a) := by
    intro v
    have hz : ∑ a, b (node root v a) = 0 := by
      calc _ = ∑ p : Fibre root v, b p.val :=
            Equiv.sum_comp (index root v).symm (fun p : Fibre root v => b p.val)
        _ = 0 := hsum v
    exact EightPermChannels.unit_routing_of_perm_cut (σ v) (hσ v)
      (fun a => b (node root v a)) hz (fun a => hb _)
  choose T hT using hloc
  refine ⟨selected root σ T, ?_⟩
  intro p
  let v := root p
  let a := index root v ⟨p,rfl⟩
  have ha : node root v a = p := by
    change ((index root v).symm ((index root v) ⟨p,rfl⟩)).val = p
    rw [Equiv.symm_apply_apply]
  rw [endpoint_count root σ T (dst root σ) (dst_root root σ) v p rfl,
    endpoint_count root σ T (src root σ) (src_root root σ) v p rfl, ← ha]
  simpa only [src, dst, (node root v).injective.eq_iff] using hT v a

/-- The global indexed network is fixed before every root-balanced unit demand. -/
theorem exists_network (root : P → V) :
    ∃ σ : Perms root,
      (∀ e : Channel root σ, root (src root σ e) = root (dst root σ e) ∧
        src root σ e ≠ dst root σ e) ∧
      (∀ p, (univ.filter (fun e : Channel root σ => src root σ e = p)).card ≤ 8) ∧
      (∀ p, (univ.filter (fun e : Channel root σ => dst root σ e = p)).card ≤ 8) ∧
      Fintype.card (Channel root σ) ≤ 8 * Fintype.card P ∧
      ∀ b : P → ℤ, (∀ v, ∑ p : Fibre root v, b p.val = 0) → (∀ p, |b p| ≤ 1) →
        ∃ T : Finset (Channel root σ), ∀ p,
          ((T.filter (fun e => dst root σ e = p)).card : ℤ) -
            ((T.filter (fun e => src root σ e = p)).card : ℤ) = b p := by
  classical
  choose σ hσ using fun v : V =>
    Expander.EightPerm.exists_eight_perm_cut (Fintype.card (Fibre root v))
  refine ⟨σ, ?_, out_degree_le root σ, in_degree_le root σ, card_channels_le root σ,
    fun b hz hb => route root σ hσ b hz hb⟩
  intro e
  refine ⟨(src_root root σ e).trans (dst_root root σ e).symm, ?_⟩
  intro h
  exact EightPermChannels.src_ne_dst (σ e.1) e.2 ((node root e.1).injective h)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.RootChannels

#check PartitionedTriangleAbsorption.BlowupB.LatinCore.RootChannels.exists_network
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.RootChannels.exists_network
