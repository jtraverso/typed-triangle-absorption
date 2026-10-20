/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import PartitionedTriangleAbsorption.BlowupB.CompleteBlowup
public import PartitionedTriangleAbsorption.TypedTransformerLabels

@[expose] public section

/-!
# Vertex splitting (families whose links are disconnected) — data and the edge map

Written proof: `cegis/b0_refiner/DIVISION_VERTICES_PRUEBA_20261014.md`.

A vertex of class `r` is split into one copy per connected component of the link `L_r`; an edge
`uv` is sent to the copies of `u` and `v` chosen by the class of the other endpoint. The data are
packaged in `SplitData F t'`, whose finite conditions are checked by `decide` per family:

* `κ r s : Fin t'` — the split class of a vertex of class `r` along an edge to class `s`;
* `π : Fin t' → Fin t` with `π (κ r s) = r`;
* (O) `{a, b, c} ∈ F → κ a b = κ a c` (the two edges of a triangle at a vertex use one copy);
* `F'` and `sig : Multiset (Fin t) → Multiset (Fin t')`, with `sig {a,b,c} = {κ a b, κ b a, κ c a}`
  on `F`, `sig F ⊆ F'` and `π`-images of `F'` in `F`.

This file: split vertices `SV`, the copy map `cp`, the edge map `φ` (`splitE`), its injectivity on
loopless edge sets, and the transfer of decompositions back from the split side
(`hasDecomp_of_split`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.VertexSplit

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer

variable {t t' : ℕ}

/-- Splitting data for a family `F` on `Fin t` into `t'` classes. -/
structure SplitData (F : Finset (Multiset (Fin t))) (t' : ℕ) where
  κ : Fin t → Fin t → Fin t'
  π : Fin t' → Fin t
  π_κ : ∀ r s, π (κ r s) = r
  /-- every class has an allowed partner (used to make the copy map total) -/
  dflt : Fin t → Fin t
  dflt_allowed : ∀ r, (∃ k, Link F r (dflt r) k) ∨ ∀ s, ¬ ∃ k, Link F r s k
  /-- (O) -/
  obs : ∀ a b c, Link F a b c → κ a b = κ a c
  F' : Finset (Multiset (Fin t'))
  sig : Multiset (Fin t) → Multiset (Fin t')
  sig_tri : ∀ a b c, Link F a b c → sig {a, b, c} = {κ a b, κ b a, κ c a}
  sig_mem : ∀ τ ∈ F, sig τ ∈ F'
  π_mem : ∀ τ' ∈ F', τ'.map π ∈ F

/-- The total copy class (`κ` along allowed pairs, a default otherwise). -/
def SplitData.cls' {F : Finset (Multiset (Fin t))} (S : SplitData F t') (r s : Fin t) : Fin t' :=
  if ∃ k, ({r, s, k} : Multiset (Fin t)) ∈ F then S.κ r s else S.κ r (S.dflt r)

/-- Edge and degree compatibility of `sig` with the counting maps (checked per family). -/
structure SplitData.Compat {F : Finset (Multiset (Fin t))} (S : SplitData F t') : Prop where
  edge : ∀ τ ∈ F, ∀ i' j' : Fin t', typeEdgeVec (S.sig τ) i' j' =
    ∑ i, ∑ j, (if S.cls' i j = i' ∧ S.cls' j i = j' then (1 : ℤ) else 0) * typeEdgeVec τ i j
  deg : ∀ τ ∈ F, ∀ r ∈ τ, ∀ j j' : Fin t', S.π j = r →
    (∑ s, (if S.cls' r s = j ∧ S.cls' s r = j' then (1 : ℤ) else 0) * typeDegVec τ r s) =
      if j ∈ S.sig τ then typeDegVec (S.sig τ) j j' else 0
  sig_π : ∀ τ ∈ F, (S.sig τ).map S.π = τ

variable {F : Finset (Multiset (Fin t))} (S : SplitData F t')

/-- The copy class used by a vertex of class `r` towards class `s` (total version). -/
abbrev SplitData.cls (r s : Fin t) : Fin t' := S.cls' r s

theorem SplitData.cls_of_link {r s k : Fin t} (h : Link F r s k) : S.cls r s = S.κ r s := by
  show S.cls' r s = _
  unfold SplitData.cls'; rw [if_pos ⟨k, h⟩]

theorem SplitData.π_cls (r s : Fin t) : S.π (S.cls r s) = r := by
  show S.π (S.cls' r s) = r
  unfold SplitData.cls'; split_ifs <;> exact S.π_κ _ _

variable {V : Type*} [DecidableEq V] (p : V → Fin t)

/-- Split vertices: a vertex together with one of its copy classes. -/
def SV : Type _ := {x : V × Fin t' // ∃ s, x.2 = S.cls (p x.1) s}

instance [Fintype V] : Fintype (SV S p) := by unfold SV; infer_instance
instance : DecidableEq (SV S p) := by unfold SV; infer_instance

/-- The label of a split vertex. -/
def sp : SV S p → Fin t' := fun x => x.1.2

/-- The copy of `u` used along an edge towards class `s`. -/
def cp (u : V) (s : Fin t) : SV S p := ⟨(u, S.cls (p u) s), s, rfl⟩

@[simp] theorem cp_fst (u : V) (s : Fin t) : (cp S p u s).1.1 = u := rfl
@[simp] theorem sp_cp (u : V) (s : Fin t) : sp S p (cp S p u s) = S.cls (p u) s := rfl

/-- The edge map `φ`. -/
def splitEdge : Sym2 V → Sym2 (SV S p) :=
  Sym2.lift ⟨fun u v => s(cp S p u (p v), cp S p v (p u)), fun u v => Sym2.eq_swap⟩

@[simp] theorem splitEdge_mk (u v : V) :
    splitEdge S p s(u, v) = s(cp S p u (p v), cp S p v (p u)) := rfl

/-- The first projection of split vertices. -/
def fstV : SV S p → V := fun x => x.1.1

@[simp] theorem fstV_cp (u : V) (s : Fin t) : fstV S p (cp S p u s) = u := rfl

theorem map_fst_splitEdge (e : Sym2 V) : Sym2.map (fstV S p) (splitEdge S p e) = e := by
  induction e using Sym2.ind with
  | _ u v => simp [Sym2.map_mk]

theorem splitEdge_injective : Function.Injective (splitEdge S p) := fun e e' h => by
  have := congrArg (Sym2.map (fstV S p)) h
  rwa [map_fst_splitEdge, map_fst_splitEdge] at this

/-- The split edge set. -/
def splitE (E : Finset (Sym2 V)) : Finset (Sym2 (SV S p)) := E.image (splitEdge S p)

theorem card_splitE (E : Finset (Sym2 V)) : (splitE S p E).card = E.card :=
  card_image_of_injective _ (splitEdge_injective S p)

theorem mem_splitE {E : Finset (Sym2 V)} {e : Sym2 V} : splitEdge S p e ∈ splitE S p E ↔ e ∈ E :=
  (splitEdge_injective S p).mem_finset_image

theorem splitE_union (A B : Finset (Sym2 V)) : splitE S p (A ∪ B) = splitE S p A ∪ splitE S p B :=
  image_union _ _

theorem splitE_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    Disjoint (splitE S p A) (splitE S p B) :=
  disjoint_image (splitEdge_injective S p) |>.mpr h

/-- Every edge of a split edge set joins copies of DISTINCT vertices when the source is loopless. -/
theorem fst_ne_of_mem_splitE {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    {x y : SV S p} (h : s(x, y) ∈ splitE S p E) : fstV S p x ≠ fstV S p y := by
  obtain ⟨e, he, hxy⟩ := mem_image.mp h
  have := congrArg (Sym2.map (fstV S p)) hxy
  rw [map_fst_splitEdge, Sym2.map_mk] at this
  intro hfst
  apply hloop e he
  rw [this, hfst]
  exact Sym2.mk_isDiag_iff.mpr rfl

/-- An edge of the split set is the image of its projection. -/
theorem splitEdge_map_fst {E : Finset (Sym2 V)} {f : Sym2 (SV S p)} (hf : f ∈ splitE S p E) :
    splitEdge S p (Sym2.map (fstV S p) f) = f ∧ Sym2.map (fstV S p) f ∈ E := by
  obtain ⟨e, he, rfl⟩ := mem_image.mp hf
  rw [map_fst_splitEdge]
  exact ⟨rfl, he⟩

end PartitionedTriangleAbsorption.BlowupB.VertexSplit
