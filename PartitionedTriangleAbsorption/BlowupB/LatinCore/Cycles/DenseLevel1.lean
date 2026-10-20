/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.DenseSpec
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoCutHub

@[expose] public section

/-!
# First level of the dense reduction: local pieces around a good hub partition

Vertices: old vertices `V`, one hub per part `P`, five private vertices per arc, and the
vertices `U'` of the (later) hub-level reserve.  For an arc `e = u → v` of `Y`:

* `π_e : v → x₀ → u`,
* `O_e : u → x₁ → x₂ → hub (p u)` and `I_e : hub (p v) → x₃ → x₄ → v`,
* `Q_e : hub (p u) → hub (p v)`, a single hub-level arc (hubs carry the colour of their part).

Pieces: the triangle `e + π_e`, the basal `9`-cycle `π_e + O_e + Q_e + I_e`, and the transition
`6`-cycle `I_e + O_f` for `e.2 = f.1`.  All lengths are uniform, so no colour case split occurs.
-/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles

open Finset

namespace DenseRed

open Hub (ne_of_cyc deg_biUnion)

/-- Vertex type of the reduction. -/
abbrev TV (V P U' : Type*) := V ⊕ (P ⊕ (((V × V) × Fin 5) ⊕ U'))

instance instDecEqTV {V P U' : Type*} [DecidableEq V] [DecidableEq P] [DecidableEq U'] :
    DecidableEq (TV V P U') :=
  inferInstanceAs (DecidableEq (V ⊕ (P ⊕ (((V × V) × Fin 5) ⊕ U'))))

section Defs

variable {V P U' : Type*}

def old (v : V) : TV V P U' := Sum.inl v
def hub (a : P) : TV V P U' := Sum.inr (Sum.inl a)
def pv (e : V × V) (k : Fin 5) : TV V P U' := Sum.inr (Sum.inr (Sum.inl (e, k)))
def ext (u : U') : TV V P U' := Sum.inr (Sum.inr (Sum.inr u))

/-- Inclusion of the hub-level vertex type `P ⊕ U'`. -/
def ι : P ⊕ U' → TV V P U' := Sum.elim hub ext

lemma ι_injective : Function.Injective (ι (V := V) (P := P) (U' := U')) := by
  rintro (a | a) (b | b) h <;> simp_all [ι, hub, ext]

def ιE : (P ⊕ U') ↪ TV V P U' := ⟨ι, ι_injective⟩

/-- Inclusion of hub-level arcs. -/
def arcE : (P ⊕ U') × (P ⊕ U') ↪ TV V P U' × TV V P U' := Function.Embedding.prodMap ιE ιE

lemma arcE_apply (x : (P ⊕ U') × (P ⊕ U')) : arcE (V := V) x = (ι x.1, ι x.2) := rfl

lemma arcE_lift (a b : P) :
    arcE (V := V) (U' := U') (liftArc P U' (a, b)) = (hub a, hub b) := rfl

/-- Colours of the private vertices. -/
def pcol (c : V → ZMod 3) (x : (V × V) × Fin 5) : ZMod 3 :=
  ![c x.1.2 + 1, c x.1.1 + 1, c x.1.1 + 2, c x.1.2 + 1, c x.1.2 + 2] x.2

/-- All colours. -/
def tcol (c : V → ZMod 3) (col : P → ZMod 3) (cU : U' → ZMod 3) : TV V P U' → ZMod 3 :=
  Sum.elim c (Sum.elim col (Sum.elim (pcol c) cU))

variable [DecidableEq V] [DecidableEq P] [DecidableEq U'] (p : V → P)

def piA (e : V × V) : Finset (TV V P U' × TV V P U') :=
  {((old e.2 : TV V P U'), (pv e 0 : TV V P U')), ((pv e 0 : TV V P U'), (old e.1 : TV V P U'))}
def OA (e : V × V) : Finset (TV V P U' × TV V P U') :=
  {((old e.1 : TV V P U'), (pv e 1 : TV V P U')), ((pv e 1 : TV V P U'), (pv e 2 : TV V P U')),
    ((pv e 2 : TV V P U'), (hub (p e.1) : TV V P U'))}
def IA (e : V × V) : Finset (TV V P U' × TV V P U') :=
  {((hub (p e.2) : TV V P U'), (pv e 3 : TV V P U')), ((pv e 3 : TV V P U'), (pv e 4 : TV V P U')),
    ((pv e 4 : TV V P U'), (old e.2 : TV V P U'))}
def QA (e : V × V) : Finset (TV V P U' × TV V P U') :=
  {((hub (p e.1) : TV V P U'), (hub (p e.2) : TV V P U'))}

def Ccyc (e : V × V) : Finset (TV V P U' × TV V P U') :=
  piA (P := P) (U' := U') e ∪ OA p e ∪ QA p e ∪ IA p e
def Tcyc (e : V × V) : Finset (TV V P U' × TV V P U') :=
  insert ((old e.1 : TV V P U'), (old e.2 : TV V P U')) (piA e)
def Dcyc (e f : V × V) : Finset (TV V P U' × TV V P U') := IA (U' := U') p e ∪ OA p f

end Defs

section Cycles

variable {V P U' : Type*} [DecidableEq V] [DecidableEq P] [DecidableEq U'] (p : V → P)

/-- The vertex sequence of the basal cycle. -/
def f9 (e : V × V) : Fin 9 → TV V P U' :=
  ![old e.1, pv e 1, pv e 2, hub (p e.1), hub (p e.2), pv e 3, pv e 4, old e.2, pv e 0]

lemma Ccyc_eq (e : V × V) : Ccyc (U' := U') p e = cycF (f9 p e) := by
  ext a
  simp only [Ccyc, piA, OA, IA, QA, f9, mem_cycF, Fin.exists_fin_succ, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  simp [eq_comm, or_assoc]
  tauto

lemma f9_injective {e : V × V} (hne : e.1 ≠ e.2) (hp : p e.1 ≠ p e.2) :
    Function.Injective (f9 (U' := U') p e) := by
  rw [← List.nodup_ofFn]
  simp [List.ofFn_succ, f9, old, pv, hub, hne, hp, Ne.symm hne]

lemma Tcyc_eq (e : V × V) : Tcyc (P := P) (U' := U') e = cycF ![old e.1, old e.2, pv e 0] := by
  ext a; simp [Tcyc, piA, mem_cycF, Fin.exists_fin_succ, eq_comm]

lemma T3_injective {e : V × V} (hne : e.1 ≠ e.2) :
    Function.Injective (![old e.1, old e.2, pv e 0] : Fin 3 → TV V P U') := by
  rw [← List.nodup_ofFn]
  simp [List.ofFn_succ, old, pv, hne]

def f6 (e f : V × V) : Fin 6 → TV V P U' :=
  ![hub (p e.2), pv e 3, pv e 4, old e.2, pv f 1, pv f 2]

lemma Dcyc_eq {e f : V × V} (hef : e.2 = f.1) : Dcyc (U' := U') p e f = cycF (f6 p e f) := by
  ext a
  simp only [Dcyc, OA, IA, f6, mem_cycF, Fin.exists_fin_succ, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  simp [eq_comm, hef, or_assoc]

lemma f6_injective (e f : V × V) : Function.Injective (f6 (U' := U') p e f) := by
  rw [← List.nodup_ofFn]
  simp [List.ofFn_succ, f6, old, pv, hub]

lemma isDirCycle_C {e : V × V} (hne : e.1 ≠ e.2) (hp : p e.1 ≠ p e.2) :
    IsDirCycle (Ccyc (U' := U') p e) ∧ (Ccyc (U' := U') p e).card ≤ 9 := by
  rw [Ccyc_eq]
  exact ⟨isDirCycle_cycF (f9_injective p hne hp), by rw [card_cycF (f9_injective p hne hp)]⟩

lemma isDirCycle_T {e : V × V} (hne : e.1 ≠ e.2) :
    IsDirCycle (Tcyc (P := P) (U' := U') e) ∧ (Tcyc (P := P) (U' := U') e).card ≤ 9 := by
  rw [Tcyc_eq]
  exact ⟨isDirCycle_cycF (T3_injective hne), by rw [card_cycF (T3_injective hne)]; norm_num⟩

lemma isDirCycle_D {e f : V × V} (hef : e.2 = f.1) :
    IsDirCycle (Dcyc (U' := U') p e f) ∧ (Dcyc (U' := U') p e f).card ≤ 9 := by
  rw [Dcyc_eq p hef]
  exact ⟨isDirCycle_cycF (f6_injective p e f), by rw [card_cycF (f6_injective p e f)]; norm_num⟩

lemma zmod3_add3 (x : ZMod 3) : x + 2 + 1 = x := by
  -- 4.35 port: `fin_cases x <;> decide` no longer finds the `Decidable` instance
  revert x; decide

lemma zmod3_add3' (x : ZMod 3) : x + 1 + 1 + 1 = x := by
  -- 4.35 port: `fin_cases x <;> decide` no longer finds the `Decidable` instance
  revert x; decide

lemma isCyc_Ccyc (c : V → ZMod 3) (col : P → ZMod 3) (cU : U' → ZMod 3) {e : V × V}
    (he : c e.2 = c e.1 + 1) (h1 : col (p e.1) = c e.1) (h2 : col (p e.2) = c e.2) :
    IsCyc (tcol c col cU) (Ccyc p e) := by
  intro a ha
  simp only [Ccyc, piA, OA, IA, QA, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at ha
  rcases ha with (((rfl | rfl) | (rfl | rfl | rfl)) | rfl) | (rfl | rfl | rfl) <;>
    simp only [tcol, pcol, old, pv, hub, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, h1, h2, he] <;>
    simp [add_assoc, zmod3_add3, zmod3_add3', he] <;>
    (try rw [he]) <;> (try ring_nf) <;> (try decide) <;>
    (try (generalize c e.1 = x; fin_cases x <;> decide))

end Cycles

end DenseRed

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles
