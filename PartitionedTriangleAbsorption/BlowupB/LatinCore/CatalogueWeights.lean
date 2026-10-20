/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Cycles.MesoscopicSpec

@[expose] public section

/-! Exact weights of the SAME indexed catalogue. These identities connect
the combinatorial producer to the numerical embedding budget; they do not
assume an independently chosen fractional weighting or physical embedding. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights

open Finset Cycles

variable {V : Type} [DecidableEq V]

def arcs (lib : Finset (Finset (V × V))) : Finset (V × V) := lib.biUnion id

def weight (lib : Finset (Finset (V × V))) (e : V × V) : ℕ :=
  (lib.filter (fun P => e ∈ P)).card

theorem positive (lib : Finset (Finset (V × V))) {e : V × V} (he : e ∈ arcs lib) :
    1 ≤ weight lib e := by
  obtain ⟨P,hP,heP⟩ := mem_biUnion.mp he
  exact card_pos.mpr ⟨P,mem_filter.mpr ⟨hP,heP⟩⟩

theorem total (lib : Finset (Finset (V × V))) :
    ∑ e ∈ arcs lib, weight lib e = ∑ P ∈ lib, P.card := by
  simp only [weight, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro P hP
  rw [← card_filter]
  apply congrArg Finset.card
  ext e
  simp only [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_biUnion.mpr ⟨P,hP,h⟩,h⟩⟩

theorem total_le (lib : Finset (Finset (V × V))) (K : ℕ)
    (hK : ∀ P ∈ lib, P.card ≤ K) :
    ∑ e ∈ arcs lib, weight lib e ≤ K * lib.card := by
  rw [total]
  calc _ ≤ ∑ _P ∈ lib, K := sum_le_sum hK
    _ = _ := by simp [mul_comm]

theorem endpoint (lib : Finset (Finset (V × V))) (endpt : V × V → V) (v : V) :
    (∑ e ∈ arcs lib, if endpt e = v then weight lib e else 0) =
      ∑ P ∈ lib, (P.filter (fun e => endpt e = v)).card := by
  have hexpand : ∀ e, (if endpt e = v then weight lib e else 0) =
      ∑ P ∈ lib, if e ∈ P ∧ endpt e = v then 1 else 0 := by
    intro e
    by_cases h : endpt e = v <;> simp [weight, card_filter, h]
  simp_rw [hexpand]
  rw [sum_comm]
  apply sum_congr rfl
  intro P hP
  rw [← card_filter]
  apply congrArg Finset.card
  ext e
  simp only [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_biUnion.mpr ⟨P,hP,h.1⟩,h⟩⟩

theorem incident (lib : Finset (Finset (V × V))) (v : V) :
    (∑ e ∈ arcs lib, if e.2 = v then weight lib e else 0) +
      (∑ e ∈ arcs lib, if e.1 = v then weight lib e else 0) = catalogLoad lib v := by
  rw [endpoint lib Prod.snd v, endpoint lib Prod.fst v, ← sum_add_distrib]
  rfl

theorem weight_le_load (lib : Finset (Finset (V × V))) {e : V × V}
    (he : e ∈ arcs lib) : weight lib e ≤ catalogLoad lib e.1 := by
  have hsingle : weight lib e ≤
      ∑ a ∈ arcs lib, if a.1 = e.1 then weight lib a else 0 := by
    have hh := single_le_sum (s := arcs lib)
      (f := fun a => if a.1 = e.1 then weight lib a else 0)
      (fun _ _ => Nat.zero_le _) he
    simpa using hh
  rw [← incident lib e.1]
  exact hsingle.trans (Nat.le_add_left _ _)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights.total_le
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights.incident
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.CatalogueWeights.weight_le_load
