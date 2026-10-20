/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.LatinCore.PhysicalProducer
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.CoreComponent
public import PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.NonLatin

@[expose] public section

/-! Unconditional family certificates for the seventeen conserved cases.
The native physical producer supplies the core; the remaining components
use their independent star certificates. The common scale precedes the host. -/

namespace PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.TypedTransformer
open PaddedGeneral.RealInverse BalFixer

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem family_certificate (d : Case) (hd : Checked d) (L : ℕ)
    (hU : RefinerAbsorber.UniversalFamilyCert Bridge.F_tri L)
    (hN : NonCoreAt d L) : UniversalCertFlexL d.F (L + 11) := by
  classical
  apply universalCertFlexL_of_split d.F d.S hd.compat hd.size.1 hd.size.2
    hd.pair hd.surj d.comp hd.component hd.inside L
  intro k
  have hcert : (∀ r, d.comp r ≠ k) ∨
      ComponentCertFlexTL (componentFamily d k) d.comp k L := by
    by_cases hk : k = d.core
    · subst k
      exact Or.inr (core_certificate d hd L hU)
    · exact hN k hk
  rcases hcert with he | hc
  · exact Or.inl he
  · right
    refine ⟨componentFamily d k, filter_subset _ _, ?_, ?_, hc⟩
    · intro τ hτ
      exact (mem_filter.mp hτ).2
    · intro τ hτ hinside
      exact mem_filter.mpr ⟨hτ, hinside⟩

theorem all_family_certificates :
    ∃ L, ∀ i : Fin 17, UniversalCertFlexL (cases i).F L := by
  obtain ⟨LC, hC⟩ := PhysicalProducer.triUniversalCert
  obtain ⟨LN, hN⟩ := noncore_common_scale
  let L := max LC LN
  have hC' : RefinerAbsorber.UniversalFamilyCert Bridge.F_tri L := by
    intro V _ _ p G _ ω δ ρ hs
    exact hC V p G ω δ ρ (flexScales_mono (le_max_left LC LN) hs)
  refine ⟨L + 11, ?_⟩
  intro i
  exact family_certificate (cases i) (all_checked i) L hC'
    (noncore_at_mono (cases i) (le_max_right LC LN) (hN i))

theorem family_facts : ∀ i : Fin 17, PaddedGeneral.FamilyFacts (cases i).F := by
  intro i
  refine ⟨(all_checked i).card_three, ?_, ?_⟩
  · fin_cases i <;> unfold Link <;> decide +kernel
  · fin_cases i <;> unfold Link <;> decide +kernel

theorem all_typed_specs : ∀ i : Fin 17, KeevashTypedSpec (cases i).F := by
  obtain ⟨L, hL⟩ := all_family_certificates
  intro i
  exact keevashTypedSpec_of_flexible_absorberL (cases i).F (family_facts i) L (hL i)

end PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17

#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.family_certificate
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.all_family_certificates
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.family_facts
#print axioms PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.all_typed_specs
