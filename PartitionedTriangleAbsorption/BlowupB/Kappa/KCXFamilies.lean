/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXFamily1
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXFamily2
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXFamily3
public import PartitionedTriangleAbsorption.BlowupB.Kappa.KCXFamily4

@[expose] public section

/-!
# Four families with one charge of unit `4` whose zero set does not force `3 ∣ e`

`KCX1`–`KCX3`: disconnected, a charged `KappaLinks` component on `0, 1, 2` and the isolated `333`;
`KCX4 = {000,001,012,123,133,233}` (the class "C1"): connected, one component. Inside the
component the lattice is "even, `χ = 0`, `e ≡ 0 mod 3`" (`ChargeTorsionInside` with `ψ` the edge
count). `UniversalCert` by `universalCert_of_ct_components` with templates of charge `±4` and a
4-cycle of charge `0`. Generator: `gen_kcx.py`.
-/

#print axioms PaddedComponents.universalCert_KCX1
#print axioms PaddedComponents.universalCert_KCX2
#print axioms PaddedComponents.universalCert_KCX3
#print axioms PaddedComponents.universalCert_KCX4
