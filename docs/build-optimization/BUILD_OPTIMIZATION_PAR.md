# Build optimization — PAR route, earlier 120 (Kappa) and 17 conserved cases (LatinCore)

Scope: the 431 modules of `BUILD_TARGETS.txt`. Only proofs were changed; no declaration name, type, or statement was modified, no import was changed, no declaration was added or removed (no helper lemmas were needed). `lean-toolchain`, `lake-manifest.json`, `Challenge.lean`, `Solution.lean`, `comparator.json` are untouched. No `sorry`, `native_decide`, `implemented_by`, `extern`, `opaque` or axiom was introduced; every changed file keeps its author header and `module` line, and the largest changed file has 3,964 lines.

All changes were produced by two scripts that are committed with the project (`scripts/rewrite_decide_simp.py`, `scripts/rewrite_ternary_repeat.py`), applied to every occurrence in the target modules, and validated by an incremental `lake build $(cat BUILD_TARGETS.txt)`, which completed successfully (`Build completed successfully (4884 jobs)`) after each of the two rounds. Because the modules use the module system and only proof bodies changed, no downstream module had to be rebuilt.

## Pattern 1 — decide-simp after `fin_cases` (26 modules, 772 occurrences)

Script: `scripts/rewrite_decide_simp.py`. Four generated shapes are rewritten:

* **A. `LatEq` goals** (`fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [K, canon, coeffList, typeEdgeVec, sum_insert] <;> omega`). Rewritten to: expand the family sum once, *before* the case split (`rw [K]; repeat rw [Finset.sum_insert (by decide)]; rw [Finset.sum_singleton]`), unfold the canonical coefficients once (`simp (config := {decide := true}) only [canon, coeffList, ite_true, ite_false]`), then — when every canonical coefficient has the generated form `(numerator) / d` — prove each exact division once (`have hqvk : (num) / d * d = num := Int.ediv_mul_cancel (by omega)`), replace the quotient by a fresh variable (`generalize (num) / d = qvk at *`) and clear the divisibility / nonnegativity hypotheses `p*`, `h3`, `ht`, `n**` that are no longer needed; finally `fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) only [typeEdgeVec, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Fin.reduceFinMk, Fin.isValue, ite_true, ite_false, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.reduceMul, Int.reduceSub, mul_zero, mul_one, zero_add, add_zero] <;> omega`. Each per-cell `omega` now only sees linear equalities (no `∣`, no `/`). Explicit cast lemmas replace `push_cast`/the default simp set.
* **B. `LocalSol` goals** (`fin_cases j <;> simp (config := {decide := true}) [K, FinT.coeffList, typeDegVec, Finset.sum_filter, sum_fin] at * <;> omega`, Fin 6/7 conserved cases). The `at *` (re-simplifying every hypothesis in each of the 6–7 cases) is removed: `rw [Finset.sum_apply, Finset.sum_filter, K]`, explicit `sum_insert`/`sum_singleton`, one `simp only` for the coefficients, then per-case `simp only [typeDegVec, …]` on the goal only.
* **C. witness hypotheses** (`simp (config := {decide := true}) [K, typeEdgeVec, sum_insert] at e00 …`) → `simp (config := {decide := true}) only [K, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, typeEdgeVec, <count/cast lemmas>] at e00 …`.
* **D. witness lower bounds** (`rcases hτ with rfl | … <;> simp (config := {decide := true}) [canon, coeffList, a] <;> omega`) → the same with `simp … only [canon, coeffList, a, Multiset.insert_eq_cons, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero]`.

## Pattern 2 — `repeat' first | exact …_symmetric | … | apply Ternary*.add` (119 modules, 1,626 blocks)

Script: `scripts/rewrite_ternary_repeat.py`. In the generated inverse certificates (`Flex/ParInv/Inv*`, `Kappa/Inverse*`) every `TernarySymmetric`/`TernarySupported` goal for a sum of weights was closed by trying all leaf lemmas with `exact` (default transparency) *before* `apply Ternary*.add`; on a sum goal every failing `exact` unfolds the weight definitions deeply. The rewritten block first tries `with_reducible apply TernarySymmetric.add` / `with_reducible apply TernarySupported.add`, then (symmetric case) the leaf lemmas under `with_reducible exact`, and keeps all original alternatives afterwards as a fallback, so the proof term is unchanged whenever the fast alternatives fail.

## Measured times

### Paired measurements (same machine state, `lake env lean <file>`, original file from the initial commit vs. rewritten file, 3 processes in parallel on an otherwise idle 8-core machine)

| module | wall before (s) | wall after (s) | CPU user before (s) | CPU user after (s) |
|---|---:|---:|---:|---:|
| `Flex/Par/Par5_3` | 261.5 | 98.4 | 255.1 | 94.9 |
| `Kappa/G2Families` | 327.0 | 167.3 | 283.3 | 140.7 |
| `Flex/Par/Par6` | 157.5 | 86.0 | 153.0 | 82.9 |
| `Kappa/G3Families` | 100.0 | 82.7 | 339.9 | 176.7 |
| `LatinCore/Conserved17/StarRemainingC` | 66.6 | 35.9 | 106.9 | 59.4 |
| `Kappa/KMFamilies` | 37.0 | 33.3 | 102.0 | 56.1 |
| `Flex/ParInv/Inv11` | 18.9 | 14.1 | 66.7 | 47.9 |
| `Kappa/InverseKT4` | 8.9 | 10.0 | 12.7 | 8.4 |

Paired measurements of further pattern-1 modules (4 processes in parallel, wall time only): `Kappa/KCTFamilies` 70.0 → 64.5 s, `Kappa/KCCFamilies` 39.6 → 32.4 s, `Kappa/KCXFamily1` 37.5 → 28.0 s, `Kappa/KCXFamily4` 17.5 → 14.7 s, `Kappa/KC2CFamily` 19.2 → 16.9 s, `Kappa/ChargeFamilies` 24.8 → 22.8 s, `Kappa/Families` 23.9 → 21.0 s.

### Build-log times of every changed module

“before” = time reported by lake in the initial full build of the targets (8 jobs in parallel, machine fully loaded); “after” = time reported by lake in the incremental rebuild after the change (round 1 for pattern 1, round 2 for pattern 2; up to 8 jobs in parallel). These numbers depend strongly on the machine load at the moment each module was compiled (e.g. modules that started at the same moment as seven others look slower), so the paired measurements above are the reliable comparison; the table is given for completeness.

| module | pattern | before (s) | after (s) |
|---|---|---:|---:|
| `Flex.Par.Par5_3` | 1 | 699 | 108 |
| `Kappa.G2Families` | 1 | 538 | 179 |
| `Flex.Par.Par5_4` | 1 | 392 | 71 |
| `Flex.Par.Par6` | 1 | 352 | 90 |
| `Flex.Par.Par5_1` | 1 | 303 | 68 |
| `LatinCore.Conserved17.StarRemainingC` | 1 | 205 | 46 |
| `LatinCore.Conserved17.StarRemainingB` | 1 | 180 | 43 |
| `Flex.Par.Par5_0` | 1 | 174 | 128 |
| `Flex.Par.Par5_2` | 1 | 173 | 125 |
| `Kappa.G3Families` | 1 | 164 | 107 |
| `LatinCore.Conserved17.StarRemainingA` | 1 | 158 | 37 |
| `Kappa.KMFamilies` | 1 | 100 | 76 |
| `Kappa.KEFamilies` | 1 | 84 | 62 |
| `Flex.ParInv.Inv11` | 2 | 73 | 53 |
| `Flex.ParInv.Inv08` | 2 | 70 | 53 |
| `Flex.ParInv.Inv09` | 2 | 70 | 53 |
| `Flex.ParInv.Inv03` | 2 | 69 | 53 |
| `Kappa.KCTFamilies` | 1 | 69 | 116 |
| `Flex.ParInv.Inv32` | 2 | 68 | 52 |
| `Flex.ParInv.Inv31` | 2 | 67 | 52 |
| `Flex.ParInv.Inv30` | 2 | 65 | 50 |
| `Kappa.KC3TFamily` | 1 | 64 | 35 |
| `Flex.ParInv.Inv52` | 2 | 63 | 46 |
| `Flex.ParInv.Inv28` | 2 | 62 | 51 |
| `Flex.ParInv.Inv29` | 2 | 62 | 51 |
| `Flex.ParInv.Inv25` | 2 | 60 | 51 |
| `Flex.ParInv.Inv27` | 2 | 60 | 51 |
| `Flex.ParInv.Inv47` | 2 | 60 | 46 |
| `Kappa.KCXFamily3` | 1 | 60 | 38 |
| `Flex.ParInv.Inv18` | 2 | 59 | 50 |
| `Flex.ParInv.Inv19` | 2 | 59 | 51 |
| `Flex.ParInv.Inv26` | 2 | 59 | 50 |
| `Flex.ParInv.Inv45` | 2 | 59 | 52 |
| `Flex.ParInv.Inv50` | 2 | 59 | 42 |
| `Flex.ParInv.Inv24` | 2 | 58 | 42 |
| `Flex.ParInv.Inv43` | 2 | 58 | 52 |
| `Flex.ParInv.Inv46` | 2 | 58 | 52 |
| `Flex.ParInv.Inv58` | 2 | 58 | 45 |
| `Kappa.KCXFamily2` | 1 | 58 | 33 |
| `Flex.ParInv.Inv12` | 2 | 57 | 51 |
| `Flex.ParInv.Inv17` | 2 | 56 | 48 |
| `Flex.ParInv.Inv22` | 2 | 56 | 49 |
| `Flex.ParInv.Inv51` | 2 | 56 | 44 |
| `Flex.ParInv.Inv60` | 2 | 56 | 49 |
| `Flex.ParInv.Inv49` | 2 | 55 | 41 |
| `Flex.ParInv.Inv23` | 2 | 54 | 48 |
| `Flex.ParInv.Inv14` | 2 | 53 | 47 |
| `Flex.ParInv.Inv37` | 2 | 52 | 56 |
| `Flex.ParInv.Inv05` | 2 | 51 | 57 |
| `Flex.ParInv.Inv54` | 2 | 50 | 45 |
| `Flex.ParInv.Inv57` | 2 | 49 | 43 |
| `Flex.ParInv.Inv40` | 2 | 48 | 42 |
| `Flex.ParInv.Inv41` | 2 | 48 | 50 |
| `Flex.ParInv.Inv64` | 2 | 48 | 52 |
| `Flex.ParInv.Inv01` | 2 | 47 | 50 |
| `Flex.ParInv.Inv04` | 2 | 47 | 52 |
| `Flex.ParInv.Inv44` | 2 | 47 | 50 |
| `Flex.ParInv.Inv63` | 2 | 47 | 54 |
| `Flex.ParInv.Inv02` | 2 | 46 | 51 |
| `Flex.ParInv.Inv10` | 2 | 46 | 54 |
| `Flex.ParInv.Inv42` | 2 | 46 | 52 |
| `Flex.ParInv.Inv48` | 2 | 46 | 42 |
| `Flex.ParInv.Inv38` | 2 | 45 | 50 |
| `Flex.ParInv.Inv39` | 2 | 45 | 49 |
| `Flex.ParInv.Inv56` | 2 | 45 | 49 |
| `Flex.ParInv.Inv00` | 2 | 44 | 45 |
| `Flex.ParInv.Inv07` | 2 | 44 | 52 |
| `Flex.ParInv.Inv21` | 2 | 44 | 52 |
| `Flex.ParInv.Inv06` | 2 | 43 | 52 |
| `Flex.ParInv.Inv13` | 2 | 43 | 48 |
| `Flex.ParInv.Inv20` | 2 | 43 | 50 |
| `Flex.ParInv.Inv34` | 2 | 42 | 51 |
| `Flex.ParInv.Inv69` | 2 | 42 | 22 |
| `Kappa.FamiliesT234` | 1 | 42 | 26 |
| `Flex.ParInv.Inv33` | 2 | 41 | 50 |
| `Flex.ParInv.Inv53` | 2 | 41 | 46 |
| `Flex.ParInv.Inv55` | 2 | 41 | 46 |
| `Flex.ParInv.Inv67` | 2 | 37 | 32 |
| `Kappa.KCXFamily1` | 1 | 35 | 37 |
| `Kappa.KCXFamily4` | 1 | 34 | 30 |
| `Flex.ParInv.Inv35` | 2 | 33 | 52 |
| `Flex.ParInv.Inv36` | 2 | 33 | 52 |
| `Flex.ParInv.Inv61` | 2 | 31 | 37 |
| `Kappa.KCCFamilies` | 1 | 31 | 59 |
| `Flex.ParInv.Inv16` | 2 | 26 | 38 |
| `Flex.ParInv.Inv62` | 2 | 26 | 55 |
| `Flex.ParInv.Inv15` | 2 | 25 | 42 |
| `Flex.ParInv.Inv66` | 2 | 25 | 35 |
| `Flex.ParInv.Inv68` | 2 | 25 | 23 |
| `Flex.ParInv.Inv59` | 2 | 24 | 25 |
| `Flex.ParInv.Inv65` | 2 | 24 | 44 |
| `Kappa.KC2CFamily` | 1 | 24 | 20 |
| `Kappa.InverseKCX2` | 2 | 22 | 15 |
| `Kappa.InverseKCX3` | 2 | 22 | 15 |
| `Kappa.InverseKCX4` | 2 | 22 | 15 |
| `Kappa.InverseKTB1` | 2 | 22 | 16 |
| `Kappa.InverseKTB2` | 2 | 22 | 15 |
| `Kappa.InverseKTH2` | 2 | 22 | 13 |
| `Kappa.InverseKTH3` | 2 | 22 | 13 |
| `Kappa.InverseKCX1` | 2 | 21 | 14 |
| `Kappa.InverseKTA1` | 2 | 21 | 15 |
| `Kappa.InverseKTB3` | 2 | 21 | 15 |
| `Kappa.InverseKTH1` | 2 | 21 | 15 |
| `Kappa.InverseKTH4` | 2 | 20 | 13 |
| `Kappa.InverseKCT5` | 2 | 18 | 14 |
| `Kappa.InverseKQ4` | 2 | 18 | 18 |
| `Kappa.InverseKQ8` | 2 | 18 | 19 |
| `Kappa.InverseKCT4` | 2 | 17 | 13 |
| `Kappa.InverseKCT6` | 2 | 17 | 14 |
| `Kappa.InverseKQ1` | 2 | 17 | 17 |
| `Kappa.InverseKQ2` | 2 | 17 | 17 |
| `Kappa.InverseKQ3` | 2 | 17 | 17 |
| `Kappa.InverseKQ6` | 2 | 17 | 18 |
| `Kappa.InverseKCT2` | 2 | 16 | 14 |
| `Kappa.InverseKM3` | 2 | 16 | 13 |
| `Kappa.InverseKQ10` | 2 | 16 | 16 |
| `Kappa.InverseKQ7` | 2 | 16 | 18 |
| `Kappa.InverseKCT3` | 2 | 15 | 14 |
| `Kappa.InverseKM2` | 2 | 15 | 14 |
| `Kappa.InverseKQ5` | 2 | 15 | 17 |
| `Kappa.InverseKQ9` | 2 | 15 | 14 |
| `Kappa.InverseKT2` | 2 | 15 | 14 |
| `Kappa.InverseKT3` | 2 | 15 | 13 |
| `Kappa.InverseKT4` | 2 | 15 | 13 |
| `Kappa.InverseKC2C` | 2 | 14 | 14 |
| `Kappa.InverseKCT1` | 2 | 14 | 14 |
| `Kappa.InverseKCa` | 2 | 14 | 13 |
| `Kappa.InverseKCb` | 2 | 14 | 13 |
| `Kappa.InverseKE3` | 2 | 14 | 12 |
| `Kappa.InverseKE4` | 2 | 14 | 12 |
| `Kappa.InverseKM1` | 2 | 14 | 13 |
| `Kappa.InverseKQ11` | 2 | 14 | 14 |
| `Kappa.InverseKT1` | 2 | 14 | 13 |
| `Kappa.InverseKE2` | 2 | 13 | 12 |
| `Kappa.InverseKM4` | 2 | 13 | 13 |
| `Kappa.InverseKM5` | 2 | 13 | 13 |
| `Kappa.InverseKC3T` | 2 | 12 | 13 |
| `Kappa.InverseKCC3` | 2 | 12 | 14 |
| `Kappa.InverseKE1` | 2 | 12 | 11 |
| `Kappa.ChargeFamilies` | 1 | 11 | 39 |
| `Kappa.Families` | 1 | 11 | 32 |
| `Kappa.InverseKCC2` | 2 | 11 | 14 |
| `Kappa.InverseKCC1` | 2 | 10 | 13 |
| `LatinCore.Conserved17.StarExample` | 1 | 9 | 7 |
| `LatinCore.Conserved17.StarMono` | 1 | 6 | 5 |
| **total (145 modules)** | | **8229** | **5641** |

## Spot check

```
'PaddedComponents.scalar_inside_KQ1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PartitionedTriangleAbsorption.BlowupB.LatinCore.Conserved17.Star14_0.localSol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PaddedComponents.typeWeightF_PAR044_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(`scalar_inside_KQ1_1` in `Kappa/G3Families` and `Star14_0.localSol` in `LatinCore/Conserved17/StarRemainingC` are rewritten by pattern 1, `typeWeightF_PAR044_symmetric` in `Flex/ParInv/Inv11` by pattern 2.)

