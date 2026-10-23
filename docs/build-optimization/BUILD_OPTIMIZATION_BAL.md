# Build optimization — BAL route (`PartitionedTriangleAbsorption/BlowupB/BalFixer/`)

## Scope and constraints

* Only modules listed in `BUILD_TARGETS.txt` were edited (134 of the 186 targets).
* `lean-toolchain`, `lake-manifest.json`, `Challenge.lean`, `Solution.lean`, `comparator.json` and every
  non-target module are unchanged.
* Every declaration keeps its name and type. Only proof scripts changed. The only added declarations
  are two `private` helper theorems per rewritten `Fam` file (`sum_coeffList_mul_aux`,
  `sum_coeffList_smul_apply_aux`).
* No `sorry`, no new axioms, no `native_decide` / `implemented_by` / `extern` / `opaque`. Author headers and
  `module` lines are kept. The largest file is `Fam/Bal21.lean` at 9,425 lines.

## Patterns rewritten (applied by script, then checked module by module)

The rewrite scripts are in `scripts/bal_build_optimization/`:

* `rewrite_bal_families.py`: patterns 1–4
* `rewrite_hvert.py`: pattern 5
* `nlinarith_to_linarith.py`: pattern 6

### 1. Local solutions (`localSol_*`, nontrivial classes)
Before:
```lean
funext j
fin_cases j <;> simp (config := {decide := true}) [K_…, FinT.coeffList, typeDegVec,
  Finset.sum_filter, Finset.sum_insert] at * <;> omega
```
After: the sum over the class's type set, weighted by `FinT.coeffList l`, is rewritten in one step to a list
sum. The step uses the private helper `sum_coeffList_smul_apply_aux`, whose side conditions (nodup and
membership) are closed by `decide +kernel`. After that, only `simp only` with explicit lemma lists is used:
```lean
funext j
rw [sum_coeffList_smul_apply_aux _ _ _ _ (by simp only [List.map_cons, List.map_nil]; decide +kernel)
  (by simp only [List.map_cons, List.map_nil]; decide +kernel)]
simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Multiset.insert_eq_cons,
  Multiset.count_cons, Multiset.count_singleton, typeDegVec]
try simp only [Fin.reduceFinMk, …, true_implies, false_implies] at hb
fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.reduceAdd,
  Nat.cast_ofNat, Int.reduceSub, Int.reduceMul, Int.reduceAdd, mul_zero, mul_one, …] <;> omega
```
This also avoids `push_cast`: casts are handled by `Nat.cast_ofNat` / `Nat.cast_zero` / `Nat.cast_one`.

### 2. Trivial classes
Before: `funext j; fin_cases j <;> simp_all`.
After: `simp only [zero_smul, Finset.sum_const_zero, Pi.zero_apply]; fin_cases j <;> assumption`
(or the equivalent closing step).

### 3. Scalar lattice goals (`scalar_*`)
Before: one large `simp (config := {decide := true}) [canon_…, FinT.coeffList, sum_insert, …]` followed by
`omega` on every goal. After:

* the parity, balance and `h3` hypotheses are first simplified using the vanishing (`z…`) and support (`s…`)
  facts;
* for each division coefficient, an explicit divisibility fact `have qk : n ∣ E := by omega` is added. The
  quotient is then obtained (`obtain ⟨a, hak⟩`) and the hypotheses it used are cleared;
* `rw [canon_…, sum_coeffList_mul_aux …]` and `rw [hak, Int.mul_ediv_cancel_left]` replace the generic simp;
* each goal is closed by `simp only [<exact list>] <;> clear … <;> omega`, so `omega` sees small contexts.

### 4. Support certificates
`(by unfold Link K_…; decide)` became `decide +kernel` (with the same `unfold`). The kernel checks the
certificate directly, without elaborator-side `Decidable` evaluation.

### 5. Vertex/parity side goals (`hvert`)
Before: `simp (config := {decide := true}) [B_…, σ_…, β_…, Fin.sum_univ_n] at hpar hb ⊢ <;> omega`.
After: `simp only [<same definitions>, Fin.reduceFinMk, Matrix.cons_val…, Finset.mem_insert,
Finset.mem_singleton, Finset.notMem_empty, true_implies, …] at hpar hb ⊢ <;> omega`.

### 6. `nlinarith` → `linarith` (non-`Fam` modules)
In `BalScales*`, `BalComponent*` and `BalLibraryChi*`, each `nlinarith [...]` call was tried as
`linarith [...]` with the same hint terms. The replacement was kept wherever it compiled. Calls that
genuinely need products (some in `BalScales*`) are still `nlinarith`.

## Validation

1. Each rewritten file was compiled individually with `lake env lean <file>`. None of the 121 `Fam`
   modules needed a fallback to the original tactic.
2. A final incremental build of the full target list (`lake build $(cat BUILD_TARGETS.txt)`) completed
   successfully (4,495 jobs, about 19.5 min wall time on this machine, all dependencies already built).
3. `#print axioms`, collected for every `keevashTypedSpec_*` and other `#print axioms` line in the build, shows
   only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorryAx`.

**Side effect:** the build now emits many more linter warnings ("This simp argument is unused"). The
explicit `simp only` lists are shared across classes, so some lemmas are unused in individual classes. These
warnings are harmless and do not affect correctness.

### Spot check
```lean
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.scalar_BAL210_0
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.localSol_BAL210_2
#print axioms PartitionedTriangleAbsorption.BlowupB.BalFixer.Fam.keevashTypedSpec_BAL210
```
For each of these, and for `tors_scales` (from `BalScalesTors`), the output is:
`depends on axioms: [propext, Classical.choice, Quot.sound]`

## Timings

Methodology and caveats:

* **Per-module table:** wall time of each module as reported by `lake build`. "Before" comes from the
  initial full build of the target list on the original sources. "After" comes from the final incremental
  build. Both builds ran with up to 8 parallel jobs on the same machine, so individual figures include
  contention noise. Note that 8 jobs is more parallelism than the 4-core runner.
* **CPU user column:** user CPU of a separate single-file `lake env lean` run of the rewritten file, where
  measured.
* **Controlled single-file comparison for `Fam/Bal21`** (same machine, `lake env lean`, sequential):
  * original: 484.5 s real / 463.1 s user
  * rewritten: 156.8 s real / 143.1 s user
  * speedup: **3.2×**
* **Per-family profile (`BAL210`):** about 55 s → 22 s user. `localSol_*` dropped from about 9.8 s to 1.4 s
  per class, and `scalar_*` from about 12 s to 2.4 s.

| module (`BlowupB/BalFixer/…`) | before (s) | after (s) | ratio | after, CPU user (s) |
|---|---:|---:|---:|---:|
| `Fam.Bal16` | 537.0 | 173.0 | 3.1× | 151.85 |
| `Fam.Bal21` | 537.0 | 169.0 | 3.2× | 150.01 |
| `BalScalesTors` | 455.0 | 211.0 | 2.2× | – |
| `Fam.BalC05` | 440.0 | 147.0 | 3.0× | 122.26 |
| `Fam.BalCY1` | 426.0 | 161.0 | 2.6× | 138.78 |
| `Fam.Bal06PartA` | 423.0 | 100.0 | 4.2× | 77.81 |
| `Fam.Bal15` | 421.0 | 142.0 | 3.0× | 126.86 |
| `Fam.Bal11Part3` | 416.0 | 104.0 | 4.0× | 78.65 |
| `Fam.Bal07Part1` | 403.0 | 102.0 | 4.0× | 82.57 |
| `Fam.Bal11Part2` | 375.0 | 100.0 | 3.8× | 78.27 |
| `Fam.Bal12Part1` | 372.0 | 93.0 | 4.0× | 73.61 |
| `Fam.Bal22Part1` | 361.0 | 93.0 | 3.9× | 79.32 |
| `Fam.Bal17Part2` | 345.0 | 93.0 | 3.7× | 77.8 |
| `Fam.Bal18` | 342.0 | 119.0 | 2.9× | 101.72 |
| `BalScalesChiY` | 340.0 | 163.0 | 2.1× | – |
| `BalScalesChiYM` | 340.0 | 161.0 | 2.1× | – |
| `Fam.Bal11Part1` | 337.0 | 81.0 | 4.2× | 64.19 |
| `Fam.Bal03` | 335.0 | 150.0 | 2.2× | 137.66 |
| `Fam.Bal17Part3` | 333.0 | 94.0 | 3.5× | 79.23 |
| `Fam.Bal20Part1` | 333.0 | 100.0 | 3.3× | 86.15 |
| `Fam.Bal06PartB` | 327.0 | 84.0 | 3.9× | 68.8 |
| `Fam.Bal14Part2` | 325.0 | 95.0 | 3.4× | 80.18 |
| `Fam.Bal07Part2` | 320.0 | 88.0 | 3.6× | 70.68 |
| `Fam.Bal14Part3` | 317.0 | 93.0 | 3.4× | 78.44 |
| `Fam.Bal02` | 299.0 | 135.0 | 2.2× | 125.58 |
| `Fam.Bal01` | 290.0 | 128.0 | 2.3× | 118.23 |
| `Fam.Bal19Part2` | 288.0 | 84.0 | 3.4× | 72.25 |
| `Fam.BalC06` | 286.0 | 88.0 | 3.2× | 74.06 |
| `Fam.Bal17Part1` | 274.0 | 76.0 | 3.6× | 64.8 |
| `Fam.Bal28Part2Block1` | 273.0 | 72.0 | 3.8× | 64.31 |
| `Fam.Bal13Part2` | 272.0 | 94.0 | 2.9× | 79.83 |
| `Fam.Bal29Part2Block1` | 270.0 | 77.0 | 3.5× | 64.79 |
| `Fam.Bal08` | 264.0 | 135.0 | 2.0× | 124.64 |
| `Fam.Bal23Part1` | 259.0 | 70.0 | 3.7× | 60.08 |
| `Fam.Bal09` | 258.0 | 131.0 | 2.0× | 129.78 |
| `Fam.Bal10` | 257.0 | 127.0 | 2.0× | 116.61 |
| `Fam.Bal19Part1` | 257.0 | 82.0 | 3.1× | 71.17 |
| `Fam.Bal26Part2Block1` | 257.0 | 66.0 | 3.9× | 56.48 |
| `Fam.Bal04Part1` | 256.0 | 110.0 | 2.3× | 92.36 |
| `Fam.Bal20Part2` | 255.0 | 82.0 | 3.1× | 68.35 |
| `Fam.Bal04Part2` | 248.0 | 108.0 | 2.3× | 90.96 |
| `BalScalesChi` | 246.0 | 113.0 | 2.2× | – |
| `Fam.Bal14Part1` | 236.0 | 84.0 | 2.8× | 71.7 |
| `Fam.Bal12Part2` | 235.0 | 75.0 | 3.1× | 60.83 |
| `Fam.BalT00` | 225.0 | 90.0 | 2.5× | 74.34 |
| `Fam.BalC01` | 217.0 | 79.0 | 2.7× | 64.09 |
| `Fam.Bal29Part1Block1` | 215.0 | 57.0 | 3.8× | 50.11 |
| `Fam.Bal27Part2Block1` | 213.0 | 59.0 | 3.6× | 51.38 |
| `Fam.BalC02` | 212.0 | 77.0 | 2.8× | 62.0 |
| `Fam.BalC07Case045` | 212.0 | 44.0 | 4.8× | 39.27 |
| `Fam.Bal13Part1` | 205.0 | 71.0 | 2.9× | 60.48 |
| `Fam.Bal28Part1Block1` | 197.0 | 54.0 | 3.6× | 47.02 |
| `Fam.Bal24Block1` | 196.0 | 63.0 | 3.1× | 53.1 |
| `Fam.Bal25Part2Block1` | 193.0 | 53.0 | 3.6× | 45.86 |
| `Fam.BalCY0` | 191.0 | 84.0 | 2.3× | 72.03 |
| `Fam.Bal23Part2Block1` | 188.0 | 50.0 | 3.8× | 45.36 |
| `Fam.BalC03` | 188.0 | 67.0 | 2.8× | 54.55 |
| `Fam.Bal00` | 187.0 | 108.0 | 1.7× | 99.51 |
| `Fam.Bal25Part1Block1` | 187.0 | 56.0 | 3.3× | 48.34 |
| `Fam.Bal24Block2` | 185.0 | 56.0 | 3.3× | 49.26 |
| `Fam.Bal28Part2` | 184.0 | 48.0 | 3.8× | 37.09 |
| `Fam.Bal23Part3Block2` | 166.0 | 42.0 | 4.0× | 36.86 |
| `Fam.Bal27Part1Block1` | 166.0 | 49.0 | 3.4× | 42.5 |
| `Fam.Bal28Part1Block2` | 166.0 | 41.0 | 4.0× | 35.69 |
| `Fam.BalFamily225` | 166.0 | 42.0 | 4.0× | 36.73 |
| `Fam.Bal26Part1Block1` | 164.0 | 41.0 | 4.0× | 36.63 |
| `Fam.Bal24Block3` | 161.0 | 49.0 | 3.3× | 42.89 |
| `Fam.Bal22Part3` | 160.0 | 44.0 | 3.6× | 37.39 |
| `Fam.Bal26Part2` | 160.0 | 43.0 | 3.7× | 36.77 |
| `Fam.Bal26Part1Block2` | 158.0 | 41.0 | 3.9× | 35.63 |
| `Fam.Bal12Part3` | 151.0 | 52.0 | 2.9× | 43.84 |
| `Fam.Bal23Part2` | 151.0 | 42.0 | 3.6× | 36.15 |
| `Fam.Bal28Part1` | 141.0 | 35.0 | 4.0× | 26.6 |
| `Fam.Bal26Part3` | 139.0 | 45.0 | 3.1× | 40.25 |
| `Fam.Bal29Part2` | 138.0 | 36.0 | 3.8× | 26.81 |
| `Fam.Bal13Part3` | 136.0 | 46.0 | 3.0× | 39.85 |
| `Fam.Bal25Part2Block2` | 135.0 | 41.0 | 3.3× | 35.47 |
| `Fam.BalC08` | 133.0 | 49.0 | 2.7× | 40.4 |
| `Fam.BalC07Case042` | 125.0 | 38.0 | 3.3× | 33.77 |
| `Fam.Bal27Part1Block2` | 124.0 | 40.0 | 3.1× | 33.99 |
| `Fam.BalC00` | 124.0 | 50.0 | 2.5× | 41.51 |
| `Fam.BalC07Case043` | 117.0 | 39.0 | 3.0× | 34.75 |
| `Fam.BalC07Case047` | 112.0 | 40.0 | 2.8× | 33.8 |
| `Fam.Bal25Part1Block2` | 108.0 | 29.0 | 3.7× | 25.12 |
| `Fam.Bal27Part2Block2` | 108.0 | 28.0 | 3.9× | 26.21 |
| `Fam.BalFamily224` | 108.0 | 31.0 | 3.5× | 24.97 |
| `Fam.BalFamily227` | 107.0 | 31.0 | 3.5× | 26.35 |
| `Fam.BalFamily228` | 107.0 | 32.0 | 3.3× | 27.07 |
| `Fam.Bal22Part4` | 106.0 | 30.0 | 3.5× | 28.62 |
| `Fam.Bal23Part3Block1` | 105.0 | 31.0 | 3.4× | 28.99 |
| `Fam.Bal29Part1Block2` | 105.0 | 30.0 | 3.5× | 26.48 |
| `BalScales` | 104.0 | 38.0 | 2.7× | – |
| `Fam.Bal25Part2` | 103.0 | 30.0 | 3.4× | 26.74 |
| `Fam.BalC07Case044` | 103.0 | 33.0 | 3.1× | 29.47 |
| `Fam.Bal28Part3` | 102.0 | 33.0 | 3.1× | 29.53 |
| `Fam.Bal19Part3` | 100.0 | 30.0 | 3.3× | 26.78 |
| `Fam.Bal23Part3` | 100.0 | 32.0 | 3.1× | 28.89 |
| `Fam.Bal26Part1` | 99.0 | 30.0 | 3.3× | 25.12 |
| `Fam.Bal22Part2` | 98.0 | 32.0 | 3.1× | 26.44 |
| `Fam.BalC04Case028` | 97.0 | 33.0 | 2.9× | 28.77 |
| `Fam.BalFamily058` | 95.0 | 32.0 | 3.0× | 26.8 |
| `Fam.Bal17Part4` | 92.0 | 27.0 | 3.4× | 23.28 |
| `Fam.BalFamily059` | 87.0 | 30.0 | 2.9× | 24.25 |
| `BalComponentTors` | 81.0 | 28.0 | 2.9× | – |
| `BalComponentChiYM` | 79.0 | 19.0 | 4.2× | – |
| `Fam.Bal23Part4` | 78.0 | 29.0 | 2.7× | 25.04 |
| `BalComponentChiY` | 77.0 | 19.0 | 4.1× | – |
| `Fam.BalC04Case029` | 76.0 | 27.0 | 2.8× | 25.07 |
| `Fam.BalFamily051` | 76.0 | 25.0 | 3.0× | 21.35 |
| `BalComponentChi` | 73.0 | 19.0 | 3.8× | – |
| `Fam.BalFamily050` | 73.0 | 26.0 | 2.8× | 19.3 |
| `Fam.Bal29Part3` | 72.0 | 24.0 | 3.0× | 19.68 |
| `Fam.BalC04Case026` | 71.0 | 25.0 | 2.8× | 22.43 |
| `Fam.BalC04Case027` | 71.0 | 26.0 | 2.7× | 24.01 |
| `Fam.Bal27Part2` | 68.0 | 23.0 | 3.0× | 18.36 |
| `Fam.Bal29Part2Block2` | 68.0 | 23.0 | 3.0× | 19.86 |
| `Fam.Bal27Part1` | 67.0 | 24.0 | 2.8× | 20.01 |
| `Fam.Bal30` | 67.0 | 24.0 | 2.8× | 20.21 |
| `Fam.Bal29Part1` | 64.0 | 25.0 | 2.6× | 18.35 |
| `Fam.Bal25Part1` | 60.0 | 20.0 | 3.0× | 16.87 |
| `Fam.BalFamily056` | 56.0 | 22.0 | 2.5× | 18.46 |
| `Fam.BalFamily053` | 55.0 | 21.0 | 2.6× | 19.44 |
| `BalComponent` | 40.0 | 19.0 | 2.1× | – |
| `Fam.Bal24` | 40.0 | 15.0 | 2.7× | 14.42 |
| `Fam.BalFamily052` | 37.0 | 17.0 | 2.2× | 16.38 |
| `Fam.BalFamily055` | 33.0 | 14.0 | 2.4× | 12.96 |
| `Fam.BalFamily054` | 32.0 | 15.0 | 2.1× | 14.25 |
| `Fam.Bal26Part2Block2` | 26.0 | 11.0 | 2.4× | 11.02 |
| `Fam.BalCM0` | 25.0 | 13.0 | 1.9× | 13.02 |
| `Fam.BalC04Case025` | 24.0 | 20.0 | 1.2× | 19.04 |
| `BalLibraryChiYM` | 23.0 | 17.0 | 1.4× | – |
| `Fam.BalFamily057` | 20.0 | 11.0 | 1.8× | 10.06 |
| `BalLibraryChiY` | 19.0 | 16.0 | 1.2× | – |
| `BalLibraryChi` | 18.0 | 20.0 | 0.9× | – |
| **total (134 modules)** | **24731** | **8173** | **3.0×** | |

## Remaining levers (not done)

* The remaining `nlinarith` calls in `BalScales*`. `BalScalesTors` is still the slowest module at about
  211 s; these calls could be replaced by explicit product hints for `linarith`.
* The `decide +kernel` certificates in `keevashTypedSpec_*` could be split into smaller theorems.
* The 52 target modules not listed above were left unchanged: none of the patterns above matched them.
