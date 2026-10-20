# Robust absorption for typed triangles — Paper II

**Juan Pablo Traverso Gianini · Lean 4 · Apache-2.0**

This repository contains the substantive Lean development accompanying
*Triangle decompositions II: Robust absorption for typed triangles*, preprint
1.0 (20 October 2026). It is a separate Palomar preparation, with its own build
directory and dependency checkouts. The manuscript's frozen source archive is
unchanged.

## Mathematical statements

A partition assigns a label to each vertex. A triangle type is the multiset of
its three labels, allowing repeated labels. The question is whether all edges
can be partitioned into triangles belonging to a prescribed family of types.
The formal divisibility condition retains both global edge-count vectors and
each vertex's degree vector into the label classes.

The six declarations selected in `comparator.json` are:

| Paper II result | Formal declaration (namespace prefixes below) | Scope |
|---|---|---|
| Theorem A | `PaddedGeneral.RealInverse.keevashTypedSpec_of_threeStepLinks` | Four-label families with the stated finite family facts and three-step links satisfy the typical-host property. |
| Theorem B | `PTA.BlowupB.teoremaB_of_keevash` | Deduction for nearly complete allowed hosts with positive type weights, conditional on that family's typical-host property. |
| Balanced consequence of B | `PTA.BlowupB.teoremaB_balanced` | The corresponding balanced-host result under the explicit finite weight condition. |
| Theorem C | `PTA.BlowupB.F0Direct.theorem146_ordered` | Two-label mixed triangles in semidense hosts, with the stated non-extremality and divisibility assumptions. |
| Computer-assisted Theorem D | `PTA.BlowupB.FiniteCensus.keevashTypedSpec_of_admissible` | Every admissible four-label family has the typical-host property; no catalogue-membership premise is assumed. |
| Lemma SC | `PTA.BlowupB.LemmaSC.absorber_onePart` | A bounded signed certificate, physical hinge supply and explicit budgets yield a terminal absorber. |

Here `PTA` abbreviates `PartitionedTriangleAbsorption` in this table only.

The typical-host property includes sufficiently large parts, no forbidden
edges, positive regular triangle weights, common-neighbour extension and
integral divisibility. It is not a decomposition theorem for arbitrary
divisible graphs. `KeevashTypedSpec` is the library's name for that explicit
property; it is not an assumed theorem or a formal import of Keevash's general
labelled-complex theorem. Theorem B deliberately retains this property as a
hypothesis. A and D prove it for the families in their statements.

Theorem C counts ordered adjacency disagreements. This is twice the unordered
edit count in the mathematical manuscript. Lemma SC counts physical hinges
with exponent `i - 4` after fixing four roots. All these conventions are
visible in the Challenge definitions.

## Proof architecture and provenance

The construction combines finite refiners, real and integral correction,
protected reserves and absorption. The finite census contains 765
representatives and explicitly checks the seventeen conserved families;
Theorem D transports the resulting property back to the original labels.
The census and physical-producer lemmas are supporting proof infrastructure,
not additional standalone claims selected by Comparator.

The source is the author's archive
`PAPER_II_LEAN_20261020_ALIGNED_v4.zip`, SHA-256
`677faa70a76444a000b8c2192a45d0ab0e39f8899825c004fdf6cbe52bb755cc`.
The original 1,510 modules are preserved subject to the recorded module-system
port. One 12,226-line generated certificate module, `Bal04`, is split at the
boundary between families BAL044 and BAL045 into two files; its original
module now re-exports both. No certificate proof body is changed by that split.
The constructor-explicit elaboration repair in `PaddedF12/TorsionFinite.lean`
is reused from the successfully checked Paper I port
[`aa032bb5dc35280aa1b30f327688c7592a9eb7c0`](https://github.com/jtraverso/nash-williams-lean/commit/aa032bb5dc35280aa1b30f327688c7592a9eb7c0).
It changes no theorem statement, hypothesis or mathematical argument.

This is a substantive source repository, not a wrapper importing a registered
entry. It does not import Paper I's Nash–Williams theorem. Shared mathematical
infrastructure is copied from the same freeze; Paper I build objects are not
used as evidence for this build.

## Review surface

- [`Challenge.lean`](Challenge.lean) imports only pinned Mathlib and reproduces
  the source definitions and six statements. Its deliberate `sorry` holes are
  confined to the six compared theorems.
- [`Solution.lean`](Solution.lean) exports the proved declarations under the
  same names from the three Paper II entry closures.
- [`tools/interface_manifest.json`](tools/interface_manifest.json) records the
  exact source locations and reproduced declaration bodies.
- [`tools/source_manifest.json`](tools/source_manifest.json),
  [`tools/port_manifest.json`](tools/port_manifest.json),
  [`tools/split_manifest.json`](tools/split_manifest.json) and
  [`tools/port_repairs.json`](tools/port_repairs.json) distinguish the source
  intake, module port, file split and compatibility repair.
- [`formalization.yaml`](formalization.yaml) records sources, attribution,
  limitations and AI assistance.

## Build and verification

Lean is pinned to `v4.35.0-rc3`, and Mathlib to
`c55e6e786f49471c72fbddbec5415808896aec1e`. Keep the committed lock file.

```text
lake exe cache get
lake build Challenge Solution
python -I tools/check_palomar.py
```

The independent Challenge build passed. The full Solution build and post-build
checks remain pending. Successful historical compilation
of the freeze is not a successful build of this port. The final report must
confirm the compared types, reproduced definitions, standard axioms and
absence of proof holes in the Solution closure. Palomar performs its own
Comparator and NanoDa verification after a fixed public commit is submitted.

## Sources and relationship to earlier work

- J. P. Traverso Gianini, *Triangle decompositions II: Robust absorption for
  typed triangles*, preprint 1.0 (2026). DOI reserved:
  `10.5281/zenodo.23502224`; the coordinated manuscript release is pending.
  This repository formalizes the six results identified above.
- P. Keevash, *The existence of designs II*, arXiv:1802.05900,
  [DOI](https://doi.org/10.48550/arXiv.1802.05900). Background for the
  labelled decomposition framework; equivalence of its hypotheses with the
  graph-level interface is not asserted.
- M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence
  Conjecture*, arXiv:2402.17855,
  [DOI](https://doi.org/10.48550/arXiv.2402.17855). Background for refined
  absorption and signed-certificate constructions.
- M. Delcourt and L. Postle, *A Proof of Nash-Williams' Conjecture*,
  arXiv:2606.11178, [DOI](https://doi.org/10.48550/arXiv.2606.11178).
  Motivation for the particular residual families. Its Theorem 13.16 and
  unpublished reference 17 are not assumed.
- B. Barber, D. Kühn, A. Lo, D. Osthus and A. Taylor, *Clique decompositions
  of multipartite graphs and completion of Latin squares*, JCTA 151 (2017),
  [DOI](https://doi.org/10.1016/j.jcta.2017.04.005). Relevant earlier partite
  decomposition and completion results.

Historical priority of the combined statements remains provisional. No claim
is made that the general absorption framework or the multipartite problem
originates here.

## Authorship, licences and computational assistance

Juan Pablo Traverso Gianini directed the work and remains responsible for the
arguments, citations, code and presentation. Aristotle (Harmonic) contributed
to exploring approaches, searching for counterexamples, developing proofs,
and formalizing and reviewing them; its role was not limited to translation.
Claude (Anthropic) and ChatGPT/Codex (OpenAI) were used to explore and check
arguments and prepare manuscripts and packaging. Python generated finite
candidate certificates; their universal uses are justified by Lean proofs,
not by the generator alone. No AI system is an author.

Original sources and packaging use [Apache-2.0](LICENSE); dependency licence
texts are retained in [`LICENSES/`](LICENSES). Neither internal AI review nor
kernel checking is described as independent human mathematical peer review.
