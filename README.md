# Concave Optimal-Transport Limits in Lean

This repository formalizes the mutually singular main convergence theorems
from *The Generalized Excursion Coupling as the Limit of Concave Optimal
Transport*. The development is a standalone Lean project with Mathlib as its
only dependency.

## Main Results

The paper-facing exports are:

- `ConcaveOTLimit.PaperStatements.concaveCostMainTheorem`
- `ConcaveOTLimit.PaperStatements.powerCostMainTheorem`

The generic theorem constructs one intrinsic generalized excursion coupling
and map, proves existence and uniqueness of each admissible concave-cost
optimizer, and proves convergence of every exact optimizer family. The power
theorem proves weak convergence of every exact power-cost optimizer family and
convergence in source measure of its maps to the same intrinsic limit.

The proofs construct the OT-specific ingredients internally: distance
duality and contact geometry, maximal-ray regularity and measurability,
one-dimensional Juillet excursion couplings, measurable selection and gluing,
optimizer graphness, secondary uniqueness, and Gamma selection.

## Third-Party Provenance

The compact-section measurable-selection proof imports five unchanged
Apache-2.0 descriptive-set-theory modules from Marcel Morgenstern's
[`lean4-ergodic-theory`](https://github.com/marcmorningstar/lean4-ergodic-theory)
at immutable commit
[`9bd9db36d3d099a32554b34eaf85e2e053a2bf31`](https://github.com/marcmorningstar/lean4-ergodic-theory/commit/9bd9db36d3d099a32554b34eaf85e2e053a2bf31).
They formalize the Novikov separation and compact-section projection chain.
The original file headers are retained under `ErgodicTheory/MeasureTheory/`;
full attribution is in `NOTICE`. No upstream-author endorsement of this
project or submission is claimed.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

Lean is pinned in `lean-toolchain`; Mathlib is pinned to an immutable commit in
`lake-manifest.json`.

## Verification

`Solutions/CompleteFormalizationAudit.lean` is imported by the root module. It
rejects proof placeholders and dependencies on axioms other than Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The repository contains no executable `sorry`, `admit`, custom `axiom`, or
`postulate` in the proof development. The two deliberate `sorry`s in
`Challenge.lean` are the conventional statement holes checked against
`Solution.lean` by [Comparator](https://github.com/leanprover/comparator).

The attributed third-party files can be checked against their pinned upstream
revision without a network request:

```sh
./scripts/verify-vendored-sources.sh
```

## Palomar

The repository uses Palomar's conventional root layout:

- `Challenge.lean`: Mathlib-only, independently auditable statements;
- `Solution.lean`: connection to the completed proof development;
- `comparator.json`: the two declarations and permitted standard axioms;
- `formalization.yaml`: provenance, scope, automation, and fidelity metadata.

On Linux, the same pinned Comparator and NanoDa check used by CI can be run
with:

```sh
./scripts/verify-comparator.sh
```

Before submission, push a final commit to a public GitHub repository and submit
its full 40-character SHA at <https://submit.palomar-registry.org/>.

## Scope

The two mutually singular convergence theorems, including intrinsic and
literal raywise identification, are complete. The manuscript's separate
general-measure corollary obtained by adding a common diagonal part is not a
paper-facing export of this repository.

## Layout

- `Definitions/`: mathematical model and statement predicates.
- `ErgodicTheory/MeasureTheory/`: attributed third-party compact-section
  projection modules.
- `Theorems/`: complete proof dependency chain.
- `Solutions/`: independent proofs and the closure audit.
- `STATEMENTS.md`: prose statements and their correspondence with Lean.
- `DEPENDENCY-MAP.md`: proof DAG for the main results.
- `LEAN-COVERAGE.md`: formalization coverage and scope.
- `RELEASE-CHECKLIST.md`: final GitHub and Palomar publication steps.

## Licence

Project-specific portions are Copyright 2026 Yash Kanoria.

The repository is released under Apache-2.0. Third-party portions retain
their original notices; see `NOTICE`.
