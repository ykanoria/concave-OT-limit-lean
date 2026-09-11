# Lean Coverage

Canonical project: this repository

Lean version: `4.30.0`

The paper-facing main theorems are unconditional:

- `ConcaveOTLimit.PaperStatements.concaveCostMainTheorem`
- `ConcaveOTLimit.PaperStatements.powerCostMainTheorem`

Their only inputs are the assumptions appearing in the mathematical
statements. No OT conclusion is passed as a theorem argument or typeclass.

## Main Results

| Paper component | Lean declaration | Status |
|---|---|---|
| Concave perturbation convergence | `PaperStatements.concaveCostMainTheorem` | Exact, unconditional |
| Power-cost convergence | `PaperStatements.powerCostMainTheorem` | Exact, unconditional |
| Intrinsic canonical coupling and map | `mainConvergenceRaywise_uniqueCoupling`, `canonicalGeneralizedECMap_spec` | Exact, unconditional |
| Every admissible optimizer family converges | `mainConvergenceRaywise_every` | Exact, unconditional |
| Every power optimizer family converges | `powerCostConvergenceRaywiseFaithful_every` | Exact, unconditional |

The generic result proves existence and uniqueness of each perturbed
optimizer, its graph representation, and convergence in source measure to a
single coupling and map chosen before the perturbation family. The power
result additionally proves weak convergence of every exact power optimizer
family to the same intrinsic limit.

## OT Producers

The assertions that were external hypotheses in the legacy development now
have unconditional producers:

| Former external input | Unconditional producer |
|---|---|
| Distance Kantorovich witness and contact characterization | `distanceContactCharacterization`, `nonemptyDistanceDualWitness_of_marginalHypotheses` |
| Borel maximal-ray assignment | `borelMaximalRayMap` |
| Endpoint nullity and compact Lipschitz ray regularity | `contactLeftEndpointNegligible`, `contactDirectionCompactExhaustionPremise`, `contactSetRayRegularity` |
| Kernel disintegration and ray-coordinate atomlessness | `existsMaximalRayKernelDisintegration`, `countablyLipschitzRayCoordinateAtomlessPremise` |
| One-dimensional Juillet existence and uniqueness | `literalJuilletConstructionPremise_unconditional`, `literalJuilletIdentificationPremise_unconditional`, `oneDimensionalExcursionVariational` |
| Measurable fiber selection | `compactSectionMeasurableSelectionPremise_of_polish`, `canonicalRayForwardRationalGapMeasurableSelectionPremise` |
| Canonical raywise replacement and strict comparison | `canonicalRaywiseReplacement` |
| Common secondary minimizer | `uniqueSecondaryMinimizer` |
| Logarithmic secondary minimizer | `logarithmicSecondaryUniqueness` |
| Concave perturbation optimizer graphness | `perturbationMinimizerGraphPremise` |
| Power optimizer existence and graphness | `powerProfile_all_minimizers_graph`, `nonempty_powerOptimizerFamily` |
| Generic and power Gamma selection | `concaveGammaSelection`, `powerGammaSelection` |

Names ending in `Premise` are intermediate propositions retained for modular
proof organization. Every such proposition on the main proof path is
constructed by an unconditional theorem before it is consumed. None occurs
in a paper-facing main theorem signature.

## Audit

`Solutions.CompleteFormalizationAudit` is part of the default `lake build`.
It applies `assert_no_sorry` and a dependency-closure axiom check to the main
results and their principal OT producers.

The accepted axioms are only:

- `propext`
- `Classical.choice`
- `Quot.sound`

There are no executable `sorry`, `admit`, custom `axiom`, or `postulate`
declarations in the proof development. `Challenge.lean` contains exactly two
deliberate statement holes, one for each declaration checked by Comparator.

## Scope

This audit closes the two mutually singular main convergence theorems,
including their intrinsic and literal raywise identification. The
manuscript's separate general-measure corollary, which adds a common diagonal
part before applying the mutually singular theorem, is not one of these two
main exports.

`Challenge.lean` is the independent Mathlib-only statement surface;
`Solution.lean` connects it to the audited proof development.
