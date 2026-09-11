# Lean Dependencies

This document records the current closed proof boundary. All declarations
listed below are in namespace `ConcaveOTLimit` unless noted otherwise.

## Paper-Facing Exports

| Declaration | Ordinary hypotheses | OT conclusion |
|---|---|---|
| `PaperStatements.concaveCostMainTheorem` | Equal positive mass, mutual singularity, source absolute continuity, finite first moments, and `PerturbationAssumptions` | A common intrinsic literal-raywise graph plan; existence and uniqueness of exact optimizers; convergence of every optimizer family |
| `PaperStatements.powerCostMainTheorem` | Equal positive mass, mutual singularity, source absolute continuity, finite logarithmic moments | A common intrinsic literal-raywise graph plan; unique logarithmic secondary minimizer; weak and in-measure convergence of every power optimizer family |

Neither signature contains an A-P, Juillet, Pegon, Kantorovich, graphness,
selection, gluing, or canonical-replacement hypothesis.

## Producer Table

| Layer | Producer declarations | Used for |
|---|---|---|
| Couplings and compactness | `finiteCouplingIsCompact`, `existsDistanceOptimal` | Existence and subsequence extraction |
| Distance duality | `distanceContactCharacterization`, `nonemptyDistanceDualWitness_of_marginalHypotheses` | Common contact support for all distance optimizers |
| Contact geometry | `distanceContactSubsetNoCrossing`, `distanceContactCoveredRaySaturation` | Oriented transport-ray geometry |
| Ray regularity | `contactLeftEndpointNegligible`, `contactDirectionCompactExhaustionPremise`, `contactSetRayRegularity` | Countably Lipschitz maximal-ray decomposition |
| Ray measurability | `borelMaximalRayMap`, `existsMaximalRayKernelDisintegration` | Measurable ray labels and conditional kernels |
| Atomlessness | `finiteKernel_hasMeasurableAtomEnumeration`, `countablyLipschitzRayCoordinateAtomlessPremise` | Atomless conditional source coordinates |
| One-dimensional OT | `existsForwardCouplingOfStochasticOrder`, `oneDimensionalExcursionVariational`, `literalJuilletConstructionPremise_unconditional`, `literalJuilletIdentificationPremise_unconditional` | Literal Juillet component construction and uniqueness |
| Selection | `compactSectionMeasurableSelectionPremise_of_polish`, `canonicalRayForwardRationalGapMeasurableSelectionPremise` | Measurable fiberwise minimizers |
| Raywise comparison | `canonicalRaywiseReplacement`, `assembledRaywiseCoupling_profileComparison_and_strictRigidity` | Global canonical replacement and equality rigidity |
| Secondary uniqueness | `uniqueSecondaryMinimizer`, `logarithmicSecondaryUniqueness` | Unique common limits |
| Generic optimizer structure | `exists_perturbationProfileMinimizer`, `perturbationMinimizerGraphPremise` | Exact graph optimizer families |
| Power optimizer structure | `exists_powerProfileMinimizer`, `powerProfile_all_minimizers_graph`, `nonempty_powerOptimizerFamily` | Exact power optimizer family |
| Gamma convergence | `concaveGammaSelection`, `powerGammaSelection` | Identification of every cluster point |
| Final topology | `optimizerPlanConvergence_of_uniqueSecondary`, `optimizerTransportMapConvergence_of_planConvergence` | Full weak and in-measure convergence |

## Closed Main Chains

Generic:

```text
MarginalHypotheses
  -> uniqueSecondaryMinimizer
  -> perturbationMinimizerGraphPremise
  -> optimizerPlanConvergence_of_uniqueSecondary
  -> mainConvergenceRaywise
  -> mainConvergenceRaywise_every
  -> PaperStatements.concaveCostMainTheorem
```

Power:

```text
PowerMarginalHypotheses
  -> logarithmicSecondaryUniqueness
  -> powerProfile_all_minimizers_graph
  -> nonempty_powerOptimizerFamily
  -> powerGammaSelection
  -> powerCostConvergenceRaywiseFaithful_every
  -> PaperStatements.powerCostMainTheorem
```

## Logical Trust Boundary

The canonical project has no custom axiom declarations and no proof
placeholders. The audited theorem closures use only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

The default target imports `Solutions.CompleteFormalizationAudit`, which
checks these claims during compilation.
