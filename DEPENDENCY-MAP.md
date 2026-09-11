# Mathematical And Lean Dependency Map

This repository contains the live standalone formalization.

## Concave Branch

```text
paper marginal assumptions
  |
  +-> distance optimizer existence
  +-> Kantorovich dual witness and common contact set
  +-> endpoint nullity, no crossing, and compact Lipschitz ray regularity
  +-> Borel maximal-ray assignment and kernel disintegration
  +-> conditional-coordinate atomlessness
  +-> literal one-dimensional Juillet construction and uniqueness
  +-> compact-section measurable selection
  +-> canonical raywise replacement and strict profile comparison
  +-> profile-independent unique secondary minimizer
  |
  +-> existence, uniqueness, and graphness of every perturbed optimizer
  +-> primary and first-order Gamma selection
  |
  +-> weak plan convergence
  +-> graph-plan convergence implies convergence in source measure
  |
  `-> PaperStatements.concaveCostMainTheorem
```

## Power Branch

```text
paper logarithmic-moment assumptions
  |
  +-> finite first moments and the complete concave-branch ray package
  +-> power quotient bounds and uniform integrability
  +-> primary and rescaled power Gamma convergence
  +-> logarithmic raywise comparison and unique secondary minimizer
  +-> existence, uniqueness, and graphness of every power optimizer
  |
  `-> PaperStatements.powerCostMainTheorem
```

## Former Conditional Interfaces

Several modules retain propositions named `...Premise` because they are
useful boundaries for local proofs. The live DAG always has the form

```text
ordinary paper assumptions -> unconditional producer -> premise -> consumer
```

and never

```text
paper-facing theorem argument -> unproved OT premise.
```

Key closures are:

```text
contactLeftEndpointNegligible
  + contactDirectionCompactExhaustionPremise
  -> contactSetRayRegularity

literalJuilletConstructionPremise_unconditional
  + literalJuilletIdentificationPremise_unconditional
  -> literal raywise excursion identification

compactSectionMeasurableSelectionPremise_of_polish
  -> canonicalRayForwardRationalGapMeasurableSelectionPremise
  -> canonicalRaywiseReplacement

perturbationMinimizerGraphPremise
  -> optimizer family production
  -> mainConvergenceRaywise_every

powerProfile_all_minimizers_graph
  -> nonempty_powerOptimizerFamily
  -> powerCostConvergenceRaywiseFaithful_every
```

## Mechanical Closure

`Solutions.CompleteFormalizationAudit` checks the dependency closures of the
two paper exports and the principal producers. A default build fails if one
of them acquires a proof placeholder or a nonstandard axiom.
