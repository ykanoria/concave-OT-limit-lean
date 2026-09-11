# Mathematical Statements

This document states the two paper-facing results in prose and records how
their hypotheses and conclusions are represented in Lean. The authoritative
formal signatures are the declarations in `Challenge.lean`; the completed
proofs are exported from
`Theorems/Thm_ConcaveOTLimit_completePaperMainTheorems.lean`.

All Lean names below are in the namespace `ConcaveOTLimit` unless a fully
qualified name is shown.

## Common notation

- `Euclidean n` is Euclidean space `R^n`.
- `FiniteCoupling mu nu` is the type of finite measures on
  `R^n x R^n` whose first and second marginals are `mu` and `nu`.
- `profileCost profile gamma` is
  `integral profile (norm (x - y)) d gamma(x,y)`.
- `distanceOptimalFace mu nu` is the set of couplings minimizing the
  distance cost `integral norm (x - y) d gamma(x,y)`.
- `IsUniqueSecondaryMinimizer profile gamma` says that `gamma` uniquely
  minimizes `profileCost profile` over the distance-optimal face.
- `epsilonDomain` is the interval `(0,1)`, approached from the right at zero.
- Convergence of coupling-valued functions is convergence in the topology on
  finite measures used by Mathlib. Convergence of maps is convergence in
  `mu`-measure.

## Concave perturbation theorem

### Prose statement

Let `mu` and `nu` be finite measures on `R^n` with equal positive mass.
Assume that they are mutually singular, that `mu` is absolutely continuous
with respect to Lebesgue measure, and that both measures have finite first
moment.

Then there are a coupling `gammaSharp` of `mu` and `nu` and a map `tSharp`
such that:

1. `gammaSharp` is the graph coupling induced by `tSharp`.
2. `gammaSharp` is intrinsic: for every strictly concave profile on
   `[0,infinity)` with an affine lower bound, it is the unique secondary
   minimizer over all distance-optimal couplings.
3. `gammaSharp` has the literal raywise generalized excursion-coupling
   description. More precisely, an off-diagonal distance-contact set
   associated with a 1-Lipschitz potential decomposes into maximal transport
   rays, and almost every coordinate component is Juillet's completed-graph
   occupation measure obtained by pairing each increasing crossing at a
   positive level with the first subsequent decreasing crossing.
4. For every admissible perturbation family `family epsilon d` with
   first-order profile `firstOrder`, exact graph optimizers exist for every
   `epsilon` in `(0,1)`.
5. Every such family of exact optimizers converges to `gammaSharp` as
   `epsilon` tends to zero from the right, and its transport maps converge in
   `mu`-measure to `tSharp`.

The quantifier order is important: `gammaSharp` and `tSharp` are chosen
before the perturbation family. Thus the same intrinsic limit works for every
admissible family.

### Hypotheses in Lean

The measure assumptions are bundled as
`MarginalHypotheses n mu nu`:

| Mathematical hypothesis | Lean field |
|---|---|
| Equal mass | `MarginalHypotheses.equalMass` |
| Positive mass | `MarginalHypotheses.positiveMass` |
| Mutual singularity | `MarginalHypotheses.mutuallySingular` |
| `mu` is absolutely continuous with respect to Lebesgue measure | `MarginalHypotheses.sourceAbsolutelyContinuous` |
| Finite first moment of `mu` | `MarginalHypotheses.sourceFirstMoment` |
| Finite first moment of `nu` | `MarginalHypotheses.targetFirstMoment` |

The theorem universally quantifies over `family` and `firstOrder`. Their
analytic conditions are bundled as
`PerturbationAssumptions family firstOrder`:

| Condition | Lean field |
|---|---|
| `family epsilon d` is nonnegative for `epsilon in (0,1)` and `d >= 0` | `PerturbationAssumptions.nonnegative` |
| Each distance profile is nondecreasing | `PerturbationAssumptions.increasing` |
| Each distance profile is strictly concave | `PerturbationAssumptions.strictlyConcave` |
| For each distance, dependence on `epsilon` is convex | `PerturbationAssumptions.convexInEpsilon` |
| `family epsilon d` tends to `d` as `epsilon` tends to zero | `PerturbationAssumptions.tendsToIdentity` |
| `(family epsilon d - d) / epsilon` tends to `firstOrder d` | `PerturbationAssumptions.firstOrderLimit` |
| `firstOrder` is strictly concave | `PerturbationAssumptions.firstOrderStrictlyConcave` |
| `firstOrder d >= -C(1+d)` for some `C >= 0` | `PerturbationAssumptions.firstOrderLowerBound` |
| `family epsilon d <= 2(1+d)` | `PerturbationAssumptions.growth` |

### Conclusions in Lean

| Mathematical conclusion | Lean declaration or expression |
|---|---|
| `gammaSharp` is induced by `tSharp` | `IsGraphPlan gammaSharp tSharp` |
| Common intrinsic secondary minimizer | `IsIntrinsicGeneralizedECPlan mu nu gammaSharp` |
| Literal maximal-ray/Juillet description | `IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp` |
| Exact graph optimizer families | `OptimizerFamily mu nu family` |
| Existence of an optimizer family | `Nonempty (OptimizerFamily mu nu family)` |
| Weak convergence of every optimizer family | `Tendsto optimizers.plan (nhdsWithin 0 epsilonDomain) (nhds gammaSharp)` |
| Convergence of maps in source measure | `TendstoInMeasure mu optimizers.transportMap (nhdsWithin 0 epsilonDomain) tSharp` |

The complete result is:

`ConcaveOTLimit.PaperStatements.concaveCostMainTheorem`.

## Power-cost theorem

### Prose statement

Let `mu` and `nu` be finite measures on `R^n` with equal positive mass.
Assume that they are mutually singular, that `mu` is absolutely continuous
with respect to Lebesgue measure, and that both measures have finite
`Psi`-moment, where

`Psi(r) = r log(1+r)`.

For the costs

`c_epsilon(x,y) = norm (x-y)^(1-epsilon)`, with `epsilon in (0,1)`,

there are a coupling `gammaSharp` and a map `tSharp` such that:

1. `gammaSharp` is the graph coupling induced by `tSharp`.
2. It is the intrinsic, literal raywise generalized excursion coupling
   described in the first theorem.
3. It is the unique secondary minimizer of the logarithmic profile
   `-r log r`, with the value at zero defined by continuous extension.
4. Exact graph optimizers for the power costs exist.
5. Every exact power-cost optimizer family converges weakly to `gammaSharp`
   as `epsilon` tends to zero from the right, and every associated transport
   map converges in `mu`-measure to `tSharp`.

### Hypotheses in Lean

The assumptions are bundled as `PowerMarginalHypotheses n mu nu`:

| Mathematical hypothesis | Lean field |
|---|---|
| Equal mass | `PowerMarginalHypotheses.equalMass` |
| Positive mass | `PowerMarginalHypotheses.positiveMass` |
| Mutual singularity | `PowerMarginalHypotheses.mutuallySingular` |
| `mu` is absolutely continuous with respect to Lebesgue measure | `PowerMarginalHypotheses.sourceAbsolutelyContinuous` |
| Finite `Psi`-moment of `mu` | `PowerMarginalHypotheses.sourceLogMoment` |
| Finite `Psi`-moment of `nu` | `PowerMarginalHypotheses.targetLogMoment` |

The specialized profiles are:

| Mathematical object | Lean declaration |
|---|---|
| `Psi(r) = r log(1+r)` | `Psi` |
| `-r log r` | `logarithmicProfile` |
| `r^(1-epsilon)` | `powerProfile` |

### Conclusions in Lean

| Mathematical conclusion | Lean declaration or expression |
|---|---|
| Graph limit | `IsGraphPlan gammaSharp tSharp` |
| Common intrinsic secondary minimizer | `IsIntrinsicGeneralizedECPlan mu nu gammaSharp` |
| Literal maximal-ray/Juillet description | `IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp` |
| Unique logarithmic secondary minimizer | `IsUniqueSecondaryMinimizer logarithmicProfile gammaSharp` |
| Existence of exact power optimizer families | `Nonempty (OptimizerFamily mu nu powerProfile)` |
| Weak convergence of every power optimizer family | `Tendsto optimizers.plan (nhdsWithin 0 epsilonDomain) (nhds gammaSharp)` |
| Convergence of maps in source measure | `TendstoInMeasure mu optimizers.transportMap (nhdsWithin 0 epsilonDomain) tSharp` |

The complete result is:

`ConcaveOTLimit.PaperStatements.powerCostMainTheorem`.

## Formalization boundary

The two fully qualified theorem names above are the targets listed in
`comparator.json`. `Challenge.lean` independently defines their statement
vocabulary using only Mathlib and contains one conventional challenge hole
for each target. `Solution.lean` imports the completed development, where
both declarations have closed proofs.

No distance-duality witness, transport-ray regularity statement,
disintegration, measurable selection, Juillet identification, graphness, or
optimizer-existence result is a hypothesis of either paper-facing theorem.
Those OT-specific assertions are proved in the dependency chain and occur
only as conclusions or internal lemmas.
