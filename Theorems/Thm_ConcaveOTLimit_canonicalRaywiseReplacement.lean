import Theorems.Thm_ConcaveOTLimit_canonicalRationalGapMeasurableSelector
import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementIntegration
import Theorems.Thm_ConcaveOTLimit_measurableKernelAtomEnumeration

open MeasureTheory Set
open scoped BigOperators

namespace ConcaveOTLimit

universe u

private theorem isDistanceCyclicallyMonotone_universeZero
    {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hCyclic : IsDistanceCyclicallyMonotone.{0, u} Gamma) :
    IsDistanceCyclicallyMonotone.{0, 0} Gamma := by
  intro I _ x y hxy sigma
  let e : ULift.{u} I ≃ I := Equiv.ulift
  let sigma' : Equiv.Perm (ULift.{u} I) :=
    e.trans sigma |>.trans e.symm
  have hCycle :=
    hCyclic
      (fun i => x (e i)) (fun i => y (e i))
      (fun i => hxy (e i)) sigma'
  calc
    (∑ i, dist (x i) (y i)) =
        ∑ i : ULift.{u} I, dist (x (e i)) (y (e i)) :=
      (Equiv.sum_comp e fun i => dist (x i) (y i)).symm
    _ <= ∑ i : ULift.{u} I,
        dist (x (e i)) (y (e (sigma' i))) :=
      hCycle
    _ = ∑ i : ULift.{u} I,
        dist (x (e i)) (y (sigma (e i))) := by
      apply Fintype.sum_congr
      intro i
      rfl
    _ = ∑ i, dist (x i) (y (sigma i)) :=
      Equiv.sum_comp e fun i => dist (x i) (y (sigma i))

/-- Paper Theorem 2: a regular sigma-compact support determines one canonical
raywise excursion-coupled graph plan, independent of the input coupling,
which improves every admissible concave distance profile and is
equality-rigid for strict profiles. -/
theorem canonicalRaywiseReplacement
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hInput :
      exists gamma : FiniteCoupling mu nu, IsSupported gamma Gamma) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
        (IsDistanceCyclicallyMonotone Gamma ->
          IsDistanceOptimal gammaSharp) /\
        IsSupported gammaSharp
          {z | SameMaximalRayClosure Gamma z.1 z.2} /\
        Nonempty
          (RaywiseExcursionDisintegration
            Gamma mu nu gammaSharp.plan tSharp) /\
        ∀ gamma : FiniteCoupling mu nu,
          IsSupported gamma Gamma ->
            ∀ profile : Real -> Real,
              AdmissibleConcaveProfile profile ->
                profileCost profile gammaSharp <=
                  profileCost profile gamma /\
                (AdmissibleStrictlyConcaveProfile profile ->
                  (profileCost profile gammaSharp =
                    profileCost profile gamma <-> gamma = gammaSharp)) := by
  have hIntegration :
      CanonicalRaywiseReplacementIntegrationPremise
        n mu nu Gamma hRegularity := by
    refine
      { coarea := ?_
        fiberSelection := ?_ }
    · intro D
      exact
        countablyLipschitzRayCoordinateAtomlessPremise
          mu Gamma hRegularity D.rayAssignment D.defaultRay
    · intro gamma _hSupported D
      exact
        MaximalRayKernelDisintegration.canonicalRayForwardRationalGapMeasurableSelectionPremise
          D gamma
  obtain
      ⟨gammaSharp, tSharp, hGraph, hCyclicOptimal, hSameRay,
        hDisintegration, hComparison⟩ :=
    canonicalRaywiseReplacement_of_integrationPremise
      n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
      hInput hIntegration
  refine
    ⟨gammaSharp, tSharp, hGraph, ?_, hSameRay,
      hDisintegration, hComparison⟩
  intro hCyclic
  exact
    hCyclicOptimal
      (isDistanceCyclicallyMonotone_universeZero hCyclic)

end ConcaveOTLimit
