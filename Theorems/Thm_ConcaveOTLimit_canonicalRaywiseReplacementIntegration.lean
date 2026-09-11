import Theorems.Thm_ConcaveOTLimit_raywiseExcursionIdentification
import Theorems.Thm_ConcaveOTLimit_sameMaximalRayClosureSupport
import Theorems.Thm_ConcaveOTLimit_raywiseDistancePreservation
import Theorems.Thm_ConcaveOTLimit_globalConditionalDeterminism
import Theorems.Thm_ConcaveOTLimit_globalRaywiseProfileComparison
import Theorems.Thm_ConcaveOTLimit_distanceCyclicMonotoneSufficiency

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Reduced canonical-replacement boundary -/

/-- The analytic inputs not yet derived from the marginal hypotheses.
Five fields of `CanonicalRaywiseReplacementResidualInputs` are derived after
selection; its cyclic field is replaced by a separate application-level
input-optimality implication. -/
structure CanonicalRaywiseReplacementIntegrationPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma) : Prop where
  coarea :
    ∀ D : MaximalRayKernelDisintegration n mu nu Gamma,
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay
  fiberSelection :
    ∀ (gamma : FiniteCoupling mu nu),
      IsSupported gamma Gamma ->
        ∀ D : MaximalRayKernelDisintegration n mu nu Gamma,
          MaximalRayKernelDisintegration.CanonicalRayForwardRationalGapMeasurableSelectionPremise
            D gamma

private theorem canonicalRaywiseReplacement_of_supportedInput
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hInputOptimal :
      IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
        IsDistanceOptimal gamma)
    (hIntegration :
      CanonicalRaywiseReplacementIntegrationPremise
        n mu nu Gamma hRegularity) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
        (IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
          IsDistanceOptimal gammaSharp) /\
        IsSupported gammaSharp
          {z | SameMaximalRayClosure Gamma z.1 z.2} /\
        Nonempty
          (RaywiseExcursionDisintegration
            Gamma mu nu gammaSharp.plan tSharp) /\
        ∀ eta : FiniteCoupling mu nu,
          IsSupported eta Gamma ->
            ∀ profile : Real -> Real,
              AdmissibleConcaveProfile profile ->
                profileCost profile gammaSharp <=
                  profileCost profile eta /\
                (AdmissibleStrictlyConcaveProfile profile ->
                  (profileCost profile gammaSharp =
                    profileCost profile eta <-> eta = gammaSharp)) := by
  let D : MaximalRayKernelDisintegration n mu nu Gamma :=
    Classical.choice
      (existsMaximalRayKernelDisintegration
        n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
        ⟨gamma, hSupported⟩)
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  obtain ⟨gammaLift, hGlobal, hFiber, hIdentification⟩ :=
    existsCanonicalRayLiftedMinimizer_with_raywiseExcursionIdentification_of_weakPremise
      D hRegularity gamma hSupported
      hMarginals.sourceAbsolutelyContinuous
      (hIntegration.coarea D)
      hMarginals.mutuallySingular
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
      (hIntegration.fiberSelection gamma hSupported D)
  have hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n) :=
    hGlobal.1
  have hExcursion :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          ((assembledRaywiseComponentFiber D gamma gammaLift R).map
            fun z =>
              (rayCoordinate R z.1, rayCoordinate R z.2)) := by
    filter_upwards [hIdentification] with R hR
    obtain ⟨_hCoupling, hInheritance, hRIdentification⟩ := hR
    simpa only
        [RaywiseCoordinateInheritance.coordinateCoupling,
          rayCoordinatePair] using
      hRIdentification.coordinateIsExcursion
  let gammaSharp : FiniteCoupling mu nu :=
    assembledRaywiseCoupling D gamma hSupported gammaLift
  obtain ⟨tSharp, _hT, hGraphRaw, _hConditional⟩ :=
    assembledRaywiseCoupling_graph_and_condDistrib_ae_deterministic_of_weakPremise
      D hRegularity gamma hSupported gammaLift hLiftedForward
      hMarginals.sourceAbsolutelyContinuous
      (hIntegration.coarea D)
      hMarginals.mutuallySingular
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
      hExcursion
  have hGraph : IsGraphPlan gammaSharp tSharp := by
    simpa only [gammaSharp] using hGraphRaw
  have hAtomless :=
    maximalRaySource_coordinateAtomless_of_weakPremise
      D hRegularity gamma hSupported
      hMarginals.sourceAbsolutelyContinuous
      (hIntegration.coarea D)
  have hSingular :=
    maximalRayCoordinateMarginals_mutuallySingular_ae
      D gamma hSupported hMarginals.mutuallySingular
  have hSameRay :
      IsSupported gammaSharp
        {z | SameMaximalRayClosure Gamma z.1 z.2} := by
    simpa only [gammaSharp] using
      assembledRaywiseCoupling_supported_sameMaximalRayClosure_of_mutuallySingular
        D gamma hSupported gammaLift hLiftedForward
        hMarginals.mutuallySingular
  have hDisintegration :
      Nonempty
        (RaywiseExcursionDisintegration
          Gamma mu nu gammaSharp.plan tSharp) := by
    exact
      existsRaywiseExcursionDisintegration_of_assembled
        D gamma hSupported gammaLift hLiftedForward
        tSharp hGraph hAtomless hSingular hExcursion
  have hDistanceOptimal :
      IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
        IsDistanceOptimal gammaSharp := by
    intro hCyclic
    simpa only [gammaSharp] using
      assembledRaywiseCoupling_isDistanceOptimal_of_input
        D gamma hSupported gammaLift hLiftedForward
        hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        (hInputOptimal hCyclic)
  obtain ⟨hProfileComparison, hStrictProfileRigidity⟩ :=
    canonicalRaywiseReplacement_profileFields_of_fiberMinimality_of_weakPremise
      D hRegularity hMarginals gamma hSupported gammaLift
      hLiftedForward (hIntegration.coarea D) hFiber
  refine
    ⟨gammaSharp, tSharp, hGraph, hDistanceOptimal, hSameRay,
      hDisintegration, ?_⟩
  intro eta hEta profile hProfile
  refine
    ⟨hProfileComparison eta hEta profile hProfile, ?_⟩
  intro hStrict
  constructor
  · intro hCost
    exact
      hStrictProfileRigidity eta hEta profile hStrict hCost
  · intro hEq
    rw [hEq]

/-- Exact canonical replacement from the reduced analytic boundary.
Distance-cyclic monotonicity makes the chosen supported input optimal, and
distance preservation transfers that optimality to the output. -/
theorem canonicalRaywiseReplacement_of_integrationPremise
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
      ∃ gamma : FiniteCoupling mu nu, IsSupported gamma Gamma)
    (hIntegration :
      CanonicalRaywiseReplacementIntegrationPremise
        n mu nu Gamma hRegularity) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
        (IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
          IsDistanceOptimal gammaSharp) /\
        IsSupported gammaSharp
          {z | SameMaximalRayClosure Gamma z.1 z.2} /\
        Nonempty
          (RaywiseExcursionDisintegration
            Gamma mu nu gammaSharp.plan tSharp) /\
        ∀ eta : FiniteCoupling mu nu,
          IsSupported eta Gamma ->
            ∀ profile : Real -> Real,
              AdmissibleConcaveProfile profile ->
                profileCost profile gammaSharp <=
                  profileCost profile eta /\
                (AdmissibleStrictlyConcaveProfile profile ->
                  (profileCost profile gammaSharp =
                    profileCost profile eta <-> eta = gammaSharp)) := by
  obtain ⟨gamma, hSupported⟩ := hInput
  exact
    canonicalRaywiseReplacement_of_supportedInput
      n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
      gamma hSupported
      (fun hCyclic =>
        distanceCyclicMonotoneSufficiency_of_marginalHypotheses
          n mu nu hMarginals Gamma gamma hCyclic hSupported)
      hIntegration

/-- Contact-set application form. Once the chosen supported input is known
to be distance-optimal, raywise distance preservation gives an unconditionally
optimal replacement, hence the cyclic implication in the exact target. -/
theorem canonicalRaywiseReplacement_of_integrationPremise_and_optimalInput
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hOptimal : IsDistanceOptimal gamma)
    (hIntegration :
      CanonicalRaywiseReplacementIntegrationPremise
        n mu nu Gamma hRegularity) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
        (IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
          IsDistanceOptimal gammaSharp) /\
        IsSupported gammaSharp
          {z | SameMaximalRayClosure Gamma z.1 z.2} /\
        Nonempty
          (RaywiseExcursionDisintegration
            Gamma mu nu gammaSharp.plan tSharp) /\
        ∀ eta : FiniteCoupling mu nu,
          IsSupported eta Gamma ->
            ∀ profile : Real -> Real,
              AdmissibleConcaveProfile profile ->
                profileCost profile gammaSharp <=
                  profileCost profile eta /\
                (AdmissibleStrictlyConcaveProfile profile ->
                  (profileCost profile gammaSharp =
                    profileCost profile eta <-> eta = gammaSharp)) :=
  canonicalRaywiseReplacement_of_supportedInput
    n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
    gamma hSupported (fun _hCyclic => hOptimal) hIntegration

end ConcaveOTLimit
