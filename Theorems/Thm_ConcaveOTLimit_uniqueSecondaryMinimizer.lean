import Theorems.Thm_ConcaveOTLimit_canonicalRationalGapMeasurableSelector
import Theorems.Thm_ConcaveOTLimit_distanceOptimalSupportCyclic
import Theorems.Thm_ConcaveOTLimit_measurableKernelAtomEnumeration
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Theorems.Thm_ConcaveOTLimit_uniqueSecondaryMinimizerAssembly

open MeasureTheory Set

noncomputable section

namespace ConcaveOTLimit

/-- Distance optimality and cyclic monotonicity of its topological support
supply the dual witness required by the final assembly. -/
theorem nonemptyDistanceDualWitness_of_marginalHypotheses
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    Nonempty (DistanceDualWitness mu nu) := by
  obtain ⟨gamma, hOptimal⟩ :=
    existsDistanceOptimal n mu nu hMarginals.equalMass
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
  apply
    (nonemptyDistanceDualWitness_iff_existsSupportedDistanceCyclicallyMonotone.{0}
      n mu nu hMarginals.sourceFirstMoment
      hMarginals.targetFirstMoment).2
  exact
    ⟨Measure.support
        (gamma.plan : Measure (Euclidean n × Euclidean n)),
      gamma,
      distanceOptimalSupportCyclicallyMonotone
        n hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        gamma hOptimal,
      Measure.support_mem_ae⟩

/-- The sole residual input after the dual witness, contact-set regularity,
and conditional coordinate atomlessness have been constructed. -/
def UniqueSecondaryMinimizerFiberSelectionPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) : Prop :=
  ∃ w : DistanceDualWitness mu nu,
    ∀ gamma : FiniteCoupling mu nu,
      IsSupported gamma
          (uniqueSecondaryContactSet n mu nu hMarginals w) ->
        ∀ D : MaximalRayKernelDisintegration n mu nu
            (uniqueSecondaryContactSet n mu nu hMarginals w),
          MaximalRayKernelDisintegration.CanonicalRayForwardRationalGapMeasurableSelectionPremise
            D gamma

/-- Conditional closure of the exact paper theorem from the remaining
canonical rational-gap measurable-selection input. -/
theorem uniqueSecondaryMinimizer_of_fiberSelectionPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (hFiberSelection :
      UniqueSecondaryMinimizerFiberSelectionPremise
        n mu nu hMarginals) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          exists u : Euclidean n -> Real,
            LipschitzWith 1 u /\
              exists Gamma : Set (Euclidean n × Euclidean n),
                Gamma =
                  distanceContactSet u \
                    {z : Euclidean n × Euclidean n | z.1 = z.2} /\
                IsSigmaCompact Gamma /\
                Nonempty
                  (RaywiseExcursionDisintegration
                    Gamma mu nu gammaSharp.plan tSharp) := by
  obtain ⟨w, hFiberSelection⟩ := hFiberSelection
  have hLeftEndpoint :
      (volume : Measure (Euclidean n))
        (leftTransportSet
            (uniqueSecondaryContactSet n mu nu hMarginals w) \
          transportSet
            (uniqueSecondaryContactSet n mu nu hMarginals w)) = 0 :=
    contactLeftEndpointNegligible
      (uniqueSecondaryDistancePotential n mu nu hMarginals w)
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals w).1
      (uniqueSecondaryContactSet n mu nu hMarginals w)
      (uniqueSecondaryContactSet_isSigmaCompact
        n mu nu hMarginals w)
      (uniqueSecondaryContactSet_subset
        n mu nu hMarginals w)
  have hCompactExhaustion :
      ContactDirectionCompactExhaustionPremise
        (volume : Measure (Euclidean n))
        (uniqueSecondaryDistancePotential n mu nu hMarginals w)
        (uniqueSecondaryDistancePotential_spec
          n mu nu hMarginals w).1
        (uniqueSecondaryContactSet n mu nu hMarginals w)
        (uniqueSecondaryContactSet_isSigmaCompact
          n mu nu hMarginals w)
        (uniqueSecondaryContactSet_diagonalFree
          n mu nu hMarginals w)
        (uniqueSecondaryContactSet_subset
          n mu nu hMarginals w) :=
    contactDirectionCompactExhaustionPremise
      (volume : Measure (Euclidean n))
      (uniqueSecondaryDistancePotential n mu nu hMarginals w)
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals w).1
      (uniqueSecondaryContactSet n mu nu hMarginals w)
      (uniqueSecondaryContactSet_isSigmaCompact
        n mu nu hMarginals w)
      (uniqueSecondaryContactSet_diagonalFree
        n mu nu hMarginals w)
      (uniqueSecondaryContactSet_subset
        n mu nu hMarginals w)
  apply
    uniqueSecondaryMinimizer_of_assemblyPremise
      n mu nu hMarginals
  refine
    { distanceDualWitness := w
      leftEndpointNegligible := hLeftEndpoint
      compactExhaustion := hCompactExhaustion
      canonicalRaywisePremise := ?_ }
  refine
    { coarea := ?_
      fiberSelection := ?_ }
  · intro D
    exact
      countablyLipschitzRayCoordinateAtomlessPremise
        mu
        (uniqueSecondaryContactSet n mu nu hMarginals w)
        (uniqueSecondaryRayRegularity
          n mu nu hMarginals w hLeftEndpoint hCompactExhaustion)
        D.rayAssignment D.defaultRay
  · intro gamma hSupported D
    exact hFiberSelection gamma hSupported D

/-- Paper Theorem 4: every admissible strictly concave secondary profile has
the same unique distance-optimal minimizer, induced by the intrinsic
generalized excursion-coupling map. -/
theorem uniqueSecondaryMinimizer
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          exists u : Euclidean n -> Real,
            LipschitzWith 1 u /\
              exists Gamma : Set (Euclidean n × Euclidean n),
                Gamma =
                  distanceContactSet u \
                    {z : Euclidean n × Euclidean n | z.1 = z.2} /\
                IsSigmaCompact Gamma /\
                Nonempty
                  (RaywiseExcursionDisintegration
                    Gamma mu nu gammaSharp.plan tSharp) := by
  apply
    uniqueSecondaryMinimizer_of_fiberSelectionPremise
      n mu nu hMarginals
  obtain ⟨w⟩ :=
    nonemptyDistanceDualWitness_of_marginalHypotheses
      n mu nu hMarginals
  refine ⟨w, ?_⟩
  intro gamma _ D
  exact
    MaximalRayKernelDisintegration.canonicalRayForwardRationalGapMeasurableSelectionPremise
      D gamma

end ConcaveOTLimit
