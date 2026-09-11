import Theorems.Thm_ConcaveOTLimit_mainConvergenceRaywiseFaithful
import Theorems.Thm_ConcaveOTLimit_powerCostConvergence

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Paper-style power specialization: exact power-cost optimizers converge
to the intrinsic generalized excursion graph plan, whose disintegration is
raywise the literal completed-graph excursion coupling. -/
theorem powerCostConvergenceRaywiseFaithful
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        ∃ optimizers : OptimizerFamily mu nu powerProfile,
          IsGraphPlan gammaSharp tSharp /\
            IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
            IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp /\
            Tendsto optimizers.plan
              (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
            TendstoInMeasure
              (mu : Measure (Euclidean n))
              optimizers.transportMap
              (nhdsWithin 0 epsilonDomain) tSharp := by
  let hMarginals := marginalHypothesesOfPower n mu nu hPower
  obtain
      ⟨gammaPower, tPower, optimizers, hGraphPower, hLogPower,
        hPlanPower, hMapPower⟩ :=
    powerCostConvergence n mu nu hPower
  obtain
      ⟨gammaLog, _tLog, _hGraphLog, hIntrinsicLog, hLogLog⟩ :=
    logarithmicSecondaryUniqueness n mu nu hPower
  obtain
      ⟨gammaRay, tRay, hGraphRay, hIntrinsicRay, hRaywise,
        _hGeneralConvergence⟩ :=
    mainConvergenceRaywise n mu nu hMarginals
  have hPowerEqLog : gammaPower = gammaLog :=
    (hLogPower.2 gammaLog hLogLog.1).symm
  have hLogEqRay : gammaLog = gammaRay :=
    ((hIntrinsicLog strictExponentialProfile
      strictExponentialProfile_admissible).2 gammaRay
        ((hIntrinsicRay strictExponentialProfile
          strictExponentialProfile_admissible).1)).symm
  have hPowerEqRay : gammaPower = gammaRay :=
    hPowerEqLog.trans hLogEqRay
  have hGraphPowerRay : IsGraphPlan gammaRay tPower := by
    simpa only [hPowerEqRay] using hGraphPower
  have hPowerMapAe :
      tPower =ᵐ[(mu : Measure (Euclidean n))] tRay :=
    isGraphPlan_map_unique_ae hGraphRay hGraphPowerRay
  have hPlanRay :
      Tendsto optimizers.plan
        (nhdsWithin 0 epsilonDomain) (nhds gammaRay) := by
    simpa only [hPowerEqRay] using hPlanPower
  have hMapRay :
      TendstoInMeasure
        (mu : Measure (Euclidean n))
        optimizers.transportMap
        (nhdsWithin 0 epsilonDomain) tRay :=
    hMapPower.congr_right hPowerMapAe
  have hLogRay :
      IsUniqueSecondaryMinimizer logarithmicProfile gammaRay := by
    simpa only [hPowerEqRay] using hLogPower
  exact
    ⟨gammaRay, tRay, optimizers, hGraphRay, hIntrinsicRay,
      hRaywise, hLogRay, hPlanRay, hMapRay⟩

/-- Canonical form of the raywise-faithful power convergence theorem. -/
theorem powerCostConvergenceRaywiseFaithful_canonical
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    ∃ optimizers : OptimizerFamily mu nu powerProfile,
      IsGraphPlan
          (canonicalGeneralizedECCoupling n mu nu
            (marginalHypothesesOfPower n mu nu hPower))
          (canonicalGeneralizedECMap n mu nu
            (marginalHypothesesOfPower n mu nu hPower)) /\
        IsIntrinsicGeneralizedECPlan mu nu
          (canonicalGeneralizedECCoupling n mu nu
            (marginalHypothesesOfPower n mu nu hPower)) /\
        IsRaywiseGeneralizedECPlan mu nu
          (canonicalGeneralizedECCoupling n mu nu
            (marginalHypothesesOfPower n mu nu hPower))
          (canonicalGeneralizedECMap n mu nu
            (marginalHypothesesOfPower n mu nu hPower)) /\
        IsUniqueSecondaryMinimizer logarithmicProfile
          (canonicalGeneralizedECCoupling n mu nu
            (marginalHypothesesOfPower n mu nu hPower)) /\
        Tendsto optimizers.plan
          (nhdsWithin 0 epsilonDomain)
          (nhds
            (canonicalGeneralizedECCoupling n mu nu
              (marginalHypothesesOfPower n mu nu hPower))) /\
        TendstoInMeasure
          (mu : Measure (Euclidean n))
          optimizers.transportMap
          (nhdsWithin 0 epsilonDomain)
          (canonicalGeneralizedECMap n mu nu
            (marginalHypothesesOfPower n mu nu hPower)) := by
  let hMarginals := marginalHypothesesOfPower n mu nu hPower
  obtain
      ⟨gammaSharp, tSharp, optimizers, hGraphSharp,
        hIntrinsicSharp, _hRaywiseSharp, hLogSharp,
        hPlanSharp, hMapSharp⟩ :=
    powerCostConvergenceRaywiseFaithful n mu nu hPower
  have hGammaEq :
      gammaSharp =
        canonicalGeneralizedECCoupling n mu nu hMarginals :=
    (isIntrinsicGeneralizedECPlan_iff_eq_canonicalGeneralizedECCoupling
      n mu nu hMarginals gammaSharp).1 hIntrinsicSharp
  have hCanonical :=
    canonicalGeneralizedECMap_spec n mu nu hMarginals
  have hGraphSharpCanonical :
      IsGraphPlan
        (canonicalGeneralizedECCoupling n mu nu hMarginals) tSharp := by
    simpa only [hGammaEq] using hGraphSharp
  have hSharpMapAe :
      tSharp =ᵐ[(mu : Measure (Euclidean n))]
        canonicalGeneralizedECMap n mu nu hMarginals :=
    isGraphPlan_map_unique_ae hCanonical.1 hGraphSharpCanonical
  have hPlanCanonical :
      Tendsto optimizers.plan
        (nhdsWithin 0 epsilonDomain)
        (nhds
          (canonicalGeneralizedECCoupling n mu nu hMarginals)) := by
    simpa only [hGammaEq] using hPlanSharp
  have hMapCanonical :
      TendstoInMeasure
        (mu : Measure (Euclidean n))
        optimizers.transportMap
        (nhdsWithin 0 epsilonDomain)
        (canonicalGeneralizedECMap n mu nu hMarginals) :=
    hMapSharp.congr_right hSharpMapAe
  have hLogCanonical :
      IsUniqueSecondaryMinimizer logarithmicProfile
        (canonicalGeneralizedECCoupling n mu nu hMarginals) := by
    simpa only [hGammaEq] using hLogSharp
  refine
    ⟨optimizers, hCanonical.1,
      (canonicalGeneralizedECCoupling_spec n mu nu hMarginals).1,
      hCanonical.2.2.1, hLogCanonical,
      hPlanCanonical, hMapCanonical⟩

end ConcaveOTLimit
