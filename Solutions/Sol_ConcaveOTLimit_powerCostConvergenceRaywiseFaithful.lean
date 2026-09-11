import Theorems.Thm_ConcaveOTLimit_powerCostConvergence
import Theorems.Thm_ConcaveOTLimit_mainConvergenceRaywiseFaithful

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Paper-style power-cost convergence specialized to the intrinsic
generalized excursion coupling with its literal raywise description. -/
theorem powerCostConvergenceRaywiseFaithful_independent
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
  obtain
      ⟨gammaPower, tPower, optimizers, hGraphPower, hUniquePower,
        hPlanConvergence, hMapConvergence⟩ :=
    powerCostConvergence n mu nu hPower
  let hMarginals := marginalHypothesesOfPower n mu nu hPower
  obtain
      ⟨gammaRay, tRay, hGraphRay, hIntrinsicRay, hRaywise, _⟩ :=
    mainConvergenceRaywise n mu nu hMarginals
  obtain
      ⟨gammaLog, _tLog, _hGraphLog, hIntrinsicLog, hUniqueLog⟩ :=
    logarithmicSecondaryUniqueness n mu nu hPower

  have hPowerEqLog : gammaPower = gammaLog :=
    hUniqueLog.2 gammaPower hUniquePower.1
  have hLogEqRay : gammaLog = gammaRay :=
    (hIntrinsicRay strictExponentialProfile
      strictExponentialProfile_admissible).2 gammaLog
        ((hIntrinsicLog strictExponentialProfile
          strictExponentialProfile_admissible).1)
  have hPowerEqRay : gammaPower = gammaRay :=
    hPowerEqLog.trans hLogEqRay
  have hGraphRayPower : IsGraphPlan gammaPower tRay := by
    rw [hPowerEqRay]
    exact hGraphRay
  have hIntrinsicRayPower :
      IsIntrinsicGeneralizedECPlan mu nu gammaPower := by
    rw [hPowerEqRay]
    exact hIntrinsicRay
  have hRaywisePower :
      IsRaywiseGeneralizedECPlan mu nu gammaPower tRay := by
    rw [hPowerEqRay]
    exact hRaywise

  have hMapsEq :
      tPower =ᵐ[(mu : Measure (Euclidean n))] tRay :=
    isGraphPlan_map_unique_ae hGraphRayPower hGraphPower
  have hMapConvergenceRay :
      TendstoInMeasure
        (mu : Measure (Euclidean n))
        optimizers.transportMap
        (nhdsWithin 0 epsilonDomain) tRay :=
    hMapConvergence.congr_right hMapsEq

  exact
    ⟨gammaPower, tRay, optimizers, hGraphRayPower, hIntrinsicRayPower,
      hRaywisePower, hUniquePower, hPlanConvergence, hMapConvergenceRay⟩

/-- Independent proof of the paper-strengthened statement for every exact
power-cost optimizer family. -/
theorem powerCostConvergenceRaywiseFaithful_every_independent
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
          IsUniqueSecondaryMinimizer logarithmicProfile gammaSharp /\
          Nonempty (OptimizerFamily mu nu powerProfile) /\
            ∀ optimizers : OptimizerFamily mu nu powerProfile,
              Tendsto optimizers.plan
                  (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
                TendstoInMeasure
                  (mu : Measure (Euclidean n))
                  optimizers.transportMap
                  (nhdsWithin 0 epsilonDomain) tSharp := by
  obtain
      ⟨gammaSharp, tSharp, witness, hGraphSharp, hIntrinsicSharp,
        hRaywiseSharp, hLogSharp, hWitnessPlan, _hWitnessMap⟩ :=
    powerCostConvergenceRaywiseFaithful_independent n mu nu hPower
  refine
    ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp, hRaywiseSharp,
      hLogSharp, ⟨witness⟩, ?_⟩
  intro optimizers
  have hPlansEventually :
      witness.plan =ᶠ[nhdsWithin 0 epsilonDomain] optimizers.plan := by
    filter_upwards [eventually_mem_nhdsWithin] with epsilon hEpsilon
    exact
      (optimizers.uniquelyOptimal epsilon hEpsilon).2
        (witness.plan epsilon)
        (witness.uniquelyOptimal epsilon hEpsilon).1
  have hPlanConvergence :
      Tendsto optimizers.plan
        (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) :=
    Tendsto.congr' hPlansEventually hWitnessPlan
  exact
    ⟨hPlanConvergence,
      optimizerTransportMapConvergence_of_planConvergence
        n mu nu gammaSharp tSharp hGraphSharp powerProfile
        optimizers hPlanConvergence⟩

end ConcaveOTLimit
