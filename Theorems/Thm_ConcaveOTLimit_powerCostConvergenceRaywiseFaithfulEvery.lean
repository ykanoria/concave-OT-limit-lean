import Theorems.Thm_ConcaveOTLimit_powerCostConvergenceRaywiseFaithful

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Every exact power-cost optimizer family converges to the same intrinsic
generalized excursion graph plan and its literal raywise excursion map. -/
theorem powerCostConvergenceRaywiseFaithful_every
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
    powerCostConvergenceRaywiseFaithful n mu nu hPower
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
