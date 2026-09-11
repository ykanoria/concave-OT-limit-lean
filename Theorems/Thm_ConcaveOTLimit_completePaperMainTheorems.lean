import Theorems.Thm_ConcaveOTLimit_mainConvergenceRaywiseFaithful
import Theorems.Thm_ConcaveOTLimit_powerCostConvergenceRaywiseFaithfulEvery

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Every exact optimizer family for an admissible concave perturbation
converges to the same intrinsic, raywise generalized excursion coupling and
map. No optimizer, graphness, raywise, or measurable-selection assertion is
assumed. -/
theorem mainConvergenceRaywise_every
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                Nonempty (OptimizerFamily mu nu family) /\
                  ∀ optimizers : OptimizerFamily mu nu family,
                    Tendsto optimizers.plan
                        (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
                      TendstoInMeasure
                        (mu : Measure (Euclidean n))
                        optimizers.transportMap
                        (nhdsWithin 0 epsilonDomain) tSharp := by
  obtain
      ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp,
        hRaywiseSharp, hOptimizerExists⟩ :=
    mainConvergenceRaywise n mu nu hMarginals
  refine
    ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp,
      hRaywiseSharp, ?_⟩
  intro family firstOrder hFamily
  obtain ⟨witness, _hWitnessConvergence⟩ :=
    hOptimizerExists family firstOrder hFamily
  refine ⟨⟨witness⟩, ?_⟩
  intro optimizers
  have hFirstOrderAdmissible :
      AdmissibleStrictlyConcaveProfile firstOrder :=
    ⟨hFamily.firstOrderStrictlyConcave,
      hFamily.firstOrderLowerBound⟩
  have hUniqueSharp :
      IsUniqueSecondaryMinimizer firstOrder gammaSharp :=
    hIntrinsicSharp firstOrder hFirstOrderAdmissible
  have hPlanConvergence :
      Tendsto optimizers.plan
        (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) :=
    optimizerPlanConvergence_of_uniqueSecondary
      n mu nu hMarginals gammaSharp family firstOrder hFamily
        optimizers hUniqueSharp
  exact
    ⟨hPlanConvergence,
      optimizerTransportMapConvergence_of_planConvergence
        n mu nu gammaSharp tSharp hGraphSharp family optimizers
        hPlanConvergence⟩

namespace PaperStatements

/-- Paper main theorem for admissible concave perturbation families. -/
alias concaveCostMainTheorem := mainConvergenceRaywise_every

/-- Paper main theorem for the power-cost family. -/
alias powerCostMainTheorem :=
  powerCostConvergenceRaywiseFaithful_every

end PaperStatements
end ConcaveOTLimit
