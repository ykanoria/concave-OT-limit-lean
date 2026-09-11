import Theorems.Thm_ConcaveOTLimit_mainConvergenceAssembly
import Theorems.Thm_ConcaveOTLimit_perturbationMinimizerGraphness
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Theorems.Thm_ConcaveOTLimit_uniqueSecondaryMinimizer

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Exact `mainConvergence` conclusion from the graphness producer. Secondary
uniqueness supplies the intrinsic graph plan, while the optimizer producer
supplies exact optimizer families. -/
theorem mainConvergence_of_perturbationMinimizerGraph
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (hGraph : PerturbationMinimizerGraphPremise n mu nu) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                exists optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp := by
  apply mainConvergence_of_producers n mu nu hMarginals
  · obtain
        ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp, _⟩ :=
      uniqueSecondaryMinimizer n mu nu hMarginals
    exact
      ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp⟩
  · exact
      optimizerFamilyProducer_of_perturbation_graph_minimizers
        n mu nu hMarginals hGraph

/-- The graphness premise is not merely sufficient: the optimizer families in
the exact result make it necessary. -/
theorem mainConvergence_result_iff_perturbationMinimizerGraph
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    (exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                exists optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp) ↔
      PerturbationMinimizerGraphPremise n mu nu := by
  constructor
  · rintro
      ⟨_gammaSharp, _tSharp, _hGraphSharp, _hIntrinsicSharp,
        hConvergence⟩
    intro family firstOrder hFamily epsilon hEpsilon gamma hGamma
    obtain ⟨optimizers, _hMapConvergence⟩ :=
      hConvergence family firstOrder hFamily
    have hGammaEq :
        gamma = optimizers.plan epsilon :=
      (optimizers.uniquelyOptimal epsilon hEpsilon).2 gamma hGamma
    subst gamma
    exact
      ⟨optimizers.transportMap epsilon,
        optimizers.graph epsilon hEpsilon⟩
  · intro hGraph
    exact
      mainConvergence_of_perturbationMinimizerGraph
        n mu nu hMarginals hGraph

/-- Exact convergence theorem: admissible concave perturbation optimizers
converge in source measure to the intrinsic generalized excursion map. -/
theorem mainConvergence
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                exists optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp :=
  mainConvergence_of_perturbationMinimizerGraph
    n mu nu hMarginals
      (perturbationMinimizerGraphPremise n mu nu hMarginals)

end ConcaveOTLimit
