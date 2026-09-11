import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory

namespace ConcaveOTLimit

/-- Every minimizer of every admissible perturbation profile is a graph
plan. This is the pointwise producer used to construct optimizer families. -/
def PerturbationMinimizerGraphPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n)) : Prop :=
  ∀ (family : Real -> Real -> Real) (firstOrder : Real -> Real),
    PerturbationAssumptions family firstOrder ->
      ∀ epsilon, epsilon ∈ epsilonDomain ->
        ∀ gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma ->
            ∃ T : Euclidean n -> Euclidean n,
              IsGraphPlan gamma T

end ConcaveOTLimit
