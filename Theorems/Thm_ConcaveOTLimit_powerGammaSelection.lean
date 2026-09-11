import Theorems.Thm_ConcaveOTLimit_finiteCouplingFunctionalsEquicoercive
import Theorems.Thm_ConcaveOTLimit_globalPowerGammaConvergencesOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_powerOptimizerLimitIsSecondaryMinimizer

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- Paper Proposition 2: the primary and rescaled power-cost functionals
Gamma-converge to the distance and logarithmic lexicographic objectives,
respectively, and every sequential weak limit of exact optimizers is a
logarithmic secondary minimizer. -/
theorem powerGammaSelection
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : PowerMarginalHypotheses n mu nu)
    (optimizers : OptimizerFamily mu nu powerProfile)
    (eps : Nat -> Real)
    (hEps : ∀ k, eps k ∈ epsilonDomain)
    (hEpsZero :
      Tendsto eps atTop (nhdsWithin 0 epsilonDomain))
    (gammaZero : FiniteCoupling mu nu)
    (hLimit :
      Tendsto (fun k => optimizers.plan (eps k))
        atTop (nhds gammaZero)) :
    SequentialGammaConverges
        (fun k (gamma : FiniteCoupling mu nu) =>
          (profileCost (powerProfile (eps k)) gamma : EReal))
        (fun gamma : FiniteCoupling mu nu =>
          (distanceCost gamma : EReal)) /\
      SequentialGammaConverges
        (fun k (gamma : FiniteCoupling mu nu) =>
          (rescaledProfileCost powerProfile (eps k) gamma : EReal))
        (fun gamma : FiniteCoupling mu nu =>
          extendedSecondaryCost logarithmicProfile gamma) /\
      IsEquicoercive
        (fun k (gamma : FiniteCoupling mu nu) =>
          (profileCost (powerProfile (eps k)) gamma : EReal)) /\
      IsEquicoercive
        (fun k (gamma : FiniteCoupling mu nu) =>
          (rescaledProfileCost powerProfile (eps k) gamma : EReal)) /\
      IsSecondaryMinimizer logarithmicProfile gammaZero := by
  obtain ⟨hPrimaryGamma, hRescaledGamma⟩ :=
    globalPowerGammaConvergencesOfMarginalLogMoments
      hMarginals.sourceLogMoment hMarginals.targetLogMoment
      eps hEps hEpsZero
  have hPrimaryEquicoercive :=
    finiteCouplingFunctionalsEquicoercive
      (fun k (gamma : FiniteCoupling mu nu) =>
        (profileCost (powerProfile (eps k)) gamma : EReal))
  have hRescaledEquicoercive :=
    finiteCouplingFunctionalsEquicoercive
      (fun k (gamma : FiniteCoupling mu nu) =>
        (rescaledProfileCost powerProfile (eps k) gamma : EReal))
  have hSecondary :=
    powerOptimizerLimitIsSecondaryMinimizer
      hMarginals.sourceLogMoment hMarginals.targetLogMoment
      optimizers eps hEps hEpsZero gammaZero hLimit
  exact
    ⟨hPrimaryGamma, hRescaledGamma,
      hPrimaryEquicoercive, hRescaledEquicoercive, hSecondary⟩

end ConcaveOTLimit
