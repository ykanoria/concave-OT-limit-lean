import Theorems.Thm_ConcaveOTLimit_isMinimizerOnRescaledProfileCost
import Theorems.Thm_ConcaveOTLimit_powerGammaConvergencesOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_sequentialGammaLimitIsMinimizer

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- Every convergent sequence of exact power-cost optimizers has a
logarithmic secondary-minimizer limit. -/
theorem powerOptimizerLimitIsSecondaryMinimizer
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (optimizers : OptimizerFamily mu nu powerProfile)
    (epsilon : Nat -> Real)
    (hEpsilon : ∀ n, epsilon n ∈ epsilonDomain)
    (hEpsilonTendsto :
      Tendsto epsilon atTop (nhdsWithin 0 epsilonDomain))
    (gamma : FiniteCoupling mu nu)
    (hLimit :
      Tendsto (fun n => optimizers.plan (epsilon n))
        atTop (nhds gamma)) :
    IsSecondaryMinimizer logarithmicProfile gamma := by
  obtain ⟨hPrimaryGamma, hRescaledGamma⟩ :=
    powerGammaConvergencesOfMarginalLogMoments
      hMu hNu epsilon hEpsilon hEpsilonTendsto
  have hPrimaryMin :
      ∀ n,
        IsMinOn
          (fun eta : FiniteCoupling mu nu =>
            (profileCost (powerProfile (epsilon n)) eta : EReal))
          Set.univ (optimizers.plan (epsilon n)) := by
    intro n
    have hReal :=
      (optimizers.uniquelyOptimal (epsilon n) (hEpsilon n)).1
    intro eta _heta
    exact EReal.coe_le_coe_iff.mpr
      (hReal.2 eta (mem_univ eta))
  have hPrimaryLimit :=
    sequentialGammaLimitIsMinimizer
      hPrimaryGamma hLimit (mem_univ gamma) hPrimaryMin
  have hDistanceOptimal : IsDistanceOptimal gamma := by
    change
      IsMinimizerOn Set.univ
        (distanceCost : FiniteCoupling mu nu -> Real) gamma
    refine ⟨mem_univ gamma, ?_⟩
    intro eta _heta
    exact EReal.coe_le_coe_iff.mp
      (hPrimaryLimit (mem_univ eta))
  have hRescaledMin :
      ∀ n,
        IsMinOn
          (fun eta : FiniteCoupling mu nu =>
            (rescaledProfileCost powerProfile (epsilon n) eta : EReal))
          Set.univ (optimizers.plan (epsilon n)) := by
    intro n
    have hReal :=
      isMinimizerOn_rescaledProfileCost
        (hEpsilon n).1
        (optimizers.uniquelyOptimal
          (epsilon n) (hEpsilon n)).1
    intro eta _heta
    exact EReal.coe_le_coe_iff.mpr
      (hReal.2 eta (mem_univ eta))
  have hSecondaryLimit :=
    sequentialGammaLimitIsMinimizer
      hRescaledGamma hLimit hDistanceOptimal hRescaledMin
  change
    IsMinimizerOn (distanceOptimalFace mu nu)
      (profileCost logarithmicProfile) gamma
  refine ⟨hDistanceOptimal, ?_⟩
  intro eta heta
  exact EReal.coe_le_coe_iff.mp
    (hSecondaryLimit heta)

end ConcaveOTLimit
