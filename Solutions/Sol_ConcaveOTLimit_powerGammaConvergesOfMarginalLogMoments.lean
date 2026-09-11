import Theorems.Thm_ConcaveOTLimit_logarithmicCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientOrliczBound
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientSequentialGammaConverges
import Theorems.Thm_ConcaveOTLimit_powerQuotientCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments

open Filter MeasureTheory Topology

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonLeHalf : ∀ n, epsilon n <= 1 / 2)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0))
    (hLogarithmicLowerSemicontinuous :
      ∀ {gammaSeq : Nat -> FiniteCoupling mu nu}
        {gamma : FiniteCoupling mu nu},
        Tendsto gammaSeq atTop (nhds gamma) ->
          ∀ r : Real, r < profileCost logarithmicProfile gamma ->
            ∀ᶠ k in atTop,
              r <= profileCost logarithmicProfile (gammaSeq k)) :
    SequentialGammaConverges
      (fun n (gamma : FiniteCoupling mu nu) =>
        ((integral (gamma.plan : Measure (E × E))
          (fun z =>
            (powerProfile (epsilon n) ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon n) : Real) : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        (profileCost logarithmicProfile gamma : EReal)) := by
  exact powerDifferenceQuotientSequentialGammaConverges
    epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
    (fun hPos hHalf hNonnegative =>
      powerDifferenceQuotientOrliczBound hPos hHalf hNonnegative)
    (logarithmicCostIntegrableOfMarginalLogMoments hMu hNu)
    (fun n gamma =>
      powerQuotientCostIntegrableOfMarginalLogMoments
        hMu hNu gamma (hEpsilonPos n) (hEpsilonLeHalf n))
    (recoveryBoundIntegrableOfMarginalLogMoments hMu hNu)
    hLogarithmicLowerSemicontinuous
