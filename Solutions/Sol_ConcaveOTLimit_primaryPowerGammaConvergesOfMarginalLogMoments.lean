import Theorems.Thm_ConcaveOTLimit_distanceCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_distanceCostSequentiallyContinuousOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientIntegralLeMarginals
import Theorems.Thm_ConcaveOTLimit_powerQuotientCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_primaryPowerSequentialGammaConverges

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
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0)) :
    SequentialGammaConverges
      (fun n (gamma : FiniteCoupling mu nu) =>
        (profileCost (powerProfile (epsilon n)) gamma : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        (distanceCost gamma : EReal)) := by
  let bound : Real :=
    2 * (mu : Measure E).real Set.univ +
      (integral (mu : Measure E) (fun x => Psi (2 * ‖x‖)) : Real) +
      (integral (nu : Measure E) (fun y => Psi (2 * ‖y‖)) : Real)
  have hPsiNonnegative : ∀ x : E, 0 <= Psi (2 * ‖x‖) := by
    intro x
    unfold Psi
    exact mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg x))
      (Real.log_nonneg (by
        have hx : 0 <= 2 * ‖x‖ :=
          mul_nonneg (by norm_num) (norm_nonneg x)
        linarith))
  have hBoundNonnegative : 0 <= bound := by
    dsimp [bound]
    have hMuIntegral :
        0 <= integral (mu : Measure E) (fun x => Psi (2 * ‖x‖)) :=
      integral_nonneg hPsiNonnegative
    have hNuIntegral :
        0 <= integral (nu : Measure E) (fun y => Psi (2 * ‖y‖)) :=
      integral_nonneg hPsiNonnegative
    positivity
  exact primaryPowerSequentialGammaConverges
    epsilon hEpsilonPos hEpsilonTendsto bound hBoundNonnegative
    (distanceCostIntegrableOfMarginalLogMoments hMu hNu)
    (fun n gamma =>
      powerQuotientCostIntegrableOfMarginalLogMoments
        hMu hNu gamma (hEpsilonPos n) (hEpsilonLeHalf n))
    (fun n gamma => by
      simpa [bound] using
        powerDifferenceQuotientIntegralLeMarginals
          hMu hNu gamma (hEpsilonPos n) (hEpsilonLeHalf n))
    (fun hGamma =>
      distanceCostSequentiallyContinuousOfMarginalLogMoments
        hMu hNu hGamma)
