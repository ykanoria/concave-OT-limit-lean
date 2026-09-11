import Theorems.Thm_ConcaveOTLimit_distanceCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_powerProfileCostDecomposition
import Theorems.Thm_ConcaveOTLimit_powerQuotientCostIntegrableOfMarginalLogMoments

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) {epsilon : Real}
    (hEpsilonPos : 0 < epsilon)
    (hEpsilonLeHalf : epsilon <= 1 / 2) :
    rescaledProfileCost powerProfile epsilon gamma =
      (distanceCost gamma - minimalDistanceCost mu nu) / epsilon +
        integral (gamma.plan : Measure (E × E))
          (fun z =>
            (powerProfile epsilon ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon) := by
  have hDistance :=
    distanceCostIntegrableOfMarginalLogMoments hMu hNu gamma
  have hQuotient :=
    powerQuotientCostIntegrableOfMarginalLogMoments
      hMu hNu gamma hEpsilonPos hEpsilonLeHalf
  unfold rescaledProfileCost
  rw [powerProfileCostDecomposition gamma hEpsilonPos.ne' hDistance hQuotient]
  field_simp
  ring
