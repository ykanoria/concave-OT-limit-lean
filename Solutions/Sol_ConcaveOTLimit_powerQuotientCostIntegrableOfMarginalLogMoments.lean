import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientOrliczBound
import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments

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
    Integrable
      (fun z : E × E =>
        (powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) / epsilon)
      (gamma.plan : Measure (E × E)) := by
  have hDominating :=
    recoveryBoundIntegrableOfMarginalLogMoments hMu hNu gamma
  refine hDominating.mono' ?_ (ae_of_all _ fun z => ?_)
  · have hContinuous :
        Continuous
          (fun r : Real =>
            (powerProfile epsilon r - r) / epsilon) := by
      unfold powerProfile
      exact
        ((Real.continuous_rpow_const
          (by linarith)).sub continuous_id).div_const _
    exact
      (hContinuous.measurable.comp
        ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact powerDifferenceQuotientOrliczBound
      hEpsilonPos hEpsilonLeHalf (norm_nonneg _)
