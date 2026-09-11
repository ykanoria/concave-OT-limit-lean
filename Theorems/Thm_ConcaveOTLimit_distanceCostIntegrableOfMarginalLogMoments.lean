import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace ConcaveOTLimit

private theorem psiNonnegative {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem leOneAddPsi {r : Real} (hr : 0 <= r) :
    r <= 1 + Psi r := by
  by_cases hrOne : r <= 1
  · linarith [psiNonnegative hr]
  · have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one (le_of_not_ge hrOne)
    have hLog :=
      Real.one_sub_inv_le_log_of_pos (show 0 < 1 + r by linarith)
    have hMul :
        r * (1 - (1 + r)⁻¹) <= r * Real.log (1 + r) :=
      mul_le_mul_of_nonneg_left hLog hr
    have hFraction : r / (1 + r) <= 1 :=
      (div_le_one (by linarith)).2 (by linarith)
    rw [mul_sub, mul_one] at hMul
    rw [div_eq_mul_inv] at hFraction
    unfold Psi
    linarith

/-- Marginal logarithmic moments imply integrability of distance cost
under every finite coupling. -/
theorem distanceCostIntegrableOfMarginalLogMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    Integrable (fun z : E × E => ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  have hRecovery :=
    recoveryBoundIntegrableOfMarginalLogMoments hMu hNu gamma
  have hPsi : Integrable (fun z : E × E => Psi ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
    exact (hRecovery.sub (integrable_const 2)).congr
      (ae_of_all _ fun z => by simp)
  refine ((integrable_const 1).add hPsi).mono'
    ((measurable_fst.sub measurable_snd).norm).aestronglyMeasurable
    (ae_of_all _ ?_)
  intro z
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact leOneAddPsi (norm_nonneg _)

end ConcaveOTLimit
