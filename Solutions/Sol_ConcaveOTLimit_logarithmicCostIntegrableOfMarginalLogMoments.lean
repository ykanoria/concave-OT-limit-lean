import Theorems.Thm_ConcaveOTLimit_absLogarithmicProfileLeOneAddPsi
import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    Integrable
      (fun z : E × E => logarithmicProfile ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  have hDominating :=
    recoveryBoundIntegrableOfMarginalLogMoments hMu hNu gamma
  refine hDominating.mono' ?_ (ae_of_all _ fun z => ?_)
  · exact
      (Real.continuous_negMulLog.measurable.comp
        ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact
      (absLogarithmicProfileLeOneAddPsi (norm_nonneg _)).trans (by
        linarith)
