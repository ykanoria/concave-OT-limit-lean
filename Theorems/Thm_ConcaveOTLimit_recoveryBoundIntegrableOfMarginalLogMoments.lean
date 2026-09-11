import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_PsiNormSubBound

open MeasureTheory

namespace ConcaveOTLimit

private theorem measurePreservingFst
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (E × E)) (mu : Measure E) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.1

private theorem measurePreservingSnd
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (E × E)) (nu : Measure E) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.2

private theorem measurablePsi : Measurable Psi := by
  exact measurable_id.mul
    (Real.measurable_log.comp (measurable_const.add measurable_id))

/-- Marginal logarithmic moments make the power-recovery dominator
integrable under every finite coupling. -/
theorem recoveryBoundIntegrableOfMarginalLogMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    Integrable
      (fun z : E × E => 2 + Psi ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  have hFirst : Integrable (fun z : E × E => Psi ‖z.1‖)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingFst gamma).integrable_comp_of_integrable hMu
  have hSecond : Integrable (fun z : E × E => Psi ‖z.2‖)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingSnd gamma).integrable_comp_of_integrable hNu
  have hSum : Integrable
      (fun z : E × E => 1 + Psi ‖z.1‖ + Psi ‖z.2‖)
      (gamma.plan : Measure (E × E)) :=
    ((integrable_const 1).add hFirst).add hSecond
  have hDominating : Integrable
      (fun z : E × E => 4 * (1 + Psi ‖z.1‖ + Psi ‖z.2‖))
      (gamma.plan : Measure (E × E)) :=
    hSum.const_mul 4
  have hPsiDifference : Integrable
      (fun z : E × E => Psi ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
    refine hDominating.mono'
      (measurablePsi.comp
        ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
      (ae_of_all _ ?_)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact PsiNormSubBound z.1 z.2
    · exact mul_nonneg (norm_nonneg _)
        (Real.log_nonneg (by
          exact le_add_of_nonneg_right (norm_nonneg _)))
  exact (integrable_const 2).add hPsiDifference

end ConcaveOTLimit
