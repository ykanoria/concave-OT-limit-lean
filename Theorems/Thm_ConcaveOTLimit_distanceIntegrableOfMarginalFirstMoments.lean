import Definitions.Def_ConcaveOTLimitModel

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

/-- Finite first moments of both marginals imply integrability of the
pointwise distance under every coupling with those marginals. -/
theorem distanceIntegrableOfMarginalFirstMoments
    {E : Type*} [MeasurableSpace E] [NormedAddGroup E] [BorelSpace E]
    [MeasurableSub₂ E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    Integrable (fun z : E × E => ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  have hFirst : Integrable (fun z : E × E => ‖z.1‖)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingFst gamma).integrable_comp_of_integrable hMu
  have hSecond : Integrable (fun z : E × E => ‖z.2‖)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingSnd gamma).integrable_comp_of_integrable hNu
  refine (hFirst.add hSecond).mono_nonneg
    (continuous_norm.measurable.comp measurable_sub).aestronglyMeasurable
    (ae_of_all _ fun z => norm_nonneg (z.1 - z.2))
    (ae_of_all _ fun z => norm_sub_le z.1 z.2)

end ConcaveOTLimit
