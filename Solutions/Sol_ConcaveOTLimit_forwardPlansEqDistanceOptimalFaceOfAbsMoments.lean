import Theorems.Thm_ConcaveOTLimit_forwardPlansEqDistanceOptimalFace

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (hMu : Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => |y|) (nu : Measure Real))
    (gammaForward : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gammaForward) :
    {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} =
      distanceOptimalFace mu nu := by
  have hMuId :
      Integrable (fun x : Real => x) (mu : Measure Real) := by
    apply (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hMu
  have hNuId :
      Integrable (fun y : Real => y) (nu : Measure Real) := by
    apply (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hNu
  exact forwardPlansEqDistanceOptimalFace
    hMuId hNuId gammaForward hForward
