import Theorems.Thm_ConcaveOTLimit_forwardPlansEqDistanceOptimalFaceOfAbsMoments
import Theorems.Thm_ConcaveOTLimit_isForwardPlanOfJuilletExcursionPlan

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (gamma : FiniteCoupling mu nu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    IsForwardPlan gamma /\
      {eta : FiniteCoupling mu nu | IsForwardPlan eta} =
        distanceOptimalFace mu nu := by
  have hForward : IsForwardPlan gamma :=
    isForwardPlanOfJuilletExcursionPlan hAtomless hOrder hExcursion
  exact ⟨hForward,
    forwardPlansEqDistanceOptimalFaceOfAbsMoments
      hFirstMu hFirstNu gamma hForward⟩
