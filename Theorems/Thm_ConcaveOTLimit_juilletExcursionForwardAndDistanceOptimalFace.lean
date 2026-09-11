import Theorems.Thm_ConcaveOTLimit_forwardPlansEqDistanceOptimalFaceOfAbsMoments
import Theorems.Thm_ConcaveOTLimit_isForwardPlanOfJuilletExcursionPlan

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The Juillet excursion plan is forward, and the forward coupling class is
the distance-optimal face, under absolute first-moment assumptions. -/
theorem juilletExcursionForwardAndDistanceOptimalFace
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

end ConcaveOTLimit
