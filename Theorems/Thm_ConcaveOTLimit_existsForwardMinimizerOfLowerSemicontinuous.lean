import Theorems.Thm_ConcaveOTLimit_isCompactForwardPlanSet
import Mathlib.Topology.Semicontinuity.Basic

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A lower-semicontinuous functional attains its minimum on the forward
coupling class whenever that class has a supplied inhabitant. -/
theorem existsForwardMinimizerOfLowerSemicontinuous
    {mu nu : FiniteMeasure Real}
    (gammaForward : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gammaForward)
    (functional : FiniteCoupling mu nu -> Real)
    (hLowerSemicontinuous :
      LowerSemicontinuousOn functional
        {eta : FiniteCoupling mu nu | IsForwardPlan eta}) :
    exists gamma : FiniteCoupling mu nu,
      IsMinimizerOn
        {eta : FiniteCoupling mu nu | IsForwardPlan eta}
        functional gamma := by
  let forwardSet : Set (FiniteCoupling mu nu) :=
    {eta | IsForwardPlan eta}
  have hNonempty : forwardSet.Nonempty :=
    ⟨gammaForward, hForward⟩
  obtain ⟨gamma, hGammaForward, hGammaMin⟩ :=
    hLowerSemicontinuous.exists_isMinOn
      hNonempty (isCompactForwardPlanSet mu nu)
  exact ⟨gamma, hGammaForward, hGammaMin⟩

end ConcaveOTLimit
