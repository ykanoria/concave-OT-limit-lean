import Theorems.Thm_ConcaveOTLimit_isCompactForwardPlanSet
import Mathlib.Topology.Semicontinuity.Basic

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
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
    LowerSemicontinuousOn.exists_isMinOn
      hNonempty (isCompactForwardPlanSet mu nu)
        hLowerSemicontinuous
  exact ⟨gamma, hGammaForward, fun _ hEta => hGammaMin hEta⟩
