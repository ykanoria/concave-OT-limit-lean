import Theorems.Thm_ConcaveOTLimit_isCompactForwardPlanSet

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (gammaForward : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gammaForward)
    (functional : FiniteCoupling mu nu -> Real)
    (hContinuous : Continuous functional) :
    exists gamma : FiniteCoupling mu nu,
      IsMinimizerOn
        {eta : FiniteCoupling mu nu | IsForwardPlan eta}
        functional gamma := by
  let forwardSet : Set (FiniteCoupling mu nu) :=
    {eta | IsForwardPlan eta}
  have hNonempty : forwardSet.Nonempty :=
    ⟨gammaForward, hForward⟩
  obtain ⟨gamma, hGammaForward, hGammaMin⟩ :=
    (isCompactForwardPlanSet mu nu).exists_isMinOn
      hNonempty hContinuous.continuousOn
  exact ⟨gamma, hGammaForward, fun eta hEta => hGammaMin hEta⟩
