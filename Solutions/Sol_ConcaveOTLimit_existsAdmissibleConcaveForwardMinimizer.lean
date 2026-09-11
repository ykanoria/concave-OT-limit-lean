import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostLowerSemicontinuousOnForward
import Theorems.Thm_ConcaveOTLimit_existsForwardMinimizerOfLowerSemicontinuous

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real))
    (gammaForward : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gammaForward) :
    exists gamma : FiniteCoupling mu nu,
      IsMinimizerOn
        {eta : FiniteCoupling mu nu | IsForwardPlan eta}
        (profileCost profile) gamma := by
  exact existsForwardMinimizerOfLowerSemicontinuous
    gammaForward hForward (profileCost profile)
    (admissibleConcaveProfileCostLowerSemicontinuousOnForward
      hProfile hMu hNu)
