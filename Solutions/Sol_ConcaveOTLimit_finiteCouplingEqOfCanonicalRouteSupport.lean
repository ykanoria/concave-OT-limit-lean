import Theorems.Thm_ConcaveOTLimit_juilletCanonicalRouteSetFstInjOn
import Theorems.Thm_ConcaveOTLimit_finiteCouplingEqOfGraphOfCommonInjectiveSupport

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    {gammaEC gamma : FiniteCoupling mu nu}
    {T : Real -> Real}
    (hAtomless : IsAtomlessFinite mu)
    (hGammaEC :
      IsSupported gammaEC (juilletCanonicalRouteSet mu nu))
    (hGamma :
      IsSupported gamma (juilletCanonicalRouteSet mu nu))
    (hGraph : IsGraphPlan gammaEC T) :
    gamma = gammaEC := by
  exact
    (finiteCouplingEqOfGraphOfCommonInjectiveSupport
      (juilletCanonicalRouteSetFstInjOn mu nu hAtomless)
      hGammaEC hGamma hGraph).symm
