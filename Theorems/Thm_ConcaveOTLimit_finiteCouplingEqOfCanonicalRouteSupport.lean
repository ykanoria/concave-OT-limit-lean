import Theorems.Thm_ConcaveOTLimit_juilletCanonicalRouteSetFstInjOn
import Theorems.Thm_ConcaveOTLimit_finiteCouplingEqOfGraphOfCommonInjectiveSupport

open MeasureTheory Set

namespace ConcaveOTLimit

/-- An atomless source makes a graph coupling carried by the canonical
Juillet routes the unique coupling carried by those routes. -/
theorem finiteCouplingEqOfCanonicalRouteSupport
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

end ConcaveOTLimit
