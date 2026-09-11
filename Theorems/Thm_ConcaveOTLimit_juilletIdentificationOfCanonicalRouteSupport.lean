import Theorems.Thm_ConcaveOTLimit_finiteCouplingEqOfCanonicalRouteSupport

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Concentration of every Juillet excursion plan on the canonical routes
identifies it with a graph coupling already carried by those routes. -/
theorem juilletIdentificationOfCanonicalRouteSupport
    {mu nu : FiniteMeasure Real}
    (hAtomless : IsAtomlessFinite mu)
    (gammaEC : FiniteCoupling mu nu)
    {T : Real -> Real}
    (hGraph : IsGraphPlan gammaEC T)
    (hGammaEC :
      IsSupported gammaEC (juilletCanonicalRouteSet mu nu))
    (hRouteConcentration :
      forall gamma : FiniteCoupling mu nu,
        IsJuilletExcursionPlan mu nu gamma.plan ->
          IsSupported gamma (juilletCanonicalRouteSet mu nu)) :
    forall gamma : FiniteCoupling mu nu,
      IsJuilletExcursionPlan mu nu gamma.plan ->
        gamma = gammaEC := by
  intro gamma hGamma
  exact finiteCouplingEqOfCanonicalRouteSupport
    hAtomless hGammaEC (hRouteConcentration gamma hGamma) hGraph

end ConcaveOTLimit
