import Theorems.Thm_ConcaveOTLimit_juilletIdentificationOfCanonicalRouteSupport
import Theorems.Thm_ConcaveOTLimit_juilletRouteConcentrationOfBadNullAndMapAC

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hBadNull :
      (volume : Measure Real)
        {h |
          ∃ z : Real,
            (z, h) ∈ generalizedCumulativeGraph mu nu ∧
              ¬ (IsGoodIncreasingCrossing mu nu z h ∨
                IsGoodDecreasingCrossing mu nu z h)} = 0)
    (hMapAC :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
        (volume : Measure Real))
    (gammaEC : FiniteCoupling mu nu)
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan)
    {T : Real -> Real}
    (hGraph : IsGraphPlan gammaEC T) :
    forall gamma : FiniteCoupling mu nu,
      IsJuilletExcursionPlan mu nu gamma.plan ->
        gamma = gammaEC := by
  have hRouteConcentration :
      forall gamma : FiniteCoupling mu nu,
        IsJuilletExcursionPlan mu nu gamma.plan ->
          IsSupported gamma (juilletCanonicalRouteSet mu nu) :=
    juilletRouteConcentrationOfBadNullAndMapAC
      hSingular hAtomless hOrder hBadNull hMapAC
  exact juilletIdentificationOfCanonicalRouteSupport
    hAtomless gammaEC hGraph
      (hRouteConcentration gammaEC hEC) hRouteConcentration
