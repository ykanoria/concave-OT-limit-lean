import Theorems.Thm_ConcaveOTLimit_juilletIdentificationOfCanonicalRouteSupport
import Theorems.Thm_ConcaveOTLimit_juilletRouteConcentrationOfBadNullAndMapAC

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The explicit bad-level and cumulative-pushforward reductions identify
every Juillet excursion coupling with a distinguished graph excursion
coupling. -/
theorem juilletIdentificationOfBadNullAndMapAC
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
  apply juilletIdentificationOfCanonicalRouteSupport
    hAtomless gammaEC hGraph
  · exact juilletRouteConcentrationOfBadNullAndMapAC
      hSingular hAtomless hOrder hBadNull hMapAC gammaEC hEC
  · exact juilletRouteConcentrationOfBadNullAndMapAC
      hSingular hAtomless hOrder hBadNull hMapAC

end ConcaveOTLimit
