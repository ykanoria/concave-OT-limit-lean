import Theorems.Thm_ConcaveOTLimit_juilletPositiveLevelsAe
import Theorems.Thm_ConcaveOTLimit_juilletRegularLevelsAeOfBadNullAndMapAC
import Theorems.Thm_ConcaveOTLimit_juilletRouteConcentrationOfRegularLevels

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The bad-level nullity and cumulative-pushforward absolute-continuity
interfaces concentrate every Juillet excursion coupling on the declared
relaxed canonical-route set. -/
theorem juilletRouteConcentrationOfBadNullAndMapAC
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
        (volume : Measure Real)) :
    ∀ gamma : FiniteCoupling mu nu,
      IsJuilletExcursionPlan mu nu gamma.plan ->
        IsSupported gamma (juilletCanonicalRouteSet mu nu) := by
  intro gamma hExcursion
  apply juilletRouteConcentrationOfRegularLevels
    hSingular hAtomless hOrder hExcursion
  filter_upwards
    [juilletPositiveLevelsAe
      hSingular hAtomless hOrder hExcursion,
     juilletRegularLevelsAeOfBadNullAndMapAC
      mu nu hBadNull hMapAC] with x hPositive hRegular
  exact ⟨hPositive, hRegular⟩

end ConcaveOTLimit
