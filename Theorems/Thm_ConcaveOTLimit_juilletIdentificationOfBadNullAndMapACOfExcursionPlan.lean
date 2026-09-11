import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Theorems.Thm_ConcaveOTLimit_juilletCanonicalRouteSetFstInjOn
import Theorems.Thm_ConcaveOTLimit_juilletIdentificationOfBadNullAndMapAC
import Theorems.Thm_ConcaveOTLimit_juilletRouteConcentrationOfBadNullAndMapAC

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The explicit bad-level and cumulative-pushforward reductions identify
every Juillet excursion coupling; graphness of the distinguished excursion
coupling follows from its concentration on the canonical routes. -/
theorem juilletIdentificationOfBadNullAndMapACOfExcursionPlan
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
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan) :
    forall gamma : FiniteCoupling mu nu,
      IsJuilletExcursionPlan mu nu gamma.plan ->
        gamma = gammaEC := by
  have hGammaECSupported :
      IsSupported gammaEC (juilletCanonicalRouteSet mu nu) :=
    juilletRouteConcentrationOfBadNullAndMapAC
      hSingular hAtomless hOrder hBadNull hMapAC gammaEC hEC
  obtain ⟨T, hGraph⟩ :=
    existsGraphPlanOfSupportedFstInjOn
      gammaEC (juilletCanonicalRouteSet mu nu)
        (juilletCanonicalRouteSetFstInjOn mu nu hAtomless)
        hGammaECSupported
  exact juilletIdentificationOfBadNullAndMapAC
    hSingular hAtomless hOrder hBadNull hMapAC gammaEC hEC hGraph

end ConcaveOTLimit
