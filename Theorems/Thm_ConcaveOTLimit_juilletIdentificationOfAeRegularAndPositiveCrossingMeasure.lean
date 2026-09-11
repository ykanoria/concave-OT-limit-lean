import Theorems.Thm_ConcaveOTLimit_juilletBadCrossingLevelsNullOfAeRegular
import Theorems.Thm_ConcaveOTLimit_juilletIdentificationOfBadNullAndPositiveCrossingMeasure

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Almost-everywhere regular levels and an explicit positive-crossing measure
identify every Juillet excursion coupling with a distinguished graph plan. -/
theorem juilletIdentificationOfAeRegularAndPositiveCrossingMeasure
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hAeRegular :
      ∀ᵐ h ∂(volume : Measure Real),
        ∀ z : Real,
          (z, h) ∈ generalizedCumulativeGraph mu nu ->
            IsGoodIncreasingCrossing mu nu z h ∨
              IsGoodDecreasingCrossing mu nu z h)
    (zeta : Measure (Real × Real))
    (hFirst :
      Measure.map Prod.fst zeta = (mu : Measure Real))
    (hSecondAC :
      Measure.map Prod.snd zeta ≪ (volume : Measure Real))
    (hCrossing :
      ∀ᵐ p ∂zeta, IsGoodIncreasingCrossing mu nu p.1 p.2)
    (gammaEC : FiniteCoupling mu nu)
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan)
    {T : Real -> Real}
    (hGraph : IsGraphPlan gammaEC T) :
    forall gamma : FiniteCoupling mu nu,
      IsJuilletExcursionPlan mu nu gamma.plan ->
        gamma = gammaEC := by
  have hBadNull :
      (volume : Measure Real)
        {h |
          ∃ z : Real,
            (z, h) ∈ generalizedCumulativeGraph mu nu ∧
              ¬ (IsGoodIncreasingCrossing mu nu z h ∨
                IsGoodDecreasingCrossing mu nu z h)} = 0 :=
    juilletBadCrossingLevelsNullOfAeRegular mu nu hAeRegular
  exact juilletIdentificationOfBadNullAndPositiveCrossingMeasure
    hSingular hAtomless hOrder hBadNull zeta hFirst hSecondAC hCrossing
      gammaEC hEC hGraph

end ConcaveOTLimit
