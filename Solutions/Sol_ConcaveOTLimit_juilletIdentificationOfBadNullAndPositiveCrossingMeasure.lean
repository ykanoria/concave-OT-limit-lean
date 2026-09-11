import Theorems.Thm_ConcaveOTLimit_juilletIdentificationOfBadNullAndMapAC
import Theorems.Thm_ConcaveOTLimit_juilletCumulativeLevelMapACOfPositiveCrossingMeasure

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
  have hMapAC :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
        (volume : Measure Real) :=
    juilletCumulativeLevelMapACOfPositiveCrossingMeasure
      mu nu hAtomless zeta hFirst hSecondAC hCrossing
  exact juilletIdentificationOfBadNullAndMapAC
    hSingular hAtomless hOrder hBadNull hMapAC gammaEC hEC hGraph
