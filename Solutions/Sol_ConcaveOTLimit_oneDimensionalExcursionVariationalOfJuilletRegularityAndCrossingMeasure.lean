import Theorems.Thm_ConcaveOTLimit_juilletBadCrossingLevelsNullOfAeRegular
import Theorems.Thm_ConcaveOTLimit_juilletCumulativeLevelMapACOfPositiveCrossingMeasure
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariationalOfBadNullAndMapAC

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
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
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan) :
    IsForwardPlan gammaEC /\
      {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} =
        distanceOptimalFace mu nu /\
      (forall profile : Real -> Real,
        AdmissibleConcaveProfile profile ->
          IsMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) /\
      (forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          IsUniqueMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) := by
  have hBadNull :
      (volume : Measure Real)
        {h |
          ∃ z : Real,
            (z, h) ∈ generalizedCumulativeGraph mu nu ∧
              ¬ (IsGoodIncreasingCrossing mu nu z h ∨
                IsGoodDecreasingCrossing mu nu z h)} = 0 :=
    juilletBadCrossingLevelsNullOfAeRegular mu nu hAeRegular
  have hMapAC :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
        (volume : Measure Real) :=
    juilletCumulativeLevelMapACOfPositiveCrossingMeasure
      mu nu hAtomless zeta hFirst hSecondAC hCrossing
  exact oneDimensionalExcursionVariationalOfBadNullAndMapAC
    hFirstMu hFirstNu hSingular hAtomless hOrder hBadNull hMapAC gammaEC hEC
