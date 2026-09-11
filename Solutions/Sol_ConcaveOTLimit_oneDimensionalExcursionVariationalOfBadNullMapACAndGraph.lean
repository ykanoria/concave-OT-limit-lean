import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
import Theorems.Thm_ConcaveOTLimit_juilletIdentificationOfBadNullAndMapAC
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariationalOfSupportAndIdentification

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
  apply oneDimensionalExcursionVariationalOfSupportAndIdentification
    hFirstMu hFirstNu hSingular hAtomless hOrder gammaEC hEC
  · intro profile hProfile gamma hMin hForward
    exact
      existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
        hProfile hFirstMu hFirstNu hSingular hMin hForward
  · exact juilletIdentificationOfBadNullAndMapAC
      hSingular hAtomless hOrder hBadNull hMapAC gammaEC hEC hGraph
