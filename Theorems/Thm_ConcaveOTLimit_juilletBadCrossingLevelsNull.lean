import Theorems.Thm_ConcaveOTLimit_completedGraphLevelFiniteAe
import Theorems.Thm_ConcaveOTLimit_juilletBadCrossingLevelsNullOfAeRegular
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariationalOfBadNullAndMapAC

open MeasureTheory Set

namespace ConcaveOTLimit

/-- For an atomless source, levels admitting a completed-graph hit that is
not a good increasing or decreasing crossing are Lebesgue-null. -/
theorem juilletBadCrossingLevelsNull
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu) :
    (volume : Measure Real)
      {h |
        ∃ z : Real,
          (z, h) ∈ generalizedCumulativeGraph mu nu ∧
            ¬ (IsGoodIncreasingCrossing mu nu z h ∨
              IsGoodDecreasingCrossing mu nu z h)} = 0 :=
  juilletBadCrossingLevelsNullOfAeRegular mu nu
    (generalizedCumulativeGraphRegularAe mu nu hAtomless)

/-- Source-level absolute continuity is the only remaining analytic input
needed for the one-dimensional excursion variational conclusion. -/
theorem oneDimensionalExcursionVariationalOfSourceLevelMapAC
    {mu nu : FiniteMeasure Real}
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hMapAC :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
        (volume : Measure Real))
    (gammaEC : FiniteCoupling mu nu)
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan) :
    IsForwardPlan gammaEC ∧
      {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} =
        distanceOptimalFace mu nu ∧
      (∀ profile : Real → Real,
        AdmissibleConcaveProfile profile →
          IsMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) ∧
      (∀ profile : Real → Real,
        AdmissibleStrictlyConcaveProfile profile →
          IsUniqueMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) :=
  oneDimensionalExcursionVariationalOfBadNullAndMapAC
    hFirstMu hFirstNu hSingular hAtomless hOrder
      (juilletBadCrossingLevelsNull mu nu hAtomless)
      hMapAC gammaEC hEC

end ConcaveOTLimit
