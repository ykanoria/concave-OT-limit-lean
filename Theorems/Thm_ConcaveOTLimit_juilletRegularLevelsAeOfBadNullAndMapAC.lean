import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem signedCumulativeMeasurable
    (mu nu : FiniteMeasure Real) :
    Measurable (signedCumulative mu nu) := by
  have hMuMonotone :
      Monotone (fun x : Real => ((mu : Measure Real) (Iic x)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono
      (measure_ne_top (mu : Measure Real) (Iic b))
      (measure_mono (Iic_subset_Iic.mpr hab))
  have hNuMonotone :
      Monotone (fun x : Real => ((nu : Measure Real) (Iic x)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono
      (measure_ne_top (nu : Measure Real) (Iic b))
      (measure_mono (Iic_subset_Iic.mpr hab))
  exact hMuMonotone.measurable.sub hNuMonotone.measurable

/-- If levels with a generalized-graph hit that is not a good crossing are
Lebesgue-null, and source cumulative levels have a Lebesgue-absolutely
continuous distribution, then source-almost every cumulative level has only
good increasing or decreasing hits. -/
theorem juilletRegularLevelsAeOfBadNullAndMapAC
    (mu nu : FiniteMeasure Real)
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
    ∀ᵐ x ∂(mu : Measure Real),
      ∀ z : Real,
        (z, signedCumulative mu nu x) ∈
            generalizedCumulativeGraph mu nu ->
          IsGoodIncreasingCrossing
              mu nu z (signedCumulative mu nu x) ∨
            IsGoodDecreasingCrossing
              mu nu z (signedCumulative mu nu x) := by
  let bad : Set Real :=
    {h |
      ∃ z : Real,
        (z, h) ∈ generalizedCumulativeGraph mu nu ∧
          ¬ (IsGoodIncreasingCrossing mu nu z h ∨
            IsGoodDecreasingCrossing mu nu z h)}
  have hBadNull' : (volume : Measure Real) bad = 0 := by
    simpa only [bad] using hBadNull
  have hMapBadNull :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) bad = 0 :=
    hMapAC hBadNull'
  have hMapRegular :
      ∀ᵐ h ∂Measure.map (signedCumulative mu nu) (mu : Measure Real),
        h ∉ bad := by
    apply ae_iff.mpr
    simpa only [not_not, setOf_mem_eq] using hMapBadNull
  have hSourceRegular :
      ∀ᵐ x ∂(mu : Measure Real),
        signedCumulative mu nu x ∉ bad :=
    ae_of_ae_map
      (signedCumulativeMeasurable mu nu).aemeasurable hMapRegular
  filter_upwards [hSourceRegular] with x hx
  intro z hGraph
  by_contra hNotGood
  apply hx
  exact ⟨z, hGraph, hNotGood⟩

end ConcaveOTLimit
