import Theorems.Thm_ConcaveOTLimit_goodIncreasingCrossingLevelEqOfAtomlessAt
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

/-- A measure carried by good increasing crossings reduces the absolute
continuity of source cumulative levels to that of its second marginal. -/
theorem juilletCumulativeLevelMapACOfPositiveCrossingMeasure
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (zeta : Measure (Real × Real))
    (hFirst :
      Measure.map Prod.fst zeta = (mu : Measure Real))
    (hSecondAC :
      Measure.map Prod.snd zeta ≪ (volume : Measure Real))
    (hCrossing :
      ∀ᵐ p ∂zeta, IsGoodIncreasingCrossing mu nu p.1 p.2) :
    Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
      (volume : Measure Real) := by
  have hLevel :
      (fun p : Real × Real => signedCumulative mu nu p.1) =ᵐ[zeta]
        Prod.snd := by
    filter_upwards [hCrossing] with p hp
    exact
      (goodIncreasingCrossingLevelEqOfAtomlessAt
        mu nu p.1 p.2 (hAtomless p.1) hp).symm
  have hMapEq :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) =
        Measure.map Prod.snd zeta := by
    calc
      Measure.map (signedCumulative mu nu) (mu : Measure Real) =
          Measure.map (signedCumulative mu nu)
            (Measure.map Prod.fst zeta) := by
        rw [hFirst]
      _ = Measure.map
          (signedCumulative mu nu ∘ Prod.fst) zeta :=
        Measure.map_map
          (signedCumulativeMeasurable mu nu) measurable_fst
      _ = Measure.map Prod.snd zeta := by
        apply Measure.map_congr
        simpa only [Function.comp_apply] using hLevel
  rw [hMapEq]
  exact hSecondAC

end ConcaveOTLimit
