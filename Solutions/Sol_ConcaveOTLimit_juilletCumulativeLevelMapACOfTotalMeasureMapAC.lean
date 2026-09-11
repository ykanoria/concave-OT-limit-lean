import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

open MeasureTheory Set

open ConcaveOTLimit

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

theorem solution
    (mu nu : FiniteMeasure Real)
    (hTotalMapAC :
      Measure.map (signedCumulative mu nu)
          ((mu : Measure Real) + (nu : Measure Real)) ≪
        (volume : Measure Real)) :
    Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
      (volume : Measure Real) := by
  have hMuLe :
      (mu : Measure Real) ≤
        (mu : Measure Real) + (nu : Measure Real) :=
    Measure.le_add_right le_rfl
  have hMapLe :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) ≤
        Measure.map (signedCumulative mu nu)
          ((mu : Measure Real) + (nu : Measure Real)) :=
    Measure.map_mono hMuLe (signedCumulativeMeasurable mu nu)
  exact (Measure.absolutelyContinuous_of_le hMapLe).trans hTotalMapAC
