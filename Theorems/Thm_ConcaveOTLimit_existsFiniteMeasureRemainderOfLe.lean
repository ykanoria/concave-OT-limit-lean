import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.Sub

open MeasureTheory

namespace ConcaveOTLimit

/-- A dominated finite measure can be removed while leaving a finite
remainder that recombines exactly with it. -/
theorem existsFiniteMeasureRemainderOfLe
    {Omega : Type*} [MeasurableSpace Omega]
    (gamma removed : FiniteMeasure Omega)
    (hRemoved :
      (removed : Measure Omega) ≤ (gamma : Measure Omega)) :
    ∃ remainder : FiniteMeasure Omega,
      (remainder : Measure Omega) =
          (gamma : Measure Omega) - (removed : Measure Omega) ∧
        (remainder : Measure Omega) ≤ (gamma : Measure Omega) ∧
        remainder + removed = gamma := by
  let remainder : FiniteMeasure Omega :=
    ⟨(gamma : Measure Omega) - (removed : Measure Omega),
      Measure.isFiniteMeasure_sub⟩
  refine ⟨remainder, rfl, ?_, ?_⟩
  · exact Measure.sub_le
  · apply FiniteMeasure.toMeasure_injective
    change
      (gamma : Measure Omega) - (removed : Measure Omega) +
          (removed : Measure Omega) =
        (gamma : Measure Omega)
    exact Measure.sub_add_cancel_of_le hRemoved

end ConcaveOTLimit
