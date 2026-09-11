import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory Set

open scoped MeasureTheory

namespace ConcaveOTLimit

/-- The nondifferentiable and derivative-zero values of a real Lipschitz map
form a Lebesgue-null set. -/
theorem lipschitzCriticalValuesNull
    {C : NNReal} {g : Real -> Real}
    (hg : LipschitzWith C g) :
    volume
      (g '' {t : Real | Not (DifferentiableAt Real g t)} ∪
        g '' {t : Real | HasDerivAt g 0 t}) = 0 := by
  have hNondifferentiable :
      volume {t : Real | Not (DifferentiableAt Real g t)} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact (hg.ae_differentiableAt (μ := volume)).mono fun _ ht hbad => hbad ht
  apply measure_union_null
  · rw [← hausdorffMeasure_real, ← nonpos_iff_eq_zero]
    calc
      μH[1] (g '' {t : Real | Not (DifferentiableAt Real g t)})
          ≤ (C : ENNReal) ^ (1 : Real) *
              μH[1] {t : Real | Not (DifferentiableAt Real g t)} :=
        hg.hausdorffMeasure_image_le
          (show (0 : Real) ≤ 1 from zero_le_one) _
      _ = 0 := by
        rw [hausdorffMeasure_real, hNondifferentiable, mul_zero]
  · apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := volume) (f' := fun _ : Real => 0)
    · intro t ht
      simpa using ht.hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      simp

end ConcaveOTLimit
