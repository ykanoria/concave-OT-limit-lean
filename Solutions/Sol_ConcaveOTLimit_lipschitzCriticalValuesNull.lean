import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory Set

open scoped MeasureTheory

/-- The nondifferentiable and derivative-zero values of a real Lipschitz map
form a Lebesgue-null set. -/
theorem solution
    {C : NNReal} {g : Real -> Real}
    (hg : LipschitzWith C g) :
    volume
      (g '' {t : Real | Not (DifferentiableAt Real g t)} ∪
        g '' {t : Real | HasDerivAt g 0 t}) = 0 := by
  have hBadSource :
      volume {t : Real | Not (DifferentiableAt Real g t)} = 0 := by
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    exact (hg.ae_differentiableAt (μ := volume)).mono fun _ hdiff hnDiff => hnDiff hdiff
  have hBadImage :
      volume (g '' {t : Real | Not (DifferentiableAt Real g t)}) = 0 := by
    rw [← hausdorffMeasure_real, ← nonpos_iff_eq_zero]
    refine (hg.hausdorffMeasure_image_le
      (show (0 : Real) ≤ 1 from zero_le_one)
      {t : Real | Not (DifferentiableAt Real g t)}).trans ?_
    simp only [hausdorffMeasure_real, hBadSource, mul_zero]
    exact le_rfl
  have hCriticalImage :
      volume (g '' {t : Real | HasDerivAt g 0 t}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := volume) (f' := fun _ : Real => 0) ?_ ?_
    · intro t ht
      simpa using ht.hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      simp
  exact measure_union_null hBadImage hCriticalImage
