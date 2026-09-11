import Definitions.Def_JuilletMassClock
import Theorems.Thm_ConcaveOTLimit_signedCumulativeBoundedVariation
import Theorems.Thm_ConcaveOTLimit_signedCumulativeRightContinuousAndLeftLim
import Mathlib.Topology.MetricSpace.Lipschitz

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- An atomless source forces a mass-clock factor of the signed cumulative
function to traverse every target atom with slope `-1`. -/
theorem signedCumulativeMassClockJumpInterpolation
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (g : Real -> Real)
    (hg : LipschitzWith 1 g)
    (hFactor : forall x : Real,
      g (cumulativeMassClock mu nu x) =
        signedCumulative mu nu x) :
    (forall x : Real,
      g (cumulativeMassClockLeft mu nu x) =
        signedCumulativeLeft mu nu x) /\
      forall x t : Real,
        t ∈ Icc (cumulativeMassClockLeft mu nu x)
          (cumulativeMassClock mu nu x) ->
        g t =
          signedCumulativeLeft mu nu x -
            (t - cumulativeMassClockLeft mu nu x) := by
  have hCumulativeTendsto
      (eta : FiniteMeasure Real) (x : Real) :
      Tendsto
        (fun y : Real => (eta : Measure Real).real (Iic y))
        (nhdsWithin x (Iio x))
        (nhds ((eta : Measure Real).real (Iio x))) := by
    have hTendsto :=
      (signedCumulativeBoundedVariation eta
        (0 : FiniteMeasure Real)).tendsto_leftLim x
    rw [(signedCumulativeRightContinuousAndLeftLim eta
      (0 : FiniteMeasure Real)).2 x] at hTendsto
    have hCumulative :
        signedCumulative eta (0 : FiniteMeasure Real) =
          fun y : Real => (eta : Measure Real).real (Iic y) := by
      funext y
      simp [signedCumulative, Measure.real]
    rw [hCumulative] at hTendsto
    simpa [signedCumulative, signedCumulativeLeft, Measure.real] using
      hTendsto
  have hClockTendsto (x : Real) :
      Tendsto (cumulativeMassClock mu nu)
        (nhdsWithin x (Iio x))
        (nhds (cumulativeMassClockLeft mu nu x)) := by
    simpa only [cumulativeMassClock, cumulativeMassClockLeft] using
      (hCumulativeTendsto mu x).add (hCumulativeTendsto nu x)
  have hSignedTendsto (x : Real) :
      Tendsto (signedCumulative mu nu)
        (nhdsWithin x (Iio x))
        (nhds (signedCumulativeLeft mu nu x)) := by
    have hTendsto :=
      (signedCumulativeBoundedVariation mu nu).tendsto_leftLim x
    rw [(signedCumulativeRightContinuousAndLeftLim mu nu).2 x] at hTendsto
    exact hTendsto
  have hLeftFactor :
      forall x : Real,
        g (cumulativeMassClockLeft mu nu x) =
          signedCumulativeLeft mu nu x := by
    intro x
    have hToLeft :
        Tendsto (fun y => g (cumulativeMassClock mu nu y))
          (nhdsWithin x (Iio x))
          (nhds (g (cumulativeMassClockLeft mu nu x))) :=
      (hg.continuous.tendsto _).comp (hClockTendsto x)
    have hToSigned :
        Tendsto (fun y => g (cumulativeMassClock mu nu y))
          (nhdsWithin x (Iio x))
          (nhds (signedCumulativeLeft mu nu x)) := by
      simpa only [hFactor] using hSignedTendsto x
    exact tendsto_nhds_unique hToLeft hToSigned
  have hJump (x : Real) :
      signedCumulative mu nu x =
        signedCumulativeLeft mu nu x -
          (cumulativeMassClock mu nu x -
            cumulativeMassClockLeft mu nu x) := by
    have hMu :
        (mu : Measure Real) (Iic x) =
          (mu : Measure Real) (Iio x) :=
      measure_congr (Iio_ae_eq_Iic' (hAtomless x)).symm
    simp only [signedCumulative, signedCumulativeLeft,
      cumulativeMassClock, cumulativeMassClockLeft, Measure.real, hMu]
    ring
  refine ⟨hLeftFactor, ?_⟩
  intro x t ht
  rcases ht with ⟨hLeft, hRight⟩
  have hFromLeft :=
    hg.dist_le_mul t (cumulativeMassClockLeft mu nu x)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hFromLeft
  rw [abs_of_nonneg (sub_nonneg.mpr hLeft), hLeftFactor x] at hFromLeft
  have hLower :
      signedCumulativeLeft mu nu x -
          (t - cumulativeMassClockLeft mu nu x) <=
        g t := by
    have hLower' := (abs_le.mp hFromLeft).1
    linarith
  have hFromRight :=
    hg.dist_le_mul t (cumulativeMassClock mu nu x)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hFromRight
  rw [abs_of_nonpos (sub_nonpos.mpr hRight), hFactor x, hJump x] at hFromRight
  have hUpper :
      g t <=
        signedCumulativeLeft mu nu x -
          (t - cumulativeMassClockLeft mu nu x) := by
    have hUpper' := (abs_le.mp hFromRight).2
    linarith
  exact le_antisymm hUpper hLower

end ConcaveOTLimit
