import Definitions.Def_JuilletCanonicalRoutes

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    (mu nu : FiniteMeasure Real) (x : Real)
    (hAtomlessAt : (mu : Measure Real) {x} = 0) :
    signedCumulative mu nu x <= signedCumulativeLeft mu nu x := by
  have hMu :
      (mu : Measure Real) (Iic x) = (mu : Measure Real) (Iio x) :=
    measure_congr (Iio_ae_eq_Iic' hAtomlessAt).symm
  have hNu :
      (nu : Measure Real) (Iio x) <= (nu : Measure Real) (Iic x) :=
    measure_mono Iio_subset_Iic_self
  have hNuReal :
      ((nu : Measure Real) (Iio x)).toReal <=
        ((nu : Measure Real) (Iic x)).toReal :=
    ENNReal.toReal_mono (measure_ne_top (nu : Measure Real) (Iic x)) hNu
  simp only [signedCumulative, signedCumulativeLeft, hMu]
  linarith
