import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The cumulative total mass of `mu` and `nu` up to and including `x`. -/
def cumulativeMassClock
    (mu nu : FiniteMeasure Real) (x : Real) : Real :=
  (mu : Measure Real).real (Iic x) +
    (nu : Measure Real).real (Iic x)

/-- The cumulative total mass of `mu` and `nu` strictly to the left of `x`. -/
def cumulativeMassClockLeft
    (mu nu : FiniteMeasure Real) (x : Real) : Real :=
  (mu : Measure Real).real (Iio x) +
    (nu : Measure Real).real (Iio x)

end ConcaveOTLimit
