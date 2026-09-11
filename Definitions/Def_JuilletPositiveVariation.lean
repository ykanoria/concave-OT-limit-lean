import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

open MeasureTheory

namespace ConcaveOTLimit

/-- The signed measure represented by the difference of the two marginals. -/
noncomputable def juilletSignedMeasure
    (mu nu : FiniteMeasure Real) : SignedMeasure Real :=
  (mu : Measure Real).toSignedMeasure -
    (nu : Measure Real).toSignedMeasure

/-- The positive part in the Jordan decomposition of `mu - nu`. -/
noncomputable def juilletPositiveVariationMeasure
    (mu nu : FiniteMeasure Real) : Measure Real :=
  (juilletSignedMeasure mu nu).toJordanDecomposition.posPart

end ConcaveOTLimit
