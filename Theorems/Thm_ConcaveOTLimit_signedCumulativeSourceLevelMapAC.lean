import Definitions.Def_JuilletCanonicalRoutes
import Theorems.Thm_ConcaveOTLimit_juilletPositiveVariationMeasureEqSource
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The positive-variation occupation statement needed to turn C168 into
source-level absolute continuity. This is the one-dimensional oriented
Banach-indicatrix theorem for cumulative functions of finite signed measures. -/
def AtomlessPositiveVariationOccupationAC : Prop :=
  forall s : SignedMeasure Real,
    (forall x : Real, s.toJordanDecomposition.posPart {x} = 0) ->
      Measure.map (fun x : Real => s (Iic x))
          s.toJordanDecomposition.posPart ≪
        (volume : Measure Real)

/-- C168 reduces source-level absolute continuity to the atomless
positive-variation occupation theorem. -/
theorem signedCumulativeSourceLevelMapAC_of_atomlessPositiveVariationOccupation
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOccupation : AtomlessPositiveVariationOccupationAC) :
    Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
      (volume : Measure Real) := by
  have hPositivePart :
      (juilletSignedMeasure mu nu).toJordanDecomposition.posPart =
        (mu : Measure Real) := by
    simpa only [juilletPositiveVariationMeasure] using
      juilletPositiveVariationMeasureEqSource hSingular
  have hPositivePartAtomless :
      forall x : Real,
        (juilletSignedMeasure mu nu).toJordanDecomposition.posPart {x} =
          0 := by
    intro x
    rw [hPositivePart]
    exact hAtomless x
  have hCumulative :
      (fun x : Real => juilletSignedMeasure mu nu (Iic x)) =
        signedCumulative mu nu := by
    funext x
    rw [juilletSignedMeasure,
      Measure.toSignedMeasure_sub_apply measurableSet_Iic]
    rfl
  have hMapAC :=
    hOccupation (juilletSignedMeasure mu nu) hPositivePartAtomless
  rw [hPositivePart, hCumulative] at hMapAC
  exact hMapAC

end ConcaveOTLimit
