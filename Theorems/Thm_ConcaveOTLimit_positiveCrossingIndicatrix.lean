import Theorems.Thm_ConcaveOTLimit_existsPositiveCrossingOccupationEnumeration
import Theorems.Thm_ConcaveOTLimit_juilletPositiveVariationMeasureEqSource

open MeasureTheory Set
open scoped ENNReal

namespace ConcaveOTLimit

noncomputable section

/-!
The pinned Mathlib has change-of-variables formulas for injective one-dimensional
maps, but no Banach-indicatrix/area formula counting noninjective fibers.  This
file removes a separate obstruction: cancellation between the input measures.
It reduces the desired identity exactly to the mutually singular Jordan pair.
-/

/-- The positive measure in the Jordan decomposition of `mu - nu`, packaged as
a finite measure. -/
def juilletJordanPositive
    (mu nu : FiniteMeasure Real) : FiniteMeasure Real :=
  ⟨(juilletSignedMeasure mu nu).toJordanDecomposition.posPart, inferInstance⟩

/-- The negative measure in the Jordan decomposition of `mu - nu`, packaged as
a finite measure. -/
def juilletJordanNegative
    (mu nu : FiniteMeasure Real) : FiniteMeasure Real :=
  ⟨(juilletSignedMeasure mu nu).toJordanDecomposition.negPart, inferInstance⟩

theorem juilletSignedMeasure_jordanPair
    (mu nu : FiniteMeasure Real) :
    juilletSignedMeasure
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) =
      juilletSignedMeasure mu nu := by
  simpa only [juilletSignedMeasure, juilletJordanPositive,
    juilletJordanNegative, FiniteMeasure.toMeasure_mk,
    JordanDecomposition.toSignedMeasure] using
    SignedMeasure.toSignedMeasure_toJordanDecomposition
      (juilletSignedMeasure mu nu)

private theorem juilletSignedMeasure_apply_Iic
    (mu nu : FiniteMeasure Real) (x : Real) :
    juilletSignedMeasure mu nu (Iic x) = signedCumulative mu nu x := by
  rw [juilletSignedMeasure,
    Measure.toSignedMeasure_sub_apply measurableSet_Iic]
  rfl

private theorem juilletSignedMeasure_apply_Iio
    (mu nu : FiniteMeasure Real) (x : Real) :
    juilletSignedMeasure mu nu (Iio x) = signedCumulativeLeft mu nu x := by
  rw [juilletSignedMeasure,
    Measure.toSignedMeasure_sub_apply measurableSet_Iio]
  rfl

theorem signedCumulative_jordanPair
    (mu nu : FiniteMeasure Real) :
    signedCumulative
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) =
      signedCumulative mu nu := by
  funext x
  calc
    _ = juilletSignedMeasure
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu)
        (Iic x) :=
      (juilletSignedMeasure_apply_Iic _ _ x).symm
    _ = juilletSignedMeasure mu nu (Iic x) := by
      rw [juilletSignedMeasure_jordanPair]
    _ = _ := juilletSignedMeasure_apply_Iic mu nu x

theorem signedCumulativeLeft_jordanPair
    (mu nu : FiniteMeasure Real) :
    signedCumulativeLeft
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) =
      signedCumulativeLeft mu nu := by
  funext x
  calc
    _ = juilletSignedMeasure
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu)
        (Iio x) :=
      (juilletSignedMeasure_apply_Iio _ _ x).symm
    _ = juilletSignedMeasure mu nu (Iio x) := by
      rw [juilletSignedMeasure_jordanPair]
    _ = _ := juilletSignedMeasure_apply_Iio mu nu x

theorem generalizedCumulativeGraph_jordanPair
    (mu nu : FiniteMeasure Real) :
    generalizedCumulativeGraph
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) =
      generalizedCumulativeGraph mu nu := by
  simp only [generalizedCumulativeGraph, signedCumulative_jordanPair,
    signedCumulativeLeft_jordanPair]

theorem isGoodIncreasingCrossing_jordanPair_iff
    (mu nu : FiniteMeasure Real) (x h : Real) :
    IsGoodIncreasingCrossing
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) x h ↔
      IsGoodIncreasingCrossing mu nu x h := by
  simp only [IsGoodIncreasingCrossing,
    generalizedCumulativeGraph_jordanPair]

theorem positiveCrossingFiber_jordanPair
    (mu nu : FiniteMeasure Real) (s : Set Real) (h : Real) :
    positiveCrossingFiber
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) s h =
      positiveCrossingFiber mu nu s h := by
  ext x
  simp only [positiveCrossingFiber, mem_setOf_eq,
    isGoodIncreasingCrossing_jordanPair_iff]

theorem juilletPositiveVariationMeasure_jordanPair
    (mu nu : FiniteMeasure Real) :
    juilletPositiveVariationMeasure
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) =
      juilletPositiveVariationMeasure mu nu := by
  simp only [juilletPositiveVariationMeasure,
    juilletSignedMeasure_jordanPair]

theorem positiveCrossingIndicatrixIdentity_jordanPair_iff
    (mu nu : FiniteMeasure Real) :
    PositiveCrossingIndicatrixIdentity
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) ↔
      PositiveCrossingIndicatrixIdentity mu nu := by
  constructor <;> intro hIdentity s hs
  · simpa only [positiveCrossingFiber_jordanPair,
      juilletPositiveVariationMeasure_jordanPair] using hIdentity s hs
  · simpa only [positiveCrossingFiber_jordanPair,
      juilletPositiveVariationMeasure_jordanPair] using hIdentity s hs

theorem juilletJordanPair_mutuallySingular
    (mu nu : FiniteMeasure Real) :
    FiniteMutuallySingular
      (juilletJordanPositive mu nu) (juilletJordanNegative mu nu) := by
  rcases
      (juilletSignedMeasure mu nu).toJordanDecomposition.mutuallySingular with
    ⟨s, hs, hpos, hneg⟩
  refine ⟨sᶜ, hs.compl, ?_, ?_⟩
  · simpa only [juilletJordanPositive, FiniteMeasure.toMeasure_mk,
      compl_compl] using hpos
  · simpa only [juilletJordanNegative, FiniteMeasure.toMeasure_mk] using hneg

/-- The remaining standard analytic premise: for mutually singular inputs, the
oriented crossing occupation measure is the positive input measure. -/
def MutuallySingularPositiveCrossingOccupationFormula : Prop :=
  ∀ mu nu : FiniteMeasure Real,
    FiniteMutuallySingular mu nu →
      ∀ s : Set Real, MeasurableSet s →
        (∫⁻ h,
            ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞)
          ∂(volume : Measure Real)) =
          (mu : Measure Real) s

/-- Cancellation is irrelevant to the indicatrix identity: the general case is
equivalent to its mutually singular Jordan pair. -/
theorem positiveCrossingIndicatrixIdentity_of_jordanPair
    (mu nu : FiniteMeasure Real)
    (hIdentity :
      PositiveCrossingIndicatrixIdentity
        (juilletJordanPositive mu nu) (juilletJordanNegative mu nu)) :
    PositiveCrossingIndicatrixIdentity mu nu :=
  (positiveCrossingIndicatrixIdentity_jordanPair_iff mu nu).mp hIdentity

/-- The full identity follows once the classical mutually singular
Banach-indicatrix case is supplied. -/
theorem positiveCrossingIndicatrixIdentity_of_mutuallySingularCase
    (hOccupation : MutuallySingularPositiveCrossingOccupationFormula)
    (mu nu : FiniteMeasure Real) :
    PositiveCrossingIndicatrixIdentity mu nu := by
  apply positiveCrossingIndicatrixIdentity_of_jordanPair
  intro s hs
  rw [juilletPositiveVariationMeasureEqSource
    (juilletJordanPair_mutuallySingular mu nu)]
  exact hOccupation _ _ (juilletJordanPair_mutuallySingular mu nu) s hs

end

end ConcaveOTLimit
