import Definitions.Def_JuilletMassClock
import Mathlib.Topology.Order.Monotone

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Plateau values of the cumulative mass clock are countable.  Its jump
points are countable as well, and the signed-cumulative levels contributed
by either side of those jumps form a Lebesgue-null countable set. -/
theorem cumulativeMassClockExceptionalSetsCountable
    (mu nu : FiniteMeasure Real) :
    let jumpPoints : Set Real :=
      {x |
        cumulativeMassClockLeft mu nu x <
          cumulativeMassClock mu nu x}
    let jumpLevels : Set Real :=
      signedCumulative mu nu '' jumpPoints ∪
        signedCumulativeLeft mu nu '' jumpPoints
    {c : Real |
      ∃ x y : Real,
        x < y ∧
          cumulativeMassClock mu nu x = c ∧
            cumulativeMassClock mu nu y = c}.Countable ∧
      jumpPoints.Countable ∧
        jumpLevels.Countable ∧ volume jumpLevels = 0 := by
  dsimp only
  have hClockMonotone : Monotone (cumulativeMassClock mu nu) := by
    intro x y hxy
    exact add_le_add
      (measureReal_mono (Iic_subset_Iic.mpr hxy))
      (measureReal_mono (Iic_subset_Iic.mpr hxy))
  have hPlateau :
      {c : Real |
        ∃ x y : Real,
          x < y ∧
            cumulativeMassClock mu nu x = c ∧
              cumulativeMassClock mu nu y = c}.Countable :=
    hClockMonotone.countable_setOf_two_preimages
  have hMuAtoms :
      {x : Real | (mu : Measure Real) {x} ≠ 0}.Countable := by
    simpa only [pos_iff_ne_zero] using
      (Measure.countable_meas_pos_of_disjoint_iUnion
        (μ := (mu : Measure Real))
        (fun x : Real => measurableSet_singleton x)
        (fun x y hxy => disjoint_singleton.mpr hxy))
  have hNuAtoms :
      {x : Real | (nu : Measure Real) {x} ≠ 0}.Countable := by
    simpa only [pos_iff_ne_zero] using
      (Measure.countable_meas_pos_of_disjoint_iUnion
        (μ := (nu : Measure Real))
        (fun x : Real => measurableSet_singleton x)
        (fun x y hxy => disjoint_singleton.mpr hxy))
  have hJumpSubset :
      {x |
        cumulativeMassClockLeft mu nu x <
          cumulativeMassClock mu nu x} ⊆
        {x : Real | (mu : Measure Real) {x} ≠ 0} ∪
          {x : Real | (nu : Measure Real) {x} ≠ 0} := by
    intro x hx
    have hMuIncrement :
        (mu : Measure Real).real (Iic x) =
          (mu : Measure Real).real (Iio x) +
            (mu : Measure Real).real {x} := by
      rw [← Iio_union_right]
      exact measureReal_union (by simp) (measurableSet_singleton x)
    have hNuIncrement :
        (nu : Measure Real).real (Iic x) =
          (nu : Measure Real).real (Iio x) +
            (nu : Measure Real).real {x} := by
      rw [← Iio_union_right]
      exact measureReal_union (by simp) (measurableSet_singleton x)
    have hIncrementPositive :
        0 <
          (mu : Measure Real).real {x} +
            (nu : Measure Real).real {x} := by
      change
        cumulativeMassClockLeft mu nu x <
          cumulativeMassClock mu nu x at hx
      unfold cumulativeMassClock cumulativeMassClockLeft at hx
      rw [hMuIncrement, hNuIncrement] at hx
      linarith
    rcases lt_or_eq_of_le
        (measureReal_nonneg :
          0 <= (mu : Measure Real).real {x}) with hMuPos | hMuZero
    · left
      exact
        (measureReal_ne_zero_iff
          (μ := (mu : Measure Real)) (s := {x})).mp hMuPos.ne'
    · right
      have hNuPos : 0 < (nu : Measure Real).real {x} := by
        simpa only [← hMuZero, zero_add] using hIncrementPositive
      exact
        (measureReal_ne_zero_iff
          (μ := (nu : Measure Real)) (s := {x})).mp hNuPos.ne'
  have hJumps :
      {x |
        cumulativeMassClockLeft mu nu x <
          cumulativeMassClock mu nu x}.Countable :=
    (hMuAtoms.union hNuAtoms).mono hJumpSubset
  have hJumpLevels :
      (signedCumulative mu nu ''
          {x |
            cumulativeMassClockLeft mu nu x <
              cumulativeMassClock mu nu x} ∪
        signedCumulativeLeft mu nu ''
          {x |
            cumulativeMassClockLeft mu nu x <
              cumulativeMassClock mu nu x}).Countable :=
    (hJumps.image (signedCumulative mu nu)).union
      (hJumps.image (signedCumulativeLeft mu nu))
  exact
    ⟨hPlateau, hJumps, hJumpLevels,
      hJumpLevels.measure_zero volume⟩

end ConcaveOTLimit
