import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu)
    {epsilon : Real} (hEpsilon : epsilon ≠ 0)
    (hDistance :
      Integrable (fun z : E × E => ‖z.1 - z.2‖)
        (gamma.plan : Measure (E × E)))
    (hQuotient :
      Integrable
        (fun z : E × E =>
          (powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) /
            epsilon)
        (gamma.plan : Measure (E × E))) :
    profileCost (powerProfile epsilon) gamma =
      distanceCost gamma +
        epsilon *
          integral (gamma.plan : Measure (E × E))
            (fun z =>
              (powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) /
                epsilon) := by
  change
    (∫ z, powerProfile epsilon ‖z.1 - z.2‖
      ∂(gamma.plan : Measure (E × E))) =
      (∫ z, ‖z.1 - z.2‖
        ∂(gamma.plan : Measure (E × E))) +
        epsilon *
          integral (gamma.plan : Measure (E × E))
            (fun z =>
              (powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) /
                epsilon)
  calc
    (∫ z, powerProfile epsilon ‖z.1 - z.2‖
        ∂(gamma.plan : Measure (E × E))) =
        ∫ z, ‖z.1 - z.2‖ +
          epsilon *
            ((powerProfile epsilon ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon)
          ∂(gamma.plan : Measure (E × E)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      field_simp [hEpsilon]
      ring
    _ =
        (∫ z, ‖z.1 - z.2‖
          ∂(gamma.plan : Measure (E × E))) +
          ∫ z, epsilon *
            ((powerProfile epsilon ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon)
            ∂(gamma.plan : Measure (E × E)) := by
      rw [integral_add hDistance (hQuotient.const_mul epsilon)]
    _ = _ := by
      rw [integral_const_mul]
