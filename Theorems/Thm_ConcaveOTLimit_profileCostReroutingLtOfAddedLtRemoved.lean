import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory

namespace ConcaveOTLimit

/-- Replacing one integrable part of a coupling by a strictly cheaper part
while keeping the same remainder strictly lowers the profile cost. -/
theorem profileCostReroutingLtOfAddedLtRemoved
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E}
    {gamma eta : FiniteCoupling mu nu}
    {profile : Real -> Real}
    {remainder removed added : FiniteMeasure (E × E)}
    (hGamma : gamma.plan = remainder + removed)
    (hEta : eta.plan = remainder + added)
    (hRemainder :
      Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
        (remainder : Measure (E × E)))
    (hRemoved :
      Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
        (removed : Measure (E × E)))
    (hAdded :
      Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
        (added : Measure (E × E)))
    (hCheaper :
      (∫ z, profile ‖z.1 - z.2‖
          ∂(added : Measure (E × E))) <
        ∫ z, profile ‖z.1 - z.2‖
          ∂(removed : Measure (E × E))) :
    profileCost profile eta < profileCost profile gamma := by
  unfold profileCost
  rw [hEta, hGamma]
  rw [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_add,
    integral_add_measure hRemainder hAdded,
    integral_add_measure hRemainder hRemoved]
  exact add_lt_add_right hCheaper _

end ConcaveOTLimit
