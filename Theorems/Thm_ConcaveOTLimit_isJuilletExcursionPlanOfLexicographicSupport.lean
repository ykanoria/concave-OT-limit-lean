import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMassMonotoneArchSupport

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A forward coupling with mutually singular marginals and a measurable
strictly-concave lexicographic support is a Juillet excursion plan in the
model's support-based sense. -/
theorem isJuilletExcursionPlanOfLexicographicSupport
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    {support : Set (Real × Real)}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    (hSingular : FiniteMutuallySingular mu nu)
    (hForward : IsForwardPlan gamma)
    (hMeasurable : MeasurableSet support)
    (hFull : IsSupported gamma support)
    (hLex :
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y))) :
    IsJuilletExcursionPlan mu nu gamma.plan := by
  obtain ⟨monotoneSupport, hSupportMeasurable,
      hSupportFull, hSupportMonotone⟩ :=
    existsMeasurableFullMassMonotoneArchSupport
      hProfile hSingular hForward hMeasurable hFull hLex
  refine ⟨?_, monotoneSupport, hSupportMeasurable, hSupportFull,
    hSupportMonotone⟩
  exact gamma.property

end ConcaveOTLimit
