import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMassMonotoneArchSupport

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
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
