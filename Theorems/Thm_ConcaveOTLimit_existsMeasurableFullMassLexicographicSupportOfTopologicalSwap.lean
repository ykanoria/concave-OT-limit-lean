import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMassPrimaryMonotoneSupport

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A tied-secondary swap inequality on strict-forward points of the
topological support upgrades the primary support to the measurable full-mass
lexicographic support used by the support-production interface. -/
theorem existsMeasurableFullMassLexicographicSupportOfTopologicalSwap
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hForward : IsForwardPlan gamma)
    (hTiedSecondaryOnStrictTopologicalSupport :
      forall {x y x' y' : Real},
        (x, y) ∈ Measure.support
            (gamma.plan : Measure (Real × Real)) ->
        (x', y') ∈ Measure.support
            (gamma.plan : Measure (Real × Real)) ->
        x < y ->
        x' < y' ->
        dist x y + dist x' y' = dist x y' + dist x' y ->
        profile (dist x y) + profile (dist x' y') <=
          profile (dist x y') + profile (dist x' y)) :
    exists support : Set (Real × Real),
      MeasurableSet support /\
      IsSupported gamma support /\
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y)) := by
  obtain
      ⟨support, hMeasurable, hSupported, hStrict, hTopological, hPrimary⟩ :=
    existsMeasurableFullMassPrimaryMonotoneSupport hSingular hForward
  refine ⟨support, hMeasurable, hSupported, ?_⟩
  intro x y x' y' hxy hx'y'
  refine ⟨hPrimary hxy hx'y', ?_⟩
  exact hTiedSecondaryOnStrictTopologicalSupport
    (hTopological hxy) (hTopological hx'y')
    (hStrict hxy) (hStrict hx'y')

end ConcaveOTLimit
