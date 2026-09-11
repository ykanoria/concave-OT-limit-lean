import Theorems.Thm_ConcaveOTLimit_existsMeasurableStrictForwardTopologicalSupport
import Theorems.Thm_ConcaveOTLimit_forwardPairsDistanceTwoCycleAndReroutingOfTie

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hSingular : FiniteMutuallySingular mu nu)
    (hForward : IsForwardPlan gamma) :
    exists S : Set (Real × Real),
      MeasurableSet S /\
      IsSupported gamma S /\
      (forall {x y : Real}, (x, y) ∈ S -> x < y) /\
      S ⊆ Measure.support
        (gamma.plan : Measure (Real × Real)) /\
      (forall {x y x' y' : Real},
        (x, y) ∈ S -> (x', y') ∈ S ->
          dist x y + dist x' y' <= dist x y' + dist x' y) := by
  obtain ⟨S, hMeasurable, hSupported, hStrict, hTopological⟩ :=
    existsMeasurableStrictForwardTopologicalSupport hSingular hForward
  refine
    ⟨S, hMeasurable, hSupported, hStrict, hTopological, ?_⟩
  intro x y x' y' hxy hx'y'
  exact
    (forwardPairsDistanceTwoCycleAndReroutingOfTie
      (hStrict hxy).le (hStrict hx'y').le).1
