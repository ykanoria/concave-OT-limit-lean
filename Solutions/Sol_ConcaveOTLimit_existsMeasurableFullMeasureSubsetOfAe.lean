import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory

theorem solution
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {P : X -> Prop}
    (hP : ∀ᵐ x ∂mu, P x) :
    exists S : Set X,
      MeasurableSet S /\ mu Sᶜ = 0 /\ forall x, x ∈ S -> P x := by
  have hBadNull : mu {x | Not (P x)} = 0 := ae_iff.1 hP
  obtain ⟨bad, hBadSubset, hBadMeasurable, hBadMeasure⟩ :=
    exists_measurable_superset_of_null hBadNull
  refine ⟨badᶜ, hBadMeasurable.compl, ?_, ?_⟩
  · simpa only [compl_compl] using hBadMeasure
  · intro x hx
    by_contra hxNotP
    exact hx (hBadSubset hxNotP)
