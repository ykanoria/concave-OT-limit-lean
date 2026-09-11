import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory

namespace ConcaveOTLimit

/-- An almost-everywhere property holds everywhere on a measurable conull set. -/
theorem existsMeasurableFullMeasureSubsetOfAe
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {P : X -> Prop}
    (hP : ∀ᵐ x ∂mu, P x) :
    exists S : Set X,
      MeasurableSet S /\ mu Sᶜ = 0 /\ forall x, x ∈ S -> P x := by
  have hFailureNull : mu {x | Not (P x)} = 0 := ae_iff.mp hP
  obtain ⟨N, hFailureSubset, hNMeasurable, hNNull⟩ :=
    exists_measurable_superset_of_null hFailureNull
  refine ⟨Nᶜ, hNMeasurable.compl, ?_, ?_⟩
  · simpa only [compl_compl] using hNNull
  · intro x hx
    by_contra hxP
    exact hx (hFailureSubset hxP)

end ConcaveOTLimit
