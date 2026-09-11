import Theorems.Thm_ConcaveOTLimit_existsMeasurableTransportDirection
import Theorems.Thm_ConcaveOTLimit_transportSetIsSigmaCompact

open Set

namespace ConcaveOTLimit

/-- The canonical measurable direction on the transport set extends by zero
to a measurable field on the ambient normed space. -/
theorem existsMeasurableGlobalTransportDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E]
    {Gamma : Set (E × E)}
    (hSigma : IsSigmaCompact Gamma)
    (hNoCrossing : NoCrossing Gamma) :
    exists directionField : E -> E,
      Measurable directionField /\
        ∀ z ∈ transportSet Gamma,
          ∀ x y, (x, y) ∈ Gamma ->
            x ≠ y ->
            z ∈ openSegment Real x y ->
              directionField z = rayDirection x y := by
  classical
  obtain ⟨direction, hDirectionMeasurable, hDirectionAgrees⟩ :=
    existsMeasurableTransportDirection hSigma hNoCrossing
  have hTransportMeasurable : MeasurableSet (transportSet Gamma) := by
    obtain ⟨compactPiece, hCompact, hCover⟩ :=
      transportSetIsSigmaCompact hSigma
    rw [← hCover]
    exact MeasurableSet.iUnion fun k =>
      (hCompact k).isClosed.measurableSet
  let directionField : E -> E := fun z =>
    if hz : z ∈ transportSet Gamma then direction ⟨z, hz⟩ else 0
  have hFieldMeasurable : Measurable directionField := by
    exact hDirectionMeasurable.dite measurable_const hTransportMeasurable
  refine ⟨directionField, hFieldMeasurable, ?_⟩
  intro z hz x y hxy hne hzSegment
  simp only [directionField, hz, dite_true]
  exact hDirectionAgrees ⟨z, hz⟩ x y hxy hne hzSegment

end ConcaveOTLimit
