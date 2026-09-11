import Theorems.Thm_ConcaveOTLimit_existsMeasurableGlobalTransportDirection

open Set

open ConcaveOTLimit

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E]
    {Gamma : Set (E × E)}
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hNoCrossing : NoCrossing Gamma) :
    exists directionField : E -> E,
      Measurable directionField /\
      (∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y) /\
      ∀ x y, (x, y) ∈ Gamma ->
        LipschitzOnWith 0 directionField (openSegment Real x y) := by
  obtain ⟨directionField, hMeasurable, hAgrees⟩ :=
    existsMeasurableGlobalTransportDirection hSigma hNoCrossing
  have hAgreesWithoutNondegeneracy :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y := by
    intro z hz x y hxy hzSegment
    have hne : x ≠ y := by
      intro h
      subst y
      exact hDiagonal x hxy
    exact hAgrees z hz x y hxy hne hzSegment
  refine ⟨directionField, hMeasurable,
    hAgreesWithoutNondegeneracy, ?_⟩
  intro x y hxy
  have hne : x ≠ y := by
    intro h
    subst y
    exact hDiagonal x hxy
  rw [LipschitzOnWith.zero_iff]
  intro z hz w hw
  exact
    (hAgreesWithoutNondegeneracy z
      ⟨(x, y), hxy, hne, hz⟩ x y hxy hz).trans
      (hAgreesWithoutNondegeneracy w
        ⟨(x, y), hxy, hne, hw⟩ x y hxy hw).symm
