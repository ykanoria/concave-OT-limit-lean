import Definitions.Def_ConcaveOTLimitModel

open Set

noncomputable section

namespace ConcaveOTLimit

/-- A diagonal-free no-crossing relation admits a canonical direction field
that is constant, hence zero-Lipschitz, on every generating open segment. -/
theorem existsSegmentwiseLipschitzDirectionField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)}
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hNoCrossing : NoCrossing Gamma) :
    exists directionField : E -> E,
      (∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y) /\
      ∀ x y, (x, y) ∈ Gamma ->
        LipschitzOnWith 0 directionField (openSegment Real x y) := by
  classical
  have normalize_sub_left_eq_rayDirection :
      ∀ {x y z : E}, z ∈ openSegment Real x y ->
        NormedSpace.normalize (z - x) = rayDirection x y := by
    intro x y z hz
    rw [openSegment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hsub : x + t • (y - x) - x = t • (y - x) := by
      module
    rw [hsub, NormedSpace.normalize_smul_of_pos ht.1]
    rfl
  have normalize_sub_right_eq_rayDirection :
      ∀ {x y z : E}, z ∈ openSegment Real x y ->
        NormedSpace.normalize (y - z) = rayDirection x y := by
    intro x y z hz
    rw [openSegment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hsub : y - (x + t • (y - x)) = (1 - t) • (y - x) := by
      module
    rw [hsub, NormedSpace.normalize_smul_of_pos (sub_pos.mpr ht.2)]
    rfl
  have direction_unique :
      ∀ {x y x' y' z : E},
        (x, y) ∈ Gamma ->
        (x', y') ∈ Gamma ->
        x ≠ y ->
        x' ≠ y' ->
        z ∈ openSegment Real x y ->
        z ∈ openSegment Real x' y' ->
        rayDirection x y = rayDirection x' y' := by
    intro x y x' y' z hxy hxy' hne hne' hz hz'
    by_contra hdir
    have hinter : (segment Real x y ∩ segment Real x' y').Nonempty :=
      ⟨z, openSegment_subset_segment Real x y hz,
        openSegment_subset_segment Real x' y' hz'⟩
    rcases hNoCrossing x y x' y' hxy hxy' hne hne' hdir hinter with
      hleft | hright
    · subst x'
      exact hdir <|
        (normalize_sub_left_eq_rayDirection hz).symm.trans
          (normalize_sub_left_eq_rayDirection hz')
    · subst y'
      exact hdir <|
        (normalize_sub_right_eq_rayDirection hz).symm.trans
          (normalize_sub_right_eq_rayDirection hz')
  let directionField : E -> E := fun z =>
    if hz : z ∈ transportSet Gamma then
      let p : E × E := Classical.choose hz
      rayDirection p.1 p.2
    else
      0
  have direction_agrees :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y := by
    intro z hz x y hxy hzxy
    have hp := Classical.choose_spec hz
    have hne : x ≠ y := by
      intro h
      subst y
      exact hDiagonal x hxy
    simp only [directionField, dif_pos hz]
    exact direction_unique hp.1 hxy hp.2.1 hne hp.2.2 hzxy
  refine ⟨directionField, direction_agrees, ?_⟩
  intro x y hxy
  have hne : x ≠ y := by
    intro h
    subst y
    exact hDiagonal x hxy
  rw [LipschitzOnWith.zero_iff]
  intro z hz w hw
  exact
    (direction_agrees z ⟨(x, y), hxy, hne, hz⟩ x y hxy hz).trans
      (direction_agrees w ⟨(x, y), hxy, hne, hw⟩ x y hxy hw).symm

end ConcaveOTLimit
