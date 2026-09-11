import Definitions.Def_ConcaveOTLimitModel

open Set

namespace ConcaveOTLimit

/-- A sigma-compact no-crossing endpoint relation admits a measurable
canonical direction at every point of its open transport set. -/
theorem existsMeasurableTransportDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E]
    {Gamma : Set (E × E)}
    (hSigma : IsSigmaCompact Gamma)
    (hNoCrossing : NoCrossing Gamma) :
    exists direction : transportSet Gamma -> E,
      Measurable direction /\
        ∀ z x y, (x, y) ∈ Gamma ->
          x ≠ y ->
          z.1 ∈ openSegment Real x y ->
            direction z = rayDirection x y := by
  classical
  let offDiagonal : Set (E × E) := {p | p.1 ≠ p.2}
  let directionCarrier : E -> Set E := fun d =>
    {z | ∃ p : E × E,
      p ∈ Gamma ∧ p.1 ≠ p.2 ∧ rayDirection p.1 p.2 = d ∧
        z ∈ openSegment Real p.1 p.2}
  let incidence : Set (E × E) :=
    {q | q.2 ∈ directionCarrier q.1}
  let directionSegmentEvaluation : (E × E) × Real -> E × E :=
    fun q =>
      (rayDirection q.1.1 q.1.2,
        AffineMap.lineMap q.1.1 q.1.2 q.2)

  have hEvaluationContinuousOn :
      ContinuousOn directionSegmentEvaluation
        (offDiagonal ×ˢ (univ : Set Real)) := by
    intro q hq
    have hnorm : ‖q.1.2 - q.1.1‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq.1.symm)
    dsimp only [directionSegmentEvaluation, rayDirection,
      NormedSpace.normalize]
    apply ContinuousAt.continuousWithinAt
    fun_prop

  have hIncidenceImage :
      incidence =
        directionSegmentEvaluation ''
          ((Gamma ∩ offDiagonal) ×ˢ Ioo (0 : Real) 1) := by
    ext q
    constructor
    · intro hq
      change ∃ p : E × E,
        p ∈ Gamma ∧ p.1 ≠ p.2 ∧
          rayDirection p.1 p.2 = q.1 ∧
            q.2 ∈ openSegment Real p.1 p.2 at hq
      obtain ⟨p, hpGamma, hpne, hpdir, hpseg⟩ := hq
      rw [openSegment_eq_image_lineMap] at hpseg
      obtain ⟨t, ht, hpoint⟩ := hpseg
      refine ⟨(p, t), ⟨⟨hpGamma, hpne⟩, ht⟩, ?_⟩
      exact Prod.ext hpdir hpoint
    · rintro ⟨⟨p, t⟩, ⟨⟨hpGamma, hpne⟩, ht⟩, rfl⟩
      change ∃ p' : E × E,
        p' ∈ Gamma ∧ p'.1 ≠ p'.2 ∧
          rayDirection p'.1 p'.2 = rayDirection p.1 p.2 ∧
            AffineMap.lineMap p.1 p.2 t ∈
              openSegment Real p'.1 p'.2
      exact ⟨p, hpGamma, hpne, rfl,
        lineMap_mem_openSegment Real p.1 p.2 ht⟩

  have sigmaCompactProd :
      ∀ {s : Set (E × E)} {t : Set Real},
        IsSigmaCompact s -> IsSigmaCompact t ->
          IsSigmaCompact (s ×ˢ t) := by
    intro s t hs ht
    obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨L, hL, hLt⟩ := ht
    have hcover : s ×ˢ t = ⋃ i, ⋃ j, K i ×ˢ L j := by
      rw [← hKs, ← hLt]
      ext p
      simp only [mem_prod, mem_iUnion]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨i, j, hi, hj⟩
      · rintro ⟨i, j, hi, hj⟩
        exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [hcover]
    exact isSigmaCompact_iUnion _ fun i =>
      isSigmaCompact_iUnion _ fun j =>
        ((hK i).prod (hL j)).isSigmaCompact

  have sigmaCompactInterOpen :
      ∀ {s t : Set (E × E)},
        IsSigmaCompact s -> IsOpen t -> IsSigmaCompact (s ∩ t) := by
    intro s t hs ht
    obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨F, hFclosed, _hFsub, hFt, _hFmono⟩ :=
      ht.exists_iUnion_isClosed
    have hcover : s ∩ t = ⋃ i, ⋃ j, K i ∩ F j := by
      rw [← hKs, ← hFt]
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨i, j, hi, hj⟩
      · rintro ⟨i, j, hi, hj⟩
        exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [hcover]
    exact isSigmaCompact_iUnion _ fun i =>
      isSigmaCompact_iUnion _ fun j =>
        ((hK i).inter_right (hFclosed j)).isSigmaCompact

  have sigmaCompactIoo :
      ∀ a b : Real, IsSigmaCompact (Ioo a b) := by
    intro a b
    obtain ⟨F, hFclosed, hFsub, hFunion, _hFmono⟩ :=
      (isOpen_Ioo : IsOpen (Ioo a b)).exists_iUnion_isClosed
    refine ⟨F, ?_, hFunion⟩
    intro i
    exact IsCompact.of_isClosed_subset isCompact_Icc (hFclosed i)
      ((hFsub i).trans Ioo_subset_Icc_self)

  have hOffDiagonalOpen : IsOpen offDiagonal := by
    exact isOpen_ne_fun continuous_fst continuous_snd
  have hIncidenceSigmaCompact : IsSigmaCompact incidence := by
    rw [hIncidenceImage]
    apply IsSigmaCompact.image_of_continuousOn
      (sigmaCompactProd
        (sigmaCompactInterOpen hSigma hOffDiagonalOpen)
        (sigmaCompactIoo 0 1))
    exact hEvaluationContinuousOn.mono fun q hq =>
      ⟨hq.1.2, mem_univ q.2⟩

  have normalize_sub_left_eq_direction :
      ∀ {x y z : E}, z ∈ openSegment Real x y ->
        NormedSpace.normalize (z - x) = rayDirection x y := by
    intro x y z hz
    rw [openSegment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hsub : x + t • (y - x) - x = t • (y - x) := by
      module
    rw [hsub, NormedSpace.normalize_smul_of_pos ht.1]
    rfl
  have normalize_sub_right_eq_direction :
      ∀ {x y z : E}, z ∈ openSegment Real x y ->
        NormedSpace.normalize (y - z) = rayDirection x y := by
    intro x y z hz
    rw [openSegment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hsub : y - (x + t • (y - x)) = (1 - t) • (y - x) := by
      module
    rw [hsub, NormedSpace.normalize_smul_of_pos (sub_pos.mpr ht.2)]
    rfl
  have directionUnique :
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
        (normalize_sub_left_eq_direction hz).symm.trans
          (normalize_sub_left_eq_direction hz')
    · subst y'
      exact hdir <|
        (normalize_sub_right_eq_direction hz).symm.trans
          (normalize_sub_right_eq_direction hz')
  have carrierUnique :
      ∀ {z d d' : E},
        z ∈ directionCarrier d ->
        z ∈ directionCarrier d' ->
        d = d' := by
    intro z d d' hd hd'
    obtain ⟨p, hpGamma, hpne, hpdir, hpseg⟩ := hd
    obtain ⟨p', hpGamma', hpne', hpdir', hpseg'⟩ := hd'
    rw [← hpdir, ← hpdir']
    exact directionUnique hpGamma hpGamma' hpne hpne' hpseg hpseg'

  let direction : transportSet Gamma -> E := fun z =>
    rayDirection (Classical.choose z.property).1
      (Classical.choose z.property).2
  have hDirectionCarrier :
      ∀ z, z.1 ∈ directionCarrier (direction z) := by
    intro z
    have hp := Classical.choose_spec z.property
    exact ⟨Classical.choose z.property, hp.1, hp.2.1, rfl, hp.2.2⟩

  have hDirectionMeasurable : Measurable direction := by
    apply measurable_of_isClosed
    intro C hC
    let restrictedIncidence : Set (E × E) :=
      incidence ∩ (C ×ˢ (univ : Set E))
    let spread : Set E := Prod.snd '' restrictedIncidence
    have hRestrictedSigmaCompact :
        IsSigmaCompact restrictedIncidence := by
      obtain ⟨K, hK, hKincidence⟩ := hIncidenceSigmaCompact
      refine ⟨fun i => K i ∩ (C ×ˢ (univ : Set E)), ?_, ?_⟩
      · intro i
        exact (hK i).inter_right (hC.prod isClosed_univ)
      · ext q
        change
          (q ∈ ⋃ i, K i ∩ (C ×ˢ (univ : Set E))) ↔
            q ∈ incidence ∩ (C ×ˢ (univ : Set E))
        constructor
        · rw [mem_iUnion]
          rintro ⟨i, hiK, hiC⟩
          refine ⟨?_, hiC⟩
          rw [← hKincidence]
          exact mem_iUnion.2 ⟨i, hiK⟩
        · rintro ⟨hqIncidence, hqC⟩
          rw [← hKincidence] at hqIncidence
          obtain ⟨i, hi⟩ := mem_iUnion.1 hqIncidence
          exact mem_iUnion.2 ⟨i, hi, hqC⟩
    have hSpreadSigmaCompact : IsSigmaCompact spread :=
      hRestrictedSigmaCompact.image continuous_snd
    have hSpreadMeasurable : MeasurableSet spread := by
      obtain ⟨K, hK, hKspread⟩ := hSpreadSigmaCompact
      rw [← hKspread]
      exact MeasurableSet.iUnion fun i => (hK i).measurableSet
    have hpreimage :
        direction ⁻¹' C =
          (fun z : transportSet Gamma => z.1) ⁻¹' spread := by
      ext z
      constructor
      · intro hz
        exact ⟨(direction z, z.1),
          ⟨hDirectionCarrier z, hz, mem_univ z.1⟩, rfl⟩
      · rintro ⟨⟨d, z'⟩, ⟨hdIncidence, hdC, _⟩, hz'⟩
        change z' ∈ directionCarrier d at hdIncidence
        change z' = z.1 at hz'
        rw [hz'] at hdIncidence
        have hdirection : d = direction z :=
          carrierUnique hdIncidence (hDirectionCarrier z)
        simpa [hdirection] using hdC
    rw [hpreimage]
    exact hSpreadMeasurable.preimage measurable_subtype_coe

  refine ⟨direction, hDirectionMeasurable, ?_⟩
  intro z x y hxy hne hz
  exact carrierUnique (hDirectionCarrier z)
    ⟨(x, y), hxy, hne, rfl, hz⟩

end ConcaveOTLimit
