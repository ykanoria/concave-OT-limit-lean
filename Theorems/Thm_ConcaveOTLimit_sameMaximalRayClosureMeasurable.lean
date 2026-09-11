import Theorems.Thm_ConcaveOTLimit_maximalRayKernelDisintegration

open MeasureTheory Set Topology

noncomputable section

namespace ConcaveOTLimit

private theorem rayCoordinate_point_sameRayClosure {n : Nat}
    (R : OrientedOpenRay n) (t : Real) :
    rayCoordinate R (R.point t) = t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  unfold rayCoordinate OrientedOpenRay.point
  rw [add_sub_cancel_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hnorm]
  norm_num

private theorem point_rayCoordinate_eq_of_mem_closure_carrier {n : Nat}
    (R : OrientedOpenRay n) {z : Euclidean n}
    (hz : z ∈ closure R.carrier) :
    R.point (rayCoordinate R z) = z := by
  let s : Set (Euclidean n) :=
    {w | R.point (rayCoordinate R w) = w}
  have hsClosed : IsClosed s := by
    exact isClosed_eq
      ((OrientedOpenRay.continuous_point R).comp
        (continuous_rayCoordinate R))
      continuous_id
  have hcarrier : R.carrier ⊆ s := by
    intro w hw
    obtain ⟨t, _htl, _htu, rfl⟩ := hw
    change R.point (rayCoordinate R (R.point t)) = R.point t
    rw [rayCoordinate_point_sameRayClosure]
  exact (closure_minimal hcarrier hsClosed) hz

private theorem coordinate_bounds_of_mem_closure_carrier {n : Nat}
    (R : OrientedOpenRay n) {z : Euclidean n}
    (hz : z ∈ closure R.carrier) :
    R.lower ≤ (rayCoordinate R z : EReal) ∧
      (rayCoordinate R z : EReal) ≤ R.upper := by
  let s : Set (Euclidean n) :=
    {w |
      R.lower ≤ (rayCoordinate R w : EReal) ∧
        (rayCoordinate R w : EReal) ≤ R.upper}
  have hcoordinate :
      Continuous fun w : Euclidean n =>
        (rayCoordinate R w : EReal) :=
    continuous_coe_real_ereal.comp (continuous_rayCoordinate R)
  have hsClosed : IsClosed s := by
    exact
      (isClosed_le continuous_const hcoordinate).inter
        (isClosed_le hcoordinate continuous_const)
  have hcarrier : R.carrier ⊆ s := by
    intro w hw
    obtain ⟨t, htl, htu, rfl⟩ := hw
    change
      R.lower ≤ (rayCoordinate R (R.point t) : EReal) ∧
        (rayCoordinate R (R.point t) : EReal) ≤ R.upper
    rw [rayCoordinate_point_sameRayClosure]
    exact ⟨htl.le, htu.le⟩
  exact (closure_minimal hcarrier hsClosed) hz

private theorem point_mem_closure_carrier_of_bounds {n : Nat}
    (R : OrientedOpenRay n) (t : Real)
    (hlower : R.lower ≤ (t : EReal))
    (hupper : (t : EReal) ≤ R.upper) :
    R.point t ∈ closure R.carrier := by
  obtain ⟨s, hls, hsu⟩ :=
    EReal.lt_iff_exists_real_btwn.mp R.property.2.2
  by_cases hts : t = s
  · subst s
    exact subset_closure ⟨t, hls, hsu, rfl⟩
  have htClosure :
      t ∈ closure (openSegment Real t s) := by
    rw [closure_openSegment]
    exact left_mem_segment Real t s
  apply map_mem_closure (OrientedOpenRay.continuous_point R) htClosure
  intro u hu
  rcases lt_or_gt_of_ne hts with hlt | hgt
  · rw [openSegment_eq_Ioo hlt] at hu
    exact ⟨u,
      hlower.trans_lt (EReal.coe_lt_coe_iff.mpr hu.1),
      (EReal.coe_lt_coe_iff.mpr hu.2).trans hsu, rfl⟩
  · rw [openSegment_symm, openSegment_eq_Ioo hgt] at hu
    exact ⟨u,
      hls.trans (EReal.coe_lt_coe_iff.mpr hu.1),
      (EReal.coe_lt_coe_iff.mpr hu.2).trans_le hupper, rfl⟩

private theorem mem_closure_carrier_iff {n : Nat}
    (R : OrientedOpenRay n) (z : Euclidean n) :
    z ∈ closure R.carrier ↔
      R.lower ≤ (rayCoordinate R z : EReal) ∧
        (rayCoordinate R z : EReal) ≤ R.upper ∧
          R.point (rayCoordinate R z) = z := by
  constructor
  · intro hz
    exact
      ⟨(coordinate_bounds_of_mem_closure_carrier R hz).1,
        (coordinate_bounds_of_mem_closure_carrier R hz).2,
        point_rayCoordinate_eq_of_mem_closure_carrier R hz⟩
  · rintro ⟨hlower, hupper, hpoint⟩
    rw [← hpoint]
    exact point_mem_closure_carrier_of_bounds R _ hlower hupper

/-- Membership of a point in the closure of a varying oriented open ray is
jointly Borel measurable in the ray code and the point. -/
theorem measurableSet_mem_closure_orientedOpenRay_carrier (n : Nat) :
    MeasurableSet
      {p : OrientedOpenRay n × Euclidean n |
        p.2 ∈ closure p.1.carrier} := by
  let coordinate : OrientedOpenRay n × Euclidean n → EReal :=
    fun p => (rayCoordinate p.1 p.2 : EReal)
  have hcoordinate : Measurable coordinate :=
    measurable_coe_real_ereal.comp measurable_rayCoordinate_uncurry
  have hlower :
      Measurable fun p : OrientedOpenRay n × Euclidean n =>
        p.1.lower :=
    OrientedOpenRay.measurable_lower.comp measurable_fst
  have hupper :
      Measurable fun p : OrientedOpenRay n × Euclidean n =>
        p.1.upper :=
    OrientedOpenRay.measurable_upper.comp measurable_fst
  have hpoint :
      Measurable fun p : OrientedOpenRay n × Euclidean n =>
        p.1.point (rayCoordinate p.1 p.2) :=
    OrientedOpenRay.measurable_point_uncurry.comp
      (measurable_fst.prodMk measurable_rayCoordinate_uncurry)
  rw [show
    {p : OrientedOpenRay n × Euclidean n |
        p.2 ∈ closure p.1.carrier} =
      {p |
        p.1.lower ≤ coordinate p ∧
          coordinate p ≤ p.1.upper ∧
            p.1.point (rayCoordinate p.1 p.2) = p.2} by
      ext p
      exact mem_closure_carrier_iff p.1 p.2]
  exact
    (measurableSet_le hlower hcoordinate).inter
      ((measurableSet_le hcoordinate hupper).inter
        (measurableSet_eq_fun hpoint measurable_snd))

private theorem midpoint_mem_carrier_of_mem_closure_of_ne {n : Nat}
    (R : OrientedOpenRay n) {x y : Euclidean n}
    (hx : x ∈ closure R.carrier)
    (hy : y ∈ closure R.carrier)
    (hne : x ≠ y) :
    midpoint Real x y ∈ R.carrier := by
  let tx := rayCoordinate R x
  let ty := rayCoordinate R y
  have hxpoint : R.point tx = x :=
    point_rayCoordinate_eq_of_mem_closure_carrier R hx
  have hypoint : R.point ty = y :=
    point_rayCoordinate_eq_of_mem_closure_carrier R hy
  have htne : tx ≠ ty := by
    intro h
    apply hne
    rw [← hxpoint, ← hypoint, h]
  have hxbounds := coordinate_bounds_of_mem_closure_carrier R hx
  have hybounds := coordinate_bounds_of_mem_closure_carrier R hy
  have hmidpoint :
      R.point (midpoint Real tx ty) = midpoint Real x y := by
    rw [← hxpoint, ← hypoint]
    unfold midpoint OrientedOpenRay.point
    rw [AffineMap.lineMap_apply_module,
      AffineMap.lineMap_apply_module]
    module
  rcases lt_or_gt_of_ne htne with hxy | hyx
  · have hm :
        midpoint Real tx ty ∈ Ioo tx ty := by
      rw [← openSegment_eq_Ioo hxy]
      exact midpoint_mem_openSegment tx ty
    exact ⟨midpoint Real tx ty,
      hxbounds.1.trans_lt (EReal.coe_lt_coe_iff.mpr hm.1),
      (EReal.coe_lt_coe_iff.mpr hm.2).trans_le hybounds.2,
      hmidpoint⟩
  · have hm :
        midpoint Real tx ty ∈ Ioo ty tx := by
      rw [midpoint_comm, ← openSegment_eq_Ioo hyx]
      exact midpoint_mem_openSegment ty tx
    exact ⟨midpoint Real tx ty,
      hybounds.1.trans_lt (EReal.coe_lt_coe_iff.mpr hm.1),
      (EReal.coe_lt_coe_iff.mpr hm.2).trans_le hxbounds.2,
      hmidpoint⟩

private theorem maximalRay_eq_of_common_carrier_point_of_noCrossing
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    {R S : OrientedOpenRay n}
    (hR : R.IsMaximalTransportRay Gamma)
    (hS : S.IsMaximalTransportRay Gamma)
    {z : Euclidean n}
    (hzR : z ∈ R.carrier) (hzS : z ∈ S.carrier) :
    R = S := by
  obtain ⟨a, b, hab, habne, hzab, hdirR⟩ := hR.1 z hzR
  obtain ⟨c, d, hcd, hcdne, hzcd, hdirS⟩ := hS.1 z hzS
  have hzabSegment : z ∈ segment Real a b :=
    openSegment_subset_segment Real a b hzab
  have hzb : z ≠ b := by
    intro h
    rw [h] at hzab
    exact habne (right_mem_openSegment_iff.mp hzab)
  have hdirection :
      rayDirection a b = rayDirection c d :=
    RayLabelGeometry.rayDirection_eq_of_mem_segment_ne_right
      hNoCrossing hab hcd habne hcdne hzabSegment hzb hzcd
  exact RayLabelGeometry.maximalRay_eq_of_common_carrier_point
    hR hS (hdirR.symm.trans (hdirection.trans hdirS)) hzR hzS

section MaximalRayKernelDisintegration

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

/-- The Borel part of the same-maximal-ray-closure relation selected by the
measurable maximal ray at the pair midpoint. -/
def selectedMaximalRayClosureRelation
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    Set (Euclidean n × Euclidean n) :=
  {z |
    midpoint Real z.1 z.2 ∈ transportSet Gamma ∧
      z.1 ∈ closure (D.pairRay z).carrier ∧
      z.2 ∈ closure (D.pairRay z).carrier}

theorem measurableSet_selectedMaximalRayClosureRelation
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    MeasurableSet (selectedMaximalRayClosureRelation D) := by
  have hmidpoint :
      Measurable fun z : Euclidean n × Euclidean n =>
        midpoint Real z.1 z.2 := by
    have hcontinuous :
        Continuous fun z : Euclidean n × Euclidean n =>
          AffineMap.lineMap z.1 z.2 (⅟2 : Real) :=
      continuous_fst.lineMap continuous_snd continuous_const
    simpa only [midpoint] using hcontinuous.measurable
  have hfirst :
      Measurable fun z : Euclidean n × Euclidean n =>
        (D.pairRay z, z.1) :=
    D.measurable_pairRay.prodMk measurable_fst
  have hsecond :
      Measurable fun z : Euclidean n × Euclidean n =>
        (D.pairRay z, z.2) :=
    D.measurable_pairRay.prodMk measurable_snd
  exact
    (D.transportSet_measurable.preimage hmidpoint).inter
      ((measurableSet_mem_closure_orientedOpenRay_carrier n).preimage
          hfirst |>.inter
        ((measurableSet_mem_closure_orientedOpenRay_carrier n).preimage
          hsecond))

private theorem pairRay_eq_assigned_midpoint
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n}
    (hm : midpoint Real x y ∈ transportSet Gamma) :
    D.pairRay (x, y) =
      D.rayAssignment ⟨midpoint Real x y, hm⟩ := by
  rw [MaximalRayKernelDisintegration.pairRay,
    RayLabelGeometry.pairRay]
  exact RayLabelGeometry.pointRay_of_mem
    D.rayAssignment D.defaultRay hm

theorem selectedMaximalRayClosureRelation_subset_sameMaximalRayClosure
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    selectedMaximalRayClosureRelation D ⊆
      {z | SameMaximalRayClosure Gamma z.1 z.2} := by
  rintro ⟨x, y⟩ ⟨hm, hx, hy⟩
  rw [pairRay_eq_assigned_midpoint D hm] at hx hy
  exact
    ⟨D.rayAssignment ⟨midpoint Real x y, hm⟩,
      (D.rayAssignment_isMaximal
        ⟨midpoint Real x y, hm⟩).1, hx, hy⟩

theorem sameMaximalRayClosure_mem_selected_of_ne
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n}
    (hne : x ≠ y)
    (hSame : SameMaximalRayClosure Gamma x y) :
    (x, y) ∈ selectedMaximalRayClosureRelation D := by
  obtain ⟨R, hRmaximal, hx, hy⟩ := hSame
  have hmR :
      midpoint Real x y ∈ R.carrier :=
    midpoint_mem_carrier_of_mem_closure_of_ne R hx hy hne
  obtain ⟨a, b, hab, habne, hmab, _hdirection⟩ :=
    hRmaximal.1 (midpoint Real x y) hmR
  have hmTransport :
      midpoint Real x y ∈ transportSet Gamma :=
    ⟨(a, b), hab, habne, hmab⟩
  have hRS :
      R =
        D.rayAssignment
          ⟨midpoint Real x y, hmTransport⟩ :=
    maximalRay_eq_of_common_carrier_point_of_noCrossing
      D.noCrossing hRmaximal
      (D.rayAssignment_isMaximal
        ⟨midpoint Real x y, hmTransport⟩).1
      hmR
      (D.rayAssignment_isMaximal
        ⟨midpoint Real x y, hmTransport⟩).2
  refine ⟨hmTransport, ?_, ?_⟩
  · rw [pairRay_eq_assigned_midpoint D hmTransport, ← hRS]
    exact hx
  · rw [pairRay_eq_assigned_midpoint D hmTransport, ← hRS]
    exact hy

/-- Away from the diagonal, `SameMaximalRayClosure` is exactly the
measurable midpoint-selected relation. -/
theorem sameMaximalRayClosure_iff_selected_of_ne
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n} (hne : x ≠ y) :
    SameMaximalRayClosure Gamma x y ↔
      (x, y) ∈ selectedMaximalRayClosureRelation D :=
  ⟨sameMaximalRayClosure_mem_selected_of_ne D hne,
    fun h =>
      selectedMaximalRayClosureRelation_subset_sameMaximalRayClosure D h⟩

/-- The same-maximal-ray-closure relation off the diagonal is Borel
measurable under the concrete measurable maximal-ray disintegration. -/
theorem measurableSet_sameMaximalRayClosure_offDiagonal
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    MeasurableSet
      {z : Euclidean n × Euclidean n |
        z.1 ≠ z.2 ∧ SameMaximalRayClosure Gamma z.1 z.2} := by
  rw [show
    {z : Euclidean n × Euclidean n |
        z.1 ≠ z.2 ∧ SameMaximalRayClosure Gamma z.1 z.2} =
      {z | z.1 ≠ z.2} ∩ selectedMaximalRayClosureRelation D by
      ext z
      constructor
      · rintro ⟨hne, hSame⟩
        exact ⟨hne, (sameMaximalRayClosure_iff_selected_of_ne D hne).1 hSame⟩
      · rintro ⟨hne, hSelected⟩
        exact ⟨hne, (sameMaximalRayClosure_iff_selected_of_ne D hne).2 hSelected⟩]
  exact
    (measurableSet_eq_fun measurable_fst measurable_snd).compl.inter
      (measurableSet_selectedMaximalRayClosureRelation D)

/-- Exact reduction of global measurability to the boundary points outside
the open transport set that lie in at least one maximal-ray closure. -/
theorem measurableSet_sameMaximalRayClosure_of_boundaryDiagonal
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hBoundary :
      MeasurableSet
        {x : Euclidean n |
          x ∉ transportSet Gamma ∧
            SameMaximalRayClosure Gamma x x}) :
    MeasurableSet
      {z : Euclidean n × Euclidean n |
        SameMaximalRayClosure Gamma z.1 z.2} := by
  let boundary : Set (Euclidean n) :=
    {x |
      x ∉ transportSet Gamma ∧
        SameMaximalRayClosure Gamma x x}
  have hBoundaryDiagonal :
      MeasurableSet
        {z : Euclidean n × Euclidean n |
          z.1 = z.2 ∧ z.1 ∈ boundary} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).inter
      (hBoundary.preimage measurable_fst)
  rw [show
    {z : Euclidean n × Euclidean n |
        SameMaximalRayClosure Gamma z.1 z.2} =
      selectedMaximalRayClosureRelation D ∪
        {z | z.1 = z.2 ∧ z.1 ∈ boundary} by
      ext z
      rcases z with ⟨x, y⟩
      change
        SameMaximalRayClosure Gamma x y ↔
          (x, y) ∈ selectedMaximalRayClosureRelation D ∨
            (x = y ∧ x ∈ boundary)
      constructor
      · intro hSame
        by_cases hne : x ≠ y
        · exact Or.inl
            (sameMaximalRayClosure_mem_selected_of_ne D hne hSame)
        · have heq : x = y := not_ne_iff.mp hne
          by_cases htransport : x ∈ transportSet Gamma
          · subst y
            have hlabel :
                D.pairRay (x, x) =
                  D.rayAssignment ⟨x, htransport⟩ := by
              simpa only [midpoint_self] using
                pairRay_eq_assigned_midpoint D
                  (x := x) (y := x) (by simpa)
            refine Or.inl ⟨by simpa, ?_, ?_⟩
            · rw [hlabel]
              exact subset_closure
                (D.rayAssignment_isMaximal
                  ⟨x, htransport⟩).2
            · rw [hlabel]
              exact subset_closure
                (D.rayAssignment_isMaximal
                  ⟨x, htransport⟩).2
          · exact Or.inr
              ⟨heq, htransport, by simpa [heq] using hSame⟩
      · rintro (hSelected | ⟨heq, _hBoundary⟩)
        · exact
            selectedMaximalRayClosureRelation_subset_sameMaximalRayClosure
              D hSelected
        · simpa [heq] using _hBoundary.2]
  exact
    (measurableSet_selectedMaximalRayClosureRelation D).union
      hBoundaryDiagonal

/-- Global Borel measurability is equivalent to Borel measurability of the
only part not selected by the midpoint label: non-transport points on the
diagonal that belong to a maximal-ray closure. -/
theorem measurableSet_sameMaximalRayClosure_iff_boundaryDiagonal
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    MeasurableSet
        {z : Euclidean n × Euclidean n |
          SameMaximalRayClosure Gamma z.1 z.2} ↔
      MeasurableSet
        {x : Euclidean n |
          x ∉ transportSet Gamma ∧
            SameMaximalRayClosure Gamma x x} := by
  constructor
  · intro hSame
    have hDiagonal :
        MeasurableSet
          {x : Euclidean n |
            SameMaximalRayClosure Gamma x x} := by
      simpa only using
        hSame.preimage (measurable_id.prodMk measurable_id)
    exact D.transportSet_measurable.compl.inter hDiagonal
  · exact measurableSet_sameMaximalRayClosure_of_boundaryDiagonal D

end MaximalRayKernelDisintegration

end ConcaveOTLimit
