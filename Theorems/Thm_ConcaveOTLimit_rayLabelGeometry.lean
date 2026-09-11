import Theorems.Thm_ConcaveOTLimit_borelMaximalRayMap
import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer
import Mathlib.Analysis.Convex.Topology

open MeasureTheory Set Topology

noncomputable section

namespace ConcaveOTLimit

/-! ## Elementary transport-segment geometry -/

/-- The midpoint of every nondegenerate pair in `Gamma` is a transport
point. -/
theorem midpoint_mem_transportSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} {x y : E}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y) :
    midpoint Real x y ∈ transportSet Gamma := by
  exact ⟨(x, y), hxy, hne, midpoint_mem_openSegment x y⟩

/-- The source of every nondegenerate pair in `Gamma` belongs to the
left-closed transport set. -/
theorem fst_mem_leftTransportSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} {x y : E}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y) :
    x ∈ leftTransportSet Gamma := by
  exact ⟨(x, y), hxy, hne, left_mem_segment Real x y, hne⟩

namespace RayLabelGeometry

private def lineAnchor {n : Nat}
    (d z : Euclidean n) : Euclidean n :=
  z - (inner Real z d) • d

private def lineCoordinate {n : Nat}
    (d z : Euclidean n) : Real :=
  inner Real z d

private def segmentDirection {n : Nat}
    (x y : Euclidean n) : Euclidean n :=
  rayDirection x y

private def segmentLower {n : Nat}
    (x y : Euclidean n) : Real :=
  lineCoordinate (segmentDirection x y) x

private def segmentUpper {n : Nat}
    (x y : Euclidean n) : Real :=
  lineCoordinate (segmentDirection x y) y

private theorem lineAnchor_add_lineCoordinate {n : Nat}
    (d z : Euclidean n) :
    lineAnchor d z + lineCoordinate d z • d = z := by
  unfold lineAnchor lineCoordinate
  module

private theorem inner_lineAnchor_eq_zero {n : Nat}
    {d z : Euclidean n} (hd : ‖d‖ = 1) :
    inner Real (lineAnchor d z) d = 0 := by
  unfold lineAnchor
  rw [inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hd]
  norm_num

private theorem lineCoordinate_add_smul {n : Nat}
    {d z : Euclidean n} (hd : ‖d‖ = 1) (r : Real) :
    lineCoordinate d (z + r • d) = lineCoordinate d z + r := by
  unfold lineCoordinate
  rw [inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hd]
  norm_num

private theorem lineAnchor_add_smul {n : Nat}
    {d z : Euclidean n} (hd : ‖d‖ = 1) (r : Real) :
    lineAnchor d (z + r • d) = lineAnchor d z := by
  unfold lineAnchor
  rw [show inner Real (z + r • d) d =
      inner Real z d + r by
    simpa only [lineCoordinate] using lineCoordinate_add_smul hd r]
  module

private theorem segmentDirection_norm {n : Nat}
    {x y : Euclidean n} (hne : x ≠ y) :
    ‖segmentDirection x y‖ = 1 := by
  unfold segmentDirection rayDirection
  exact NormedSpace.norm_normalize (sub_ne_zero.mpr hne.symm)

private theorem segment_second_eq {n : Nat}
    (x y : Euclidean n) :
    y = x + ‖y - x‖ • segmentDirection x y := by
  calc
    y = x + (y - x) := by abel
    _ = x + ‖y - x‖ • segmentDirection x y := by
      rw [segmentDirection, rayDirection,
        NormedSpace.norm_smul_normalize]

private theorem segment_sub_eq {n : Nat}
    (x y : Euclidean n) :
    y - x = ‖y - x‖ • segmentDirection x y := by
  rw [segmentDirection, rayDirection,
    NormedSpace.norm_smul_normalize]

private theorem segmentUpper_eq_lower_add_norm {n : Nat}
    {x y : Euclidean n} (hne : x ≠ y) :
    segmentUpper x y = segmentLower x y + ‖y - x‖ := by
  unfold segmentUpper segmentLower
  calc
    lineCoordinate (segmentDirection x y) y =
        lineCoordinate (segmentDirection x y)
          (x + ‖y - x‖ • segmentDirection x y) := by
      exact congrArg (lineCoordinate (segmentDirection x y))
        (segment_second_eq x y)
    _ = lineCoordinate (segmentDirection x y) x + ‖y - x‖ :=
      lineCoordinate_add_smul (segmentDirection_norm hne) _

private theorem segmentLower_lt_upper {n : Nat}
    {x y : Euclidean n} (hne : x ≠ y) :
    segmentLower x y < segmentUpper x y := by
  rw [segmentUpper_eq_lower_add_norm hne]
  exact lt_add_of_pos_right _
    (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))

private theorem segment_first_point {n : Nat}
    (x y : Euclidean n) :
    lineAnchor (segmentDirection x y) x +
        segmentLower x y • segmentDirection x y = x :=
  lineAnchor_add_lineCoordinate (segmentDirection x y) x

private theorem segment_second_point {n : Nat}
    {x y : Euclidean n} (hne : x ≠ y) :
    lineAnchor (segmentDirection x y) x +
        segmentUpper x y • segmentDirection x y = y := by
  calc
    lineAnchor (segmentDirection x y) x +
          segmentUpper x y • segmentDirection x y =
        lineAnchor (segmentDirection x y) x +
          (segmentLower x y + ‖y - x‖) •
            segmentDirection x y := by
      rw [segmentUpper_eq_lower_add_norm hne]
    _ =
        (lineAnchor (segmentDirection x y) x +
          segmentLower x y • segmentDirection x y) +
          ‖y - x‖ • segmentDirection x y := by
      module
    _ = x + ‖y - x‖ • segmentDirection x y := by
      rw [segment_first_point]
    _ = y := (segment_second_eq x y).symm

/-- The oriented open ray whose carrier is exactly the nondegenerate open
segment from `x` to `y`. -/
def transportSegmentRay {n : Nat}
    (x y : Euclidean n) (hne : x ≠ y) :
    OrientedOpenRay n :=
  ⟨(((lineAnchor (segmentDirection x y) x, segmentDirection x y),
      ((segmentLower x y : EReal), (segmentUpper x y : EReal)))),
    segmentDirection_norm hne,
    inner_lineAnchor_eq_zero (segmentDirection_norm hne),
    EReal.coe_lt_coe_iff.mpr (segmentLower_lt_upper hne)⟩

private theorem transportSegmentRay_point_lineMap {n : Nat}
    {x y : Euclidean n} (hne : x ≠ y) (theta : Real) :
    (transportSegmentRay x y hne).point
        (AffineMap.lineMap
          (segmentLower x y) (segmentUpper x y) theta) =
      AffineMap.lineMap x y theta := by
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  change
    lineAnchor (segmentDirection x y) x +
        ((1 - theta) • segmentLower x y +
          theta • segmentUpper x y) • segmentDirection x y =
      (1 - theta) • x + theta • y
  calc
    lineAnchor (segmentDirection x y) x +
          ((1 - theta) • segmentLower x y +
            theta • segmentUpper x y) • segmentDirection x y =
        (1 - theta) •
            (lineAnchor (segmentDirection x y) x +
              segmentLower x y • segmentDirection x y) +
          theta •
            (lineAnchor (segmentDirection x y) x +
              segmentUpper x y • segmentDirection x y) := by
      module
    _ = (1 - theta) • x + theta • y := by
      rw [segment_first_point, segment_second_point hne]

/-- The canonical segment ray has exactly the expected open-segment
carrier. -/
theorem transportSegmentRay_carrier {n : Nat}
    {x y : Euclidean n} (hne : x ≠ y) :
    (transportSegmentRay x y hne).carrier =
      openSegment Real x y := by
  ext z
  constructor
  · rintro ⟨t, htl, htu, rfl⟩
    change (segmentLower x y : EReal) < (t : EReal) at htl
    change (t : EReal) < (segmentUpper x y : EReal) at htu
    have ht :
        t ∈ Ioo (segmentLower x y) (segmentUpper x y) :=
      ⟨EReal.coe_lt_coe_iff.mp htl, EReal.coe_lt_coe_iff.mp htu⟩
    rw [← openSegment_eq_Ioo (segmentLower_lt_upper hne),
      openSegment_eq_image_lineMap] at ht
    obtain ⟨theta, htheta, htheta_t⟩ := ht
    rw [← htheta_t, transportSegmentRay_point_lineMap hne]
    exact lineMap_mem_openSegment Real x y htheta
  · intro hz
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨theta, htheta, rfl⟩ := hz
    let t :=
      AffineMap.lineMap
        (segmentLower x y) (segmentUpper x y) theta
    have ht :
        t ∈ Ioo (segmentLower x y) (segmentUpper x y) := by
      rw [← openSegment_eq_Ioo (segmentLower_lt_upper hne)]
      exact lineMap_mem_openSegment Real _ _ htheta
    refine ⟨t, ?_, ?_, ?_⟩
    · change (segmentLower x y : EReal) < (t : EReal)
      exact EReal.coe_lt_coe_iff.mpr ht.1
    · change (t : EReal) < (segmentUpper x y : EReal)
      exact EReal.coe_lt_coe_iff.mpr ht.2
    · exact transportSegmentRay_point_lineMap hne theta

/-- A transport segment, viewed as an oriented open ray, is covered by
`Gamma`. -/
theorem transportSegmentRay_coveredBy {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {x y : Euclidean n} (hxy : (x, y) ∈ Gamma) (hne : x ≠ y) :
    (transportSegmentRay x y hne).CoveredBy Gamma := by
  intro z hz
  refine ⟨x, y, hxy, hne, ?_, rfl⟩
  rw [← transportSegmentRay_carrier hne]
  exact hz

/-! ## No-crossing and aligned maximal rays -/

private theorem normalize_sub_left_eq_rayDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y z : E} (hz : z ∈ openSegment Real x y) :
    NormedSpace.normalize (z - x) = rayDirection x y := by
  rw [openSegment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hsub : x + t • (y - x) - x = t • (y - x) := by
    module
  rw [hsub, NormedSpace.normalize_smul_of_pos ht.1]
  rfl

private theorem normalize_sub_right_eq_rayDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y z : E} (hz : z ∈ openSegment Real x y) :
    NormedSpace.normalize (y - z) = rayDirection x y := by
  rw [openSegment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hsub : y - (x + t • (y - x)) = (1 - t) • (y - x) := by
    module
  rw [hsub, NormedSpace.normalize_smul_of_pos (sub_pos.mpr ht.2)]
  rfl

private theorem rayDirection_eq_of_common_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y y' z : E}
    (hz : z ∈ openSegment Real x y)
    (hz' : z ∈ openSegment Real x y') :
    rayDirection x y = rayDirection x y' :=
  (normalize_sub_left_eq_rayDirection hz).symm.trans
    (normalize_sub_left_eq_rayDirection hz')

private theorem rayDirection_eq_of_common_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x x' y z : E}
    (hz : z ∈ openSegment Real x y)
    (hz' : z ∈ openSegment Real x' y) :
    rayDirection x y = rayDirection x' y :=
  (normalize_sub_right_eq_rayDirection hz).symm.trans
    (normalize_sub_right_eq_rayDirection hz')

/-- Under `NoCrossing`, a second transport segment passing through a point
of the first segment strictly before its target has the same orientation as
the first segment. -/
theorem rayDirection_eq_of_mem_segment_ne_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} (hNoCrossing : NoCrossing Gamma)
    {x y x' y' z : E}
    (hxy : (x, y) ∈ Gamma) (hxy' : (x', y') ∈ Gamma)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hz : z ∈ segment Real x y) (hzy : z ≠ y)
    (hz' : z ∈ openSegment Real x' y') :
    rayDirection x y = rayDirection x' y' := by
  by_contra hdir
  have hinter :
      (segment Real x y ∩ segment Real x' y').Nonempty :=
    ⟨z, hz, openSegment_subset_segment Real x' y' hz'⟩
  rcases hNoCrossing x y x' y' hxy hxy' hne hne' hdir hinter with
      hleft | hright
  · subst x'
    have hzx : z ≠ x := by
      intro hzx
      subst z
      exact hne' (left_mem_openSegment_iff.mp hz')
    have hzOpen : z ∈ openSegment Real x y :=
      mem_openSegment_of_ne_left_right hzx.symm hzy.symm hz
    exact hdir (rayDirection_eq_of_common_left hzOpen hz')
  · subst y'
    by_cases hzx : z = x
    · subst z
      exact hdir (normalize_sub_right_eq_rayDirection hz')
    · have hzOpen : z ∈ openSegment Real x y :=
        mem_openSegment_of_ne_left_right (Ne.symm hzx) hzy.symm hz
      exact hdir (rayDirection_eq_of_common_right hzOpen hz')

private theorem rayCoordinate_point {n : Nat}
    (R : OrientedOpenRay n) (t : Real) :
    rayCoordinate R (R.point t) = t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  unfold rayCoordinate OrientedOpenRay.point
  rw [add_sub_cancel_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hnorm]
  norm_num

private theorem rayPoint_injective {n : Nat}
    (R : OrientedOpenRay n) :
    Function.Injective R.point := by
  intro s t hst
  have := congrArg (rayCoordinate R) hst
  simpa [rayCoordinate_point] using this

private theorem rayParameter_mem_of_point_mem_carrier {n : Nat}
    (R : OrientedOpenRay n) {t : Real}
    (ht : R.point t ∈ R.carrier) :
    R.lower < (t : EReal) ∧ (t : EReal) < R.upper := by
  obtain ⟨s, hsl, hsu, hs⟩ := ht
  have hst : s = t := rayPoint_injective R hs
  subst s
  exact ⟨hsl, hsu⟩

private theorem ray_anchor_eq_lineAnchor_of_mem {n : Nat}
    (R : OrientedOpenRay n) {z : Euclidean n}
    (hz : z ∈ R.carrier) :
    R.anchor = lineAnchor R.direction z := by
  obtain ⟨t, _htl, _htu, rfl⟩ := hz
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  have horth : inner Real R.anchor R.direction = 0 :=
    R.property.2.1
  unfold lineAnchor OrientedOpenRay.point
  rw [inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, horth, hnorm]
  norm_num

private theorem segment_lineAnchor_eq {n : Nat}
    {x y z : Euclidean n} (hne : x ≠ y)
    (hz : z ∈ segment Real x y) :
    lineAnchor (segmentDirection x y) z =
      lineAnchor (segmentDirection x y) x := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  have hsub :
      t • (y - x) =
        (t * ‖y - x‖) • segmentDirection x y := by
    calc
      t • (y - x) =
          t • (‖y - x‖ • segmentDirection x y) :=
        congrArg (fun v : Euclidean n => t • v) (segment_sub_eq x y)
      _ = (t * ‖y - x‖) • segmentDirection x y := by
        rw [smul_smul]
  change
    lineAnchor (segmentDirection x y)
        (x + t • (y - x)) =
      lineAnchor (segmentDirection x y) x
  rw [hsub, lineAnchor_add_smul (segmentDirection_norm hne)]

private theorem segmentCoordinate_mem_Ico {n : Nat}
    {x y z : Euclidean n} (hne : x ≠ y)
    (hz : z ∈ segment Real x y) (hzy : z ≠ y) :
    lineCoordinate (segmentDirection x y) z ∈
      Ico (segmentLower x y) (segmentUpper x y) := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have htne : t ≠ 1 := by
    intro htone
    subst t
    apply hzy
    module
  have htlt : t < 1 := lt_of_le_of_ne ht.2 htne
  have hnorm : 0 < ‖y - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hsub :
      t • (y - x) =
        (t * ‖y - x‖) • segmentDirection x y := by
    calc
      t • (y - x) =
          t • (‖y - x‖ • segmentDirection x y) :=
        congrArg (fun v : Euclidean n => t • v) (segment_sub_eq x y)
      _ = (t * ‖y - x‖) • segmentDirection x y := by
        rw [smul_smul]
  change
    lineCoordinate (segmentDirection x y)
        (x + t • (y - x)) ∈
      Ico (segmentLower x y) (segmentUpper x y)
  rw [hsub, lineCoordinate_add_smul (segmentDirection_norm hne),
    segmentUpper_eq_lower_add_norm hne]
  unfold segmentLower
  constructor <;> nlinarith [ht.1, htlt, hnorm]

private def rayHull {n : Nat}
    (R S : OrientedOpenRay n) : OrientedOpenRay n :=
  ⟨(((R.anchor, R.direction),
      (min R.lower S.lower, max R.upper S.upper))),
    R.property.1,
    R.property.2.1,
    (min_le_left R.lower S.lower).trans_lt
      (R.property.2.2.trans_le (le_max_left R.upper S.upper))⟩

private theorem carrier_subset_rayHull_left {n : Nat}
    (R S : OrientedOpenRay n) :
    R.carrier ⊆ (rayHull R S).carrier := by
  rintro z ⟨t, htl, htu, rfl⟩
  exact
    ⟨t, (min_le_left R.lower S.lower).trans_lt htl,
      htu.trans_le (le_max_left R.upper S.upper), rfl⟩

private theorem carrier_subset_rayHull_right {n : Nat}
    {R S : OrientedOpenRay n}
    (hdir : R.direction = S.direction)
    (hanchor : R.anchor = S.anchor) :
    S.carrier ⊆ (rayHull R S).carrier := by
  rintro z ⟨t, htl, htu, rfl⟩
  refine
    ⟨t, (min_le_right R.lower S.lower).trans_lt htl,
      htu.trans_le (le_max_right R.upper S.upper), ?_⟩
  change R.anchor + t • R.direction = S.anchor + t • S.direction
  rw [hanchor, hdir]

private theorem rayHull_carrier_subset_union {n : Nat}
    {R S : OrientedOpenRay n}
    (hdir : R.direction = S.direction)
    (hanchor : R.anchor = S.anchor)
    (hSR : S.lower < R.upper) (hRS : R.lower < S.upper) :
    (rayHull R S).carrier ⊆ R.carrier ∪ S.carrier := by
  rintro z ⟨t, htl, htu, rfl⟩
  have ht :
      (t : EReal) ∈
        Ioo (min R.lower S.lower) (max R.upper S.upper) :=
    ⟨htl, htu⟩
  rw [← Ioo_union_Ioo' hSR hRS] at ht
  rcases ht with ht | ht
  · exact Or.inl ⟨t, ht.1, ht.2, rfl⟩
  · refine Or.inr ⟨t, ht.1, ht.2, ?_⟩
    change S.anchor + t • S.direction =
      R.anchor + t • R.direction
    rw [hanchor, hdir]

private theorem rayHull_coveredBy {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {R S : OrientedOpenRay n}
    (hR : R.CoveredBy Gamma) (hS : S.CoveredBy Gamma)
    (hdir : R.direction = S.direction)
    (hanchor : R.anchor = S.anchor)
    (hSR : S.lower < R.upper) (hRS : R.lower < S.upper) :
    (rayHull R S).CoveredBy Gamma := by
  intro z hz
  rcases rayHull_carrier_subset_union hdir hanchor hSR hRS hz with
      hzR | hzS
  · obtain ⟨x, y, hxy, hne, hzxy, hxyDir⟩ := hR z hzR
    exact ⟨x, y, hxy, hne, hzxy, hxyDir⟩
  · obtain ⟨x, y, hxy, hne, hzxy, hxyDir⟩ := hS z hzS
    exact ⟨x, y, hxy, hne, hzxy, hxyDir.trans hdir.symm⟩

/-- A maximal ray absorbs every covered ray on the same oriented affine
line whose parameter interval overlaps its own. -/
theorem maximalRay_absorbs_aligned_coveredRay {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {R S : OrientedOpenRay n}
    (hR : R.IsMaximalTransportRay Gamma)
    (hS : S.CoveredBy Gamma)
    (hdir : R.direction = S.direction)
    (hanchor : R.anchor = S.anchor)
    (hSR : S.lower < R.upper) (hRS : R.lower < S.upper) :
    S.carrier ⊆ R.carrier := by
  have hHullCovered :
      (rayHull R S).CoveredBy Gamma :=
    rayHull_coveredBy hR.1 hS hdir hanchor hSR hRS
  exact (carrier_subset_rayHull_right hdir hanchor).trans
    (hR.2 (rayHull R S) (carrier_subset_rayHull_left R S)
      hHullCovered)

/-- The maximal ray assigned at a transport point lying on a segment
strictly before its target has the segment's orientation. -/
theorem assignedRay_direction_eq_of_mem_segment_ne_right {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    {x y z : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hzTransport : z ∈ transportSet Gamma)
    (hzSegment : z ∈ segment Real x y) (hzy : z ≠ y) :
    (pi ⟨z, hzTransport⟩).direction = rayDirection x y := by
  let zT : transportSet Gamma := ⟨z, hzTransport⟩
  let R := pi zT
  obtain ⟨x', y', hxy', hne', hz', hdir'⟩ :=
    (hpi zT).1.1 z (hpi zT).2
  have hdir :=
    rayDirection_eq_of_mem_segment_ne_right hNoCrossing
      hxy hxy' hne hne' hzSegment hzy hz'
  exact hdir'.symm.trans hdir.symm

private theorem assignedRay_anchor_eq_segmentRay {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    {x y z : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hzTransport : z ∈ transportSet Gamma)
    (hzSegment : z ∈ segment Real x y) (hzy : z ≠ y) :
    (pi ⟨z, hzTransport⟩).anchor =
      (transportSegmentRay x y hne).anchor := by
  let zT : transportSet Gamma := ⟨z, hzTransport⟩
  let R := pi zT
  have hdir :
      R.direction = segmentDirection x y := by
    simpa only [segmentDirection] using
      assignedRay_direction_eq_of_mem_segment_ne_right
        hNoCrossing pi hpi hxy hne hzTransport hzSegment hzy
  calc
    R.anchor = lineAnchor R.direction z :=
      ray_anchor_eq_lineAnchor_of_mem R (hpi zT).2
    _ = lineAnchor (segmentDirection x y) z := by rw [hdir]
    _ = lineAnchor (segmentDirection x y) x :=
      segment_lineAnchor_eq hne hzSegment
    _ = (transportSegmentRay x y hne).anchor := rfl

/-- The maximal ray assigned at any transport point of a pair's left-closed
segment contains the pair's entire open segment. -/
theorem transportSegment_subset_assignedRay_carrier {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    {x y z : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hzTransport : z ∈ transportSet Gamma)
    (hzSegment : z ∈ segment Real x y) (hzy : z ≠ y) :
    openSegment Real x y ⊆
      (pi ⟨z, hzTransport⟩).carrier := by
  let zT : transportSet Gamma := ⟨z, hzTransport⟩
  let R := pi zT
  let S := transportSegmentRay x y hne
  have hdir : R.direction = S.direction := by
    simpa only [S, segmentDirection] using
      assignedRay_direction_eq_of_mem_segment_ne_right
        hNoCrossing pi hpi hxy hne hzTransport hzSegment hzy
  have hanchor : R.anchor = S.anchor := by
    simpa only [R, S, zT] using
      assignedRay_anchor_eq_segmentRay
        hNoCrossing pi hpi hxy hne hzTransport hzSegment hzy
  let q := lineCoordinate (segmentDirection x y) z
  have hpoint : R.point q = z := by
    calc
      R.point q =
          lineAnchor (segmentDirection x y) x +
            q • segmentDirection x y := by
        unfold OrientedOpenRay.point
        rw [hanchor, hdir]
        rfl
      _ = lineAnchor (segmentDirection x y) z +
            q • segmentDirection x y := by
        rw [segment_lineAnchor_eq hne hzSegment]
      _ = z := lineAnchor_add_lineCoordinate
        (segmentDirection x y) z
  have hqR :
      R.lower < (q : EReal) ∧ (q : EReal) < R.upper :=
    rayParameter_mem_of_point_mem_carrier R (by
      rw [hpoint]
      exact (hpi zT).2)
  have hqS :
      q ∈ Ico (segmentLower x y) (segmentUpper x y) :=
    segmentCoordinate_mem_Ico hne hzSegment hzy
  have hSR : S.lower < R.upper := by
    change (segmentLower x y : EReal) < R.upper
    exact (EReal.coe_le_coe_iff.mpr hqS.1).trans_lt hqR.2
  have hRS : R.lower < S.upper := by
    change R.lower < (segmentUpper x y : EReal)
    exact hqR.1.trans (EReal.coe_lt_coe_iff.mpr hqS.2)
  have hsubset :
      S.carrier ⊆ R.carrier :=
    maximalRay_absorbs_aligned_coveredRay
      (hpi zT).1 (transportSegmentRay_coveredBy hxy hne)
      hdir hanchor hSR hRS
  rw [transportSegmentRay_carrier hne] at hsubset
  exact hsubset

/-- Both endpoints of a nondegenerate pair lie in the closure of the
maximal ray assigned to its midpoint. -/
theorem pair_endpoints_mem_closure_assignedMidpointRay {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y) :
    x ∈ closure
        (pi ⟨midpoint Real x y,
          midpoint_mem_transportSet hxy hne⟩).carrier ∧
      y ∈ closure
        (pi ⟨midpoint Real x y,
          midpoint_mem_transportSet hxy hne⟩).carrier := by
  have hmOpen :
      midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  have hmne : midpoint Real x y ≠ y := by
    intro hm
    rw [hm] at hmOpen
    exact hne (right_mem_openSegment_iff.mp hmOpen)
  have hsegment :
      openSegment Real x y ⊆
        (pi ⟨midpoint Real x y,
          midpoint_mem_transportSet hxy hne⟩).carrier :=
    transportSegment_subset_assignedRay_carrier
      hNoCrossing pi hpi hxy hne
      (midpoint_mem_transportSet hxy hne)
      (openSegment_subset_segment Real x y hmOpen) hmne
  have hclosure :
      closure (openSegment Real x y) ⊆
        closure
          (pi ⟨midpoint Real x y,
            midpoint_mem_transportSet hxy hne⟩).carrier :=
    closure_mono hsegment
  rw [closure_openSegment] at hclosure
  exact
    ⟨hclosure (left_mem_segment Real x y),
      hclosure (right_mem_segment Real x y)⟩

/-- Every nondegenerate pair in `Gamma` has both endpoints in the closure
of one maximal ray, namely the ray assigned to its midpoint. -/
theorem sameMaximalRayClosure_of_mem {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y) :
    SameMaximalRayClosure Gamma x y := by
  let m : transportSet Gamma :=
    ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩
  exact
    ⟨pi m, (hpi m).1,
      pair_endpoints_mem_closure_assignedMidpointRay
        hNoCrossing pi hpi hxy hne⟩

private theorem erealParameterInterval_ext
    {a b c d : EReal} (hab : a < b) (hcd : c < d)
    (h :
      {r : Real | a < (r : EReal) ∧ (r : EReal) < b} =
        {r : Real | c < (r : EReal) ∧ (r : EReal) < d}) :
    a = c ∧ b = d := by
  have hac : a ≤ c := by
    apply le_of_not_gt
    intro hca
    have hcmin : c < min a d := lt_min hca hcd
    obtain ⟨r, hcr, hrmin⟩ :=
      EReal.lt_iff_exists_real_btwn.mp hcmin
    have hra : (r : EReal) < a :=
      hrmin.trans_le (min_le_left _ _)
    have hrd : (r : EReal) < d :=
      hrmin.trans_le (min_le_right _ _)
    have hrab :
        r ∈ {s : Real | a < (s : EReal) ∧ (s : EReal) < b} := by
      rw [h]
      exact ⟨hcr, hrd⟩
    exact lt_asymm hrab.1 hra
  have hca : c ≤ a := by
    apply le_of_not_gt
    intro hac'
    have hamin : a < min c b := lt_min hac' hab
    obtain ⟨r, har, hrmin⟩ :=
      EReal.lt_iff_exists_real_btwn.mp hamin
    have hrc : (r : EReal) < c :=
      hrmin.trans_le (min_le_left _ _)
    have hrb : (r : EReal) < b :=
      hrmin.trans_le (min_le_right _ _)
    have hrcd :
        r ∈ {s : Real | c < (s : EReal) ∧ (s : EReal) < d} := by
      rw [← h]
      exact ⟨har, hrb⟩
    exact lt_asymm hrcd.1 hrc
  have hbd : b ≤ d := by
    apply le_of_not_gt
    intro hdb
    have hmaxb : max a d < b := max_lt hab hdb
    obtain ⟨r, hmaxr, hrb⟩ :=
      EReal.lt_iff_exists_real_btwn.mp hmaxb
    have har : a < (r : EReal) :=
      (le_max_left _ _).trans_lt hmaxr
    have hdr : d < (r : EReal) :=
      (le_max_right _ _).trans_lt hmaxr
    have hrcd :
        r ∈ {s : Real | c < (s : EReal) ∧ (s : EReal) < d} := by
      rw [← h]
      exact ⟨har, hrb⟩
    exact lt_asymm hrcd.2 hdr
  have hdb : d ≤ b := by
    apply le_of_not_gt
    intro hbd'
    have hmaxd : max c b < d := max_lt hcd hbd'
    obtain ⟨r, hmaxr, hrd⟩ :=
      EReal.lt_iff_exists_real_btwn.mp hmaxd
    have hcr : c < (r : EReal) :=
      (le_max_left _ _).trans_lt hmaxr
    have hbr : b < (r : EReal) :=
      (le_max_right _ _).trans_lt hmaxr
    have hrab :
        r ∈ {s : Real | a < (s : EReal) ∧ (s : EReal) < b} := by
      rw [h]
      exact ⟨hcr, hrd⟩
    exact lt_asymm hrab.2 hbr
  exact ⟨le_antisymm hac hca, le_antisymm hbd hdb⟩

private theorem orientedOpenRay_eq_of_aligned_carrier_eq {n : Nat}
    {R S : OrientedOpenRay n}
    (hdir : R.direction = S.direction)
    (hanchor : R.anchor = S.anchor)
    (hcarrier : R.carrier = S.carrier) :
    R = S := by
  have hpoint : ∀ t : Real, R.point t = S.point t := by
    intro t
    unfold OrientedOpenRay.point
    rw [hanchor, hdir]
  have hparameters :
      {r : Real |
        R.lower < (r : EReal) ∧ (r : EReal) < R.upper} =
      {r : Real |
        S.lower < (r : EReal) ∧ (r : EReal) < S.upper} := by
    ext t
    constructor
    · intro ht
      have htR : R.point t ∈ R.carrier :=
        ⟨t, ht.1, ht.2, rfl⟩
      have htS : S.point t ∈ S.carrier := by
        rw [← hpoint t, ← hcarrier]
        exact htR
      exact rayParameter_mem_of_point_mem_carrier S htS
    · intro ht
      have htS : S.point t ∈ S.carrier :=
        ⟨t, ht.1, ht.2, rfl⟩
      have htR : R.point t ∈ R.carrier := by
        rw [hpoint t, hcarrier]
        exact htS
      exact rayParameter_mem_of_point_mem_carrier R htR
  obtain ⟨hlower, hupper⟩ :=
    erealParameterInterval_ext R.property.2.2 S.property.2.2
      hparameters
  apply Subtype.ext
  apply Prod.ext
  · exact Prod.ext hanchor hdir
  · exact Prod.ext hlower hupper

/-- Two maximal rays of the same orientation that contain a common carrier
point are equal as canonical ray codes. -/
theorem maximalRay_eq_of_common_carrier_point {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {R S : OrientedOpenRay n}
    (hR : R.IsMaximalTransportRay Gamma)
    (hS : S.IsMaximalTransportRay Gamma)
    (hdir : R.direction = S.direction)
    {z : Euclidean n}
    (hzR : z ∈ R.carrier) (hzS : z ∈ S.carrier) :
    R = S := by
  have hanchor : R.anchor = S.anchor := by
    calc
      R.anchor = lineAnchor R.direction z :=
        ray_anchor_eq_lineAnchor_of_mem R hzR
      _ = lineAnchor S.direction z := by rw [hdir]
      _ = S.anchor :=
        (ray_anchor_eq_lineAnchor_of_mem S hzS).symm
  obtain ⟨r, hrl, hru, hrz⟩ := hzR
  obtain ⟨s, hsl, hsu, hsz⟩ := hzS
  have hrs : r = s := by
    apply rayPoint_injective R
    calc
      R.point r = z := hrz
      _ = S.point s := hsz.symm
      _ = R.point s := by
        unfold OrientedOpenRay.point
        rw [hanchor, hdir]
  subst s
  have hSR : S.lower < R.upper := hsl.trans hru
  have hRS : R.lower < S.upper := hrl.trans hsu
  have hSsubR :
      S.carrier ⊆ R.carrier :=
    maximalRay_absorbs_aligned_coveredRay
      hR hS.1 hdir hanchor hSR hRS
  have hRsubS :
      R.carrier ⊆ S.carrier :=
    maximalRay_absorbs_aligned_coveredRay
      hS hR.1 hdir.symm hanchor.symm hRS hSR
  exact orientedOpenRay_eq_of_aligned_carrier_eq hdir hanchor
    (Subset.antisymm hRsubS hSsubR)

/-- Maximal-ray assignments agree at any two transport points lying on the
same pair segment strictly before its target. -/
theorem maximalRayAssignment_eq_of_mem_transportSegment {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    {x y z w : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hzTransport : z ∈ transportSet Gamma)
    (hwTransport : w ∈ transportSet Gamma)
    (hzSegment : z ∈ segment Real x y) (hzy : z ≠ y)
    (hwSegment : w ∈ segment Real x y) (hwy : w ≠ y) :
    pi ⟨z, hzTransport⟩ = pi ⟨w, hwTransport⟩ := by
  let zT : transportSet Gamma := ⟨z, hzTransport⟩
  let wT : transportSet Gamma := ⟨w, hwTransport⟩
  let R := pi zT
  let S := pi wT
  have hzSaturation :
      openSegment Real x y ⊆ R.carrier :=
    transportSegment_subset_assignedRay_carrier
      hNoCrossing pi hpi hxy hne hzTransport hzSegment hzy
  have hwSaturation :
      openSegment Real x y ⊆ S.carrier :=
    transportSegment_subset_assignedRay_carrier
      hNoCrossing pi hpi hxy hne hwTransport hwSegment hwy
  have hdirR : R.direction = rayDirection x y :=
    assignedRay_direction_eq_of_mem_segment_ne_right
      hNoCrossing pi hpi hxy hne hzTransport hzSegment hzy
  have hdirS : S.direction = rayDirection x y :=
    assignedRay_direction_eq_of_mem_segment_ne_right
      hNoCrossing pi hpi hxy hne hwTransport hwSegment hwy
  have hm : midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  exact maximalRay_eq_of_common_carrier_point
    (hpi zT).1 (hpi wT).1 (hdirR.trans hdirS.symm)
    (hzSaturation hm) (hwSaturation hm)

/-! ## Total measurable ray labels -/

/-- Extend a maximal-ray assignment from the transport set to the whole
ambient space using a fixed default ray. -/
def pointRay {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (pi : transportSet Gamma → OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n) :
    Euclidean n → OrientedOpenRay n := by
  classical
  exact fun x =>
    if hx : x ∈ transportSet Gamma then pi ⟨x, hx⟩ else defaultRay

@[simp]
theorem pointRay_of_mem {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (pi : transportSet Gamma → OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    {x : Euclidean n} (hx : x ∈ transportSet Gamma) :
    pointRay Gamma pi defaultRay x = pi ⟨x, hx⟩ := by
  classical
  simp only [pointRay, dif_pos hx]

@[simp]
theorem pointRay_subtype {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (pi : transportSet Gamma → OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    (x : transportSet Gamma) :
    pointRay Gamma pi defaultRay x.1 = pi x := by
  rw [pointRay_of_mem pi defaultRay x.2]

/-- The total extension of a measurable assignment is measurable whenever
the transport set is measurable. -/
theorem measurable_pointRay {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hTransport : MeasurableSet (transportSet Gamma))
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : Measurable pi)
    (defaultRay : OrientedOpenRay n) :
    Measurable (pointRay Gamma pi defaultRay) := by
  classical
  exact hpi.dite measurable_const hTransport

/-- Label an ambient pair by the total point label of its midpoint. -/
def pairRay {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (pi : transportSet Gamma → OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n) :
    Euclidean n × Euclidean n → OrientedOpenRay n :=
  fun z => pointRay Gamma pi defaultRay (midpoint Real z.1 z.2)

@[simp]
theorem pairRay_of_mem {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (pi : transportSet Gamma → OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y) :
    pairRay Gamma pi defaultRay (x, y) =
      pi ⟨midpoint Real x y,
        midpoint_mem_transportSet hxy hne⟩ := by
  unfold pairRay
  rw [pointRay_of_mem pi defaultRay
    (midpoint_mem_transportSet hxy hne)]

/-- Midpoint-based pair labels are measurable whenever the total point
label is measurable. -/
theorem measurable_pairRay {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (pi : transportSet Gamma → OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    (hpointRay : Measurable (pointRay Gamma pi defaultRay)) :
    Measurable (pairRay Gamma pi defaultRay) := by
  apply hpointRay.comp
  have hmid :
      Continuous fun z : Euclidean n × Euclidean n =>
        AffineMap.lineMap z.1 z.2 (⅟2 : Real) :=
    continuous_fst.lineMap continuous_snd continuous_const
  simpa only [midpoint] using hmid.measurable

/-- The fixed Borel maximal-ray theorem supplies a measurable assignment
and measurable total point and pair labels for every chosen default ray. -/
theorem borelMaximalRayLabels
    (n : Nat)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hNoCrossing : NoCrossing Gamma)
    (defaultRay : OrientedOpenRay n) :
    MeasurableSet (transportSet Gamma) ∧
      ∃ pi : transportSet Gamma → OrientedOpenRay n,
        Measurable pi ∧
          IsMaximalRayAssignment Gamma pi ∧
          Measurable (pointRay Gamma pi defaultRay) ∧
          Measurable (pairRay Gamma pi defaultRay) := by
  obtain ⟨hTransport, pi, hpiMeasurable, hpi⟩ :=
    borelMaximalRayMap n Gamma hSigma hDiagonal hNoCrossing
  refine ⟨hTransport, pi, hpiMeasurable, hpi, ?_, ?_⟩
  · exact measurable_pointRay hTransport pi hpiMeasurable defaultRay
  · exact measurable_pairRay pi defaultRay
      (measurable_pointRay hTransport pi hpiMeasurable defaultRay)

/-- Pointwise label compatibility for a supported nondegenerate pair whose
source is itself a transport point. -/
theorem pairRay_eq_pointRay_fst_of_mem {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hxTransport : x ∈ transportSet Gamma) :
    pairRay Gamma pi defaultRay (x, y) =
      pointRay Gamma pi defaultRay x := by
  have hmOpen :
      midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  have hmne : midpoint Real x y ≠ y := by
    intro hm
    rw [hm] at hmOpen
    exact hne (right_mem_openSegment_iff.mp hmOpen)
  have hassignment :
      pi ⟨midpoint Real x y,
          midpoint_mem_transportSet hxy hne⟩ =
        pi ⟨x, hxTransport⟩ :=
    maximalRayAssignment_eq_of_mem_transportSegment
      hNoCrossing pi hpi hxy hne
      (midpoint_mem_transportSet hxy hne) hxTransport
      (openSegment_subset_segment Real x y hmOpen) hmne
      (left_mem_segment Real x y) hne
  rw [pairRay_of_mem pi defaultRay hxy hne,
    pointRay_of_mem pi defaultRay hxTransport]
  exact hassignment

/-- Every coupling supported on `Gamma` has midpoint-pair label equal almost
everywhere to the total label of its source, provided left endpoints outside
the transport set are source-negligible. -/
theorem pairRay_eq_pointRay_fst_ae_of_leftEndpointNegligible
    {n : Nat}
    {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hNoCrossing : NoCrossing Gamma)
    (hLeftEndpointNegligible :
      (mu : Measure (Euclidean n))
        (leftTransportSet Gamma \ transportSet Gamma) = 0)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    pairRay Gamma pi defaultRay =ᵐ[(gamma.plan :
      Measure (Euclidean n × Euclidean n))]
        fun z => pointRay Gamma pi defaultRay z.1 := by
  have hSourceGood :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ leftTransportSet Gamma → x ∈ transportSet Gamma := by
    have hNotBad :
        ∀ᵐ x ∂(mu : Measure (Euclidean n)),
          x ∉ leftTransportSet Gamma \ transportSet Gamma :=
      measure_eq_zero_iff_ae_notMem.mp hLeftEndpointNegligible
    filter_upwards [hNotBad] with x hx
    intro hxLeft
    by_contra hxTransport
    exact hx ⟨hxLeft, hxTransport⟩
  have hTargetTrivial :
      ∀ᵐ _y ∂(nu : Measure (Euclidean n)), True := by
    simp
  have hSourcePlan :
      ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)),
        z.1 ∈ leftTransportSet Gamma →
          z.1 ∈ transportSet Gamma :=
    (finiteCouplingMarginalAeTransfer
      gamma hSourceGood hTargetTrivial).1
  filter_upwards [hSupported, hSourcePlan] with z hzGamma hzSource
  have hne : z.1 ≠ z.2 := by
    intro hEq
    have hzPair : z = (z.1, z.1) := by
      apply Prod.ext
      · rfl
      · exact hEq.symm
    rw [hzPair] at hzGamma
    exact hDiagonal z.1 hzGamma
  have hxLeft : z.1 ∈ leftTransportSet Gamma :=
    fst_mem_leftTransportSet hzGamma hne
  exact pairRay_eq_pointRay_fst_of_mem
    hNoCrossing pi hpi defaultRay hzGamma hne (hzSource hxLeft)

/-- The preceding a.e. identity specialized to the regularity package used
by paper Theorem 2. -/
theorem pairRay_eq_pointRay_fst_ae
    {n : Nat}
    {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma → OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    pairRay Gamma pi defaultRay =ᵐ[(gamma.plan :
      Measure (Euclidean n × Euclidean n))]
        fun z => pointRay Gamma pi defaultRay z.1 :=
  pairRay_eq_pointRay_fst_ae_of_leftEndpointNegligible
    hDiagonal hRegularity.noCrossing
    hRegularity.leftEndpointNegligible
    pi hpi defaultRay gamma hSupported

/-- Complete ray-label bridge for paper Theorem 2: the Borel maximal-ray
map yields measurable total labels, and their pair/source compatibility
holds for every coupling supported on `Gamma`. -/
theorem borelMaximalRayLabels_with_ae_compatibility
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (defaultRay : OrientedOpenRay n) :
    MeasurableSet (transportSet Gamma) ∧
      ∃ pi : transportSet Gamma → OrientedOpenRay n,
        Measurable pi ∧
          IsMaximalRayAssignment Gamma pi ∧
          Measurable (pointRay Gamma pi defaultRay) ∧
          Measurable (pairRay Gamma pi defaultRay) ∧
          ∀ gamma : FiniteCoupling mu nu,
            IsSupported gamma Gamma →
              pairRay Gamma pi defaultRay =ᵐ[(gamma.plan :
                Measure (Euclidean n × Euclidean n))]
                  fun z => pointRay Gamma pi defaultRay z.1 := by
  obtain
      ⟨hTransport, pi, hpiMeasurable, hpi, hpointMeasurable,
        hpairMeasurable⟩ :=
    borelMaximalRayLabels n Gamma hSigma hDiagonal
      hRegularity.noCrossing defaultRay
  refine
    ⟨hTransport, pi, hpiMeasurable, hpi,
      hpointMeasurable, hpairMeasurable, ?_⟩
  intro gamma hSupported
  exact pairRay_eq_pointRay_fst_ae
    hDiagonal hRegularity pi hpi defaultRay gamma hSupported

end RayLabelGeometry

end ConcaveOTLimit
