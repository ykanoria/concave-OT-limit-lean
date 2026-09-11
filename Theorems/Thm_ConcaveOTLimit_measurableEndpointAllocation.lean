import Theorems.Thm_ConcaveOTLimit_maximalRayKernelDisintegration

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

namespace MaximalRayKernelDisintegration

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

/-- The finite-coordinate representative of the upper endpoint of a ray.
For a ray with infinite upper coordinate this returns `R.point 0`; the
allocation theorem below proves that the infinite case is never selected by
a supported target outside the transport set. -/
def upperEndpoint (R : OrientedOpenRay n) : Euclidean n :=
  R.point R.upper.toReal

/-- The upper-endpoint representative is a measurable function of the ray
code, including at rays with infinite upper coordinate. -/
theorem measurable_upperEndpoint :
    Measurable (upperEndpoint : OrientedOpenRay n → Euclidean n) := by
  exact OrientedOpenRay.measurable_point_uncurry.comp
    (measurable_id.prodMk OrientedOpenRay.measurable_upper.ereal_toReal)

private theorem rayCoordinate_point
    (R : OrientedOpenRay n) (t : Real) :
    rayCoordinate R (R.point t) = t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  unfold rayCoordinate OrientedOpenRay.point
  rw [add_sub_cancel_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hnorm]
  norm_num

private theorem point_rayCoordinate_eq_of_mem_closure_carrier
    (R : OrientedOpenRay n) {z : Euclidean n}
    (hz : z ∈ closure R.carrier) :
    R.point (rayCoordinate R z) = z := by
  let s : Set (Euclidean n) :=
    {w | R.point (rayCoordinate R w) = w}
  have hsClosed : IsClosed s := by
    exact isClosed_eq
      (OrientedOpenRay.continuous_point R |>.comp
        (continuous_rayCoordinate R))
      continuous_id
  have hcarrier : R.carrier ⊆ s := by
    intro w hw
    obtain ⟨t, _htl, _htu, rfl⟩ := hw
    change R.point (rayCoordinate R (R.point t)) = R.point t
    rw [rayCoordinate_point]
  exact (closure_minimal hcarrier hsClosed) hz

private theorem coordinate_bounds_of_mem_closure_carrier
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
    rw [rayCoordinate_point]
    exact ⟨htl.le, htu.le⟩
  exact (closure_minimal hcarrier hsClosed) hz

private theorem coordinate_strict_bounds_of_mem_carrier
    (R : OrientedOpenRay n) {z : Euclidean n}
    (hz : z ∈ R.carrier) :
    R.lower < (rayCoordinate R z : EReal) ∧
      (rayCoordinate R z : EReal) < R.upper := by
  obtain ⟨t, htl, htu, rfl⟩ := hz
  simpa only [rayCoordinate_point] using ⟨htl, htu⟩

private theorem rayCoordinate_add_direction
    (R : OrientedOpenRay n) (z : Euclidean n) (t : Real) :
    rayCoordinate R (z + t • R.direction) =
      rayCoordinate R z + t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  unfold rayCoordinate
  have hsub :
      z + t • R.direction - R.anchor =
        (z - R.anchor) + t • R.direction := by
    abel
  rw [hsub, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hnorm]
  ring

private theorem target_eq_source_add_norm_smul_direction
    {x y : Euclidean n}
    {R : OrientedOpenRay n}
    (hdir : R.direction = rayDirection x y) :
    y = x + ‖y - x‖ • R.direction := by
  calc
    y = x + (y - x) := by abel
    _ = x + ‖y - x‖ • NormedSpace.normalize (y - x) := by
      rw [NormedSpace.norm_smul_normalize]
    _ = x + ‖y - x‖ • R.direction := by
      rw [hdir, rayDirection]

private theorem rayCoordinate_midpoint_lt_target
    {x y : Euclidean n} (hne : x ≠ y)
    {R : OrientedOpenRay n}
    (hdir : R.direction = rayDirection x y) :
    rayCoordinate R (midpoint Real x y) < rayCoordinate R y := by
  have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hy :
      y = x + ‖y - x‖ • R.direction :=
    target_eq_source_add_norm_smul_direction hdir
  have hsub :
      y - x = ‖y - x‖ • R.direction := by
    calc
      y - x =
          ‖y - x‖ • NormedSpace.normalize (y - x) :=
        (NormedSpace.norm_smul_normalize (y - x)).symm
      _ = ‖y - x‖ • R.direction := by
        rw [hdir, rayDirection]
  have hm :
      midpoint Real x y =
        x + (⅟2 * ‖y - x‖) • R.direction := by
    calc
      midpoint Real x y = x + (⅟2 : Real) • (y - x) := by
        unfold midpoint
        rw [AffineMap.lineMap_apply_module]
        module
      _ = x + (⅟2 : Real) •
          (‖y - x‖ • R.direction) :=
        congrArg (fun z => x + (⅟2 : Real) • z) hsub
      _ = x + (⅟2 * ‖y - x‖) • R.direction := by
        rw [smul_smul]
  have hmCoordinate :=
    congrArg (rayCoordinate R) hm
  have hyCoordinate :=
    congrArg (rayCoordinate R) hy
  rw [rayCoordinate_add_direction] at hmCoordinate hyCoordinate
  have hhalf : (⅟2 : Real) < 1 := by norm_num
  have hscaled :
      (⅟2 : Real) * ‖y - x‖ < ‖y - x‖ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hhalf hnorm
  calc
    rayCoordinate R (midpoint Real x y) =
        rayCoordinate R x + (⅟2 : Real) * ‖y - x‖ :=
      hmCoordinate
    _ < rayCoordinate R x + ‖y - x‖ :=
      by
        simpa only [add_comm] using
          add_lt_add_left hscaled (rayCoordinate R x)
    _ = rayCoordinate R y := hyCoordinate.symm

private theorem rayDirection_eq_of_right_mem_openSegment
    {x y b : Euclidean n}
    (hy : y ∈ openSegment Real x b) :
    rayDirection x y = rayDirection x b := by
  rw [openSegment_eq_image'] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have hsub : x + t • (b - x) - x = t • (b - x) := by
    module
  unfold rayDirection
  rw [hsub, NormedSpace.normalize_smul_of_pos ht.1]

private theorem assignedRay_direction_eq_at_target
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hy : y ∈ transportSet Gamma) :
    (D.rayAssignment
        ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩).direction =
      (D.rayAssignment ⟨y, hy⟩).direction := by
  let R :=
    D.rayAssignment
      ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩
  let S := D.rayAssignment ⟨y, hy⟩
  have hmOpen : midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  have hmne : midpoint Real x y ≠ y := by
    intro hm
    rw [hm] at hmOpen
    exact hne (right_mem_openSegment_iff.mp hmOpen)
  have hRdir : R.direction = rayDirection x y :=
    RayLabelGeometry.assignedRay_direction_eq_of_mem_segment_ne_right
      D.noCrossing D.rayAssignment D.rayAssignment_isMaximal
      hxy hne (midpoint_mem_transportSet hxy hne)
      (openSegment_subset_segment Real x y hmOpen) hmne
  obtain ⟨a, b, hab, hane, hyab, hSab⟩ :=
    (D.rayAssignment_isMaximal ⟨y, hy⟩).1.1 y
      (D.rayAssignment_isMaximal ⟨y, hy⟩).2
  have hdirections : rayDirection x y = rayDirection a b := by
    by_contra hneDir
    have hinter :
        (segment Real x y ∩ segment Real a b).Nonempty :=
      ⟨y, right_mem_segment Real x y,
        openSegment_subset_segment Real a b hyab⟩
    rcases D.noCrossing x y a b hxy hab hne hane hneDir hinter with
      hleft | hright
    · subst a
      exact hneDir (rayDirection_eq_of_right_mem_openSegment hyab)
    · subst b
      exact hane (right_mem_openSegment_iff.mp hyab)
  exact hRdir.trans (hdirections.trans hSab)

private theorem anchors_eq_of_direction_eq_of_eq_points
    {R S : OrientedOpenRay n} {r s : Real}
    (hdir : R.direction = S.direction)
    (hpoint : R.point r = S.point s) :
    R.anchor = S.anchor := by
  have hRnorm : ‖R.direction‖ = 1 := R.property.1
  have hRorth : inner Real R.anchor R.direction = 0 := R.property.2.1
  have hSorth : inner Real S.anchor R.direction = 0 := by
    rw [hdir]
    exact S.property.2.1
  have hrs : r = s := by
    have hinner :=
      congrArg (fun z => inner Real z R.direction) hpoint
    unfold OrientedOpenRay.point at hinner
    change
      inner Real (R.anchor + r • R.direction) R.direction =
        inner Real (S.anchor + s • S.direction) R.direction at hinner
    rw [inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hRorth, hSorth, ← hdir,
      real_inner_self_eq_norm_sq, hRnorm] at hinner
    linarith
  unfold OrientedOpenRay.point at hpoint
  rw [← hdir, ← hrs] at hpoint
  exact add_right_cancel hpoint

private theorem maximalRay_eq_of_target_mem_transportSet
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hne : x ≠ y)
    (hy : y ∈ transportSet Gamma) :
    D.rayAssignment
        ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩ =
      D.rayAssignment ⟨y, hy⟩ := by
  let R :=
    D.rayAssignment
      ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩
  let S := D.rayAssignment ⟨y, hy⟩
  have hRmax : R.IsMaximalTransportRay Gamma :=
    (D.rayAssignment_isMaximal
      ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩).1
  have hSmax : S.IsMaximalTransportRay Gamma :=
    (D.rayAssignment_isMaximal ⟨y, hy⟩).1
  have hdir : R.direction = S.direction :=
    assignedRay_direction_eq_at_target D hxy hne hy
  have hyRclosure : y ∈ closure R.carrier :=
    (RayLabelGeometry.pair_endpoints_mem_closure_assignedMidpointRay
      D.noCrossing D.rayAssignment D.rayAssignment_isMaximal
      hxy hne).2
  have hyS : y ∈ S.carrier :=
    (D.rayAssignment_isMaximal ⟨y, hy⟩).2
  let r := rayCoordinate R y
  obtain ⟨s, hsLower, hsUpper, hsPoint⟩ := hyS
  have hrPoint : R.point r = y :=
    point_rayCoordinate_eq_of_mem_closure_carrier R hyRclosure
  have hanchor : R.anchor = S.anchor :=
    anchors_eq_of_direction_eq_of_eq_points hdir
      (hrPoint.trans hsPoint.symm)
  have hrs : r = s := by
    have hrsPoint : R.point r = R.point s := by
      calc
        R.point r = y := hrPoint
        _ = S.point s := hsPoint.symm
        _ = R.point s := by
          unfold OrientedOpenRay.point
          rw [hanchor, hdir]
    apply_fun rayCoordinate R at hrsPoint
    simpa only [rayCoordinate_point] using hrsPoint
  have hrBounds :
      R.lower ≤ (r : EReal) ∧ (r : EReal) ≤ R.upper :=
    coordinate_bounds_of_mem_closure_carrier R hyRclosure
  have hmOpen : midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  have hmR :
      midpoint Real x y ∈ R.carrier :=
    (D.rayAssignment_isMaximal
      ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩).2
  have hmBounds :=
    coordinate_strict_bounds_of_mem_carrier R hmR
  have hmr :
      rayCoordinate R (midpoint Real x y) < r := by
    apply rayCoordinate_midpoint_lt_target hne
    exact
      RayLabelGeometry.assignedRay_direction_eq_of_mem_segment_ne_right
        D.noCrossing D.rayAssignment D.rayAssignment_isMaximal
        hxy hne (midpoint_mem_transportSet hxy hne)
        (openSegment_subset_segment Real x y hmOpen)
        (by
          intro hm
          rw [hm] at hmOpen
          exact hne (right_mem_openSegment_iff.mp hmOpen))
  have hSR : S.lower < R.upper := by
    exact (hrs ▸ hsLower).trans_le hrBounds.2
  have hRS : R.lower < S.upper := by
    exact hmBounds.1.trans
      ((EReal.coe_lt_coe_iff.mpr hmr).trans (hrs ▸ hsUpper))
  have hmaxUpperR :
      max R.lower S.lower < R.upper :=
    max_lt R.property.2.2 hSR
  have hmaxUpperS :
      max R.lower S.lower < S.upper :=
    max_lt hRS S.property.2.2
  have hmaxMin :
      max R.lower S.lower < min R.upper S.upper :=
    lt_min hmaxUpperR hmaxUpperS
  obtain ⟨t, htLower, htUpper⟩ :=
    EReal.lt_iff_exists_real_btwn.mp hmaxMin
  have htR : R.point t ∈ R.carrier := by
    exact
      ⟨t, (le_max_left _ _).trans_lt htLower,
        htUpper.trans_le (min_le_left _ _), rfl⟩
  have htS : R.point t ∈ S.carrier := by
    refine
      ⟨t, (le_max_right _ _).trans_lt htLower,
        htUpper.trans_le (min_le_right _ _), ?_⟩
    unfold OrientedOpenRay.point
    rw [hanchor, hdir]
  exact RayLabelGeometry.maximalRay_eq_of_common_carrier_point
    hRmax hSmax hdir htR htS

private theorem carrier_subset_transportSet
    {R : OrientedOpenRay n}
    (hR : R.IsMaximalTransportRay Gamma) :
    R.carrier ⊆ transportSet Gamma := by
  intro z hz
  obtain ⟨x, y, hxy, hne, hzOpen, _hdir⟩ := hR.1 z hz
  exact ⟨(x, y), hxy, hne, hzOpen⟩

/-- A supported target that is itself an interior transport point receives
the same maximal-ray label as the source-target pair. This statement does
not assign labels to shared boundary endpoints. -/
theorem pairRay_eq_pointRay_snd_of_mem
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hy : y ∈ transportSet Gamma) :
    pairRay D (x, y) = pointRay D y := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact D.diagonalFree x hxy
  rw [pairRay, RayLabelGeometry.pairRay_of_mem
      D.rayAssignment D.defaultRay hxy hne,
    pointRay, RayLabelGeometry.pointRay_of_mem
      D.rayAssignment D.defaultRay hy]
  exact maximalRay_eq_of_target_mem_transportSet D hxy hne hy

/-- A supported target outside the open transport set is the finite upper
endpoint of its pair's oriented maximal ray. In particular, a physical
endpoint shared by several rays is allocated using the pair label, rather
than by any global point label. -/
theorem snd_eq_upperEndpoint_pairRay_of_not_mem
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ Gamma) (hy : y ∉ transportSet Gamma) :
    y = upperEndpoint (pairRay D (x, y)) := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact D.diagonalFree x hxy
  let R :=
    D.rayAssignment
      ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩
  have hpair : pairRay D (x, y) = R := by
    exact RayLabelGeometry.pairRay_of_mem
      D.rayAssignment D.defaultRay hxy hne
  have hyClosure : y ∈ closure R.carrier :=
    (RayLabelGeometry.pair_endpoints_mem_closure_assignedMidpointRay
      D.noCrossing D.rayAssignment D.rayAssignment_isMaximal
      hxy hne).2
  let t := rayCoordinate R y
  have htPoint : R.point t = y :=
    point_rayCoordinate_eq_of_mem_closure_carrier R hyClosure
  have htBounds :
      R.lower ≤ (t : EReal) ∧ (t : EReal) ≤ R.upper :=
    coordinate_bounds_of_mem_closure_carrier R hyClosure
  have hmOpen : midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  have hmR :
      midpoint Real x y ∈ R.carrier :=
    (D.rayAssignment_isMaximal
      ⟨midpoint Real x y, midpoint_mem_transportSet hxy hne⟩).2
  have hmBounds :=
    coordinate_strict_bounds_of_mem_carrier R hmR
  have hmt :
      rayCoordinate R (midpoint Real x y) < t := by
    apply rayCoordinate_midpoint_lt_target hne
    exact
      RayLabelGeometry.assignedRay_direction_eq_of_mem_segment_ne_right
        D.noCrossing D.rayAssignment D.rayAssignment_isMaximal
        hxy hne (midpoint_mem_transportSet hxy hne)
        (openSegment_subset_segment Real x y hmOpen)
        (by
          intro hm
          rw [hm] at hmOpen
          exact hne (right_mem_openSegment_iff.mp hmOpen))
  have hLowerT : R.lower < (t : EReal) :=
    hmBounds.1.trans (EReal.coe_lt_coe_iff.mpr hmt)
  have hyNotCarrier : y ∉ R.carrier := by
    intro hyR
    exact hy
      (carrier_subset_transportSet
        (D.rayAssignment_isMaximal
          ⟨midpoint Real x y,
            midpoint_mem_transportSet hxy hne⟩).1 hyR)
  have hUpperT : R.upper ≤ (t : EReal) := by
    apply le_of_not_gt
    intro htUpper
    exact hyNotCarrier ⟨t, hLowerT, htUpper, htPoint⟩
  have htUpper : (t : EReal) = R.upper :=
    le_antisymm htBounds.2 hUpperT
  rw [hpair, upperEndpoint, ← htUpper, EReal.toReal_coe]
  exact htPoint.symm

/-- Pointwise endpoint-allocation dichotomy for every supported pair. -/
theorem pair_target_allocation
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n} (hxy : (x, y) ∈ Gamma) :
    (y ∈ transportSet Gamma →
        pairRay D (x, y) = pointRay D y) ∧
      (y ∉ transportSet Gamma →
        y = upperEndpoint (pairRay D (x, y))) :=
  ⟨pairRay_eq_pointRay_snd_of_mem D hxy,
    snd_eq_upperEndpoint_pairRay_of_not_mem D hxy⟩

/-! ## Target kernels and restriction adapters -/

/-- The target marginal kernel of a pair-disintegrated supported coupling. -/
noncomputable def target
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  (component D gamma).map Prod.snd

/-- Every target marginal kernel is Markov. -/
theorem target_isMarkovKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    IsMarkovKernel (target D gamma) := by
  letI : IsMarkovKernel (component D gamma) :=
    component_isMarkovKernel D gamma
  exact Kernel.IsMarkovKernel.map (component D gamma) measurable_snd

/-- The target marginal kernel reconstructs the prescribed target measure. -/
theorem target_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    target D gamma ∘ₘ
        (sigma D : Measure (OrientedOpenRay n)) =
      (nu : Measure (Euclidean n)) := by
  simpa only [target] using
    component_map_snd_reconstruction D gamma hSupported

private theorem kernel_restrict_reconstruction
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (base : Measure R) (kappa : Kernel R X)
    [IsSFiniteKernel kappa]
    (lambda : Measure X)
    (s : Set X) (hs : MeasurableSet s)
    (hreconstruct : kappa ∘ₘ base = lambda) :
    kappa.restrict hs ∘ₘ base = lambda.restrict s := by
  ext t ht
  calc
    (kappa.restrict hs ∘ₘ base) t =
        ∫⁻ r, kappa r (t ∩ s) ∂base := by
      rw [Measure.bind_apply ht (Kernel.aemeasurable _)]
      simp_rw [Kernel.restrict_apply' kappa hs _ ht]
    _ = (kappa ∘ₘ base) (t ∩ s) := by
      rw [Measure.bind_apply (ht.inter hs) (Kernel.aemeasurable _)]
    _ = lambda (t ∩ s) := by rw [hreconstruct]
    _ = lambda.restrict s t := by
      rw [Measure.restrict_apply ht]

/-- Restricting every target conditional to the open transport set
reconstructs the corresponding restriction of `nu`. -/
theorem target_restrict_transportSet_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    (target D gamma).restrict D.transportSet_measurable ∘ₘ
        (sigma D : Measure (OrientedOpenRay n)) =
      (nu : Measure (Euclidean n)).restrict (transportSet Gamma) := by
  letI : IsMarkovKernel (target D gamma) :=
    target_isMarkovKernel D gamma
  exact kernel_restrict_reconstruction
    (sigma D : Measure (OrientedOpenRay n)) (target D gamma)
    (nu : Measure (Euclidean n)) (transportSet Gamma)
    D.transportSet_measurable
    (target_reconstruction D gamma hSupported)

/-- The pointwise allocation dichotomy holds almost everywhere in every
conditional pair component. -/
theorem component_target_allocation_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂component D gamma R,
        (z.2 ∈ transportSet Gamma →
            pairRay D z = pointRay D z.2) ∧
          (z.2 ∉ transportSet Gamma →
            z.2 = upperEndpoint (pairRay D z)) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel (component D gamma) :=
    component_isMarkovKernel D gamma
  apply Measure.ae_ae_of_ae_comp
  rw [component_reconstruction D gamma hSupported]
  filter_upwards [hSupported] with z hz
  exact pair_target_allocation D hz

/-- On the transport-set part of almost every component, the target point
has the component's ray label. -/
theorem component_target_interior_label_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂component D gamma R,
        z.2 ∈ transportSet Gamma → pointRay D z.2 = R := by
  filter_upwards
      [component_target_allocation_ae D gamma hSupported,
        component_ae_fiber_eq D gamma hSupported] with R halloc hlabel
  filter_upwards [halloc, hlabel] with z hz hzl
  intro hzTarget
  exact (hz.1 hzTarget).symm.trans hzl

/-- Outside the transport set, almost every component target is the upper
endpoint selected by that component's ray label. -/
theorem component_target_endpoint_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂component D gamma R,
        z.2 ∉ transportSet Gamma → z.2 = upperEndpoint R := by
  filter_upwards
      [component_target_allocation_ae D gamma hSupported,
        component_ae_fiber_eq D gamma hSupported] with R halloc hlabel
  filter_upwards [halloc, hlabel] with z hz hzl
  intro hzTarget
  simpa only [hzl] using hz.2 hzTarget

/-- Before restriction, the target kernel has the correct ray label whenever
the sampled target belongs to the open transport set. -/
theorem target_interior_label_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ y ∂target D gamma R,
        y ∈ transportSet Gamma → pointRay D y = R := by
  filter_upwards
      [component_target_interior_label_ae
        D gamma hSupported] with R hR
  rw [target, Kernel.map_apply _ measurable_snd]
  apply
    (ae_map_iff measurable_snd.aemeasurable
      (D.transportSet_measurable.imp
        (measurableSet_eq_fun
          (measurable_pointRay D) measurable_const))).2
  simpa only using hR

/-- The restriction of the target kernel to the transport set is carried by
literal point-label fibers, so AP9.2 applies there. -/
theorem target_restrict_transportSet_ae_fiber_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ y ∂(target D gamma).restrict D.transportSet_measurable R,
        pointRay D y = R := by
  filter_upwards [target_interior_label_ae D gamma hSupported] with R hR
  rw [Kernel.restrict_apply]
  filter_upwards
      [ae_restrict_of_ae hR,
        ae_restrict_mem D.transportSet_measurable] with y hy hyTransport
  exact hy hyTransport

/-- The complementary part of every target conditional is concentrated at
the upper endpoint indexed by that ray. -/
theorem target_endpoint_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ y ∂target D gamma R,
        y ∉ transportSet Gamma → y = upperEndpoint R := by
  filter_upwards
      [component_target_endpoint_ae D gamma hSupported] with R hR
  rw [target, Kernel.map_apply _ measurable_snd]
  apply
    (ae_map_iff measurable_snd.aemeasurable
      (D.transportSet_measurable.compl.imp
        (measurableSet_eq_fun measurable_id measurable_const))).2
  simpa only using hR

/-! ## Generic endpoint completion -/

private theorem finiteMeasure_eq_of_restrict_eq_of_endpoint
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {rho eta : Measure X} [IsFiniteMeasure rho] [IsFiniteMeasure eta]
    {s : Set X} (hs : MeasurableSet s) (e : X)
    (htotal : rho univ = eta univ)
    (hrestrict : rho.restrict s = eta.restrict s)
    (hrho : ∀ᵐ x ∂rho, x ∉ s → x = e)
    (heta : ∀ᵐ x ∂eta, x ∉ s → x = e) :
    rho = eta := by
  let rhoC := rho.restrict sᶜ
  let etaC := eta.restrict sᶜ
  have hrhoC : ∀ᵐ x ∂rhoC, x = e := by
    filter_upwards
        [ae_restrict_of_ae hrho, ae_restrict_mem hs.compl] with x hx hxs
    exact hx hxs
  have hetaC : ∀ᵐ x ∂etaC, x = e := by
    filter_upwards
        [ae_restrict_of_ae heta, ae_restrict_mem hs.compl] with x hx hxs
    exact hx hxs
  have hrhoSingleton : rhoC.restrict {e} = rhoC := by
    apply Measure.restrict_eq_self_of_ae_mem
    simpa only [mem_singleton_iff] using hrhoC
  have hetaSingleton : etaC.restrict {e} = etaC := by
    apply Measure.restrict_eq_self_of_ae_mem
    simpa only [mem_singleton_iff] using hetaC
  have hrhoMass : rhoC {e} = rhoC univ := by
    calc
      rhoC {e} = rhoC.restrict {e} univ := by
        rw [Measure.restrict_apply_univ]
      _ = rhoC univ := by rw [hrhoSingleton]
  have hetaMass : etaC {e} = etaC univ := by
    calc
      etaC {e} = etaC.restrict {e} univ := by
        rw [Measure.restrict_apply_univ]
      _ = etaC univ := by rw [hetaSingleton]
  have hrhoC_dirac :
      rhoC = rhoC univ • Measure.dirac e := by
    calc
      rhoC = rhoC.restrict {e} := hrhoSingleton.symm
      _ = rhoC {e} • Measure.dirac e :=
        Measure.restrict_singleton rhoC e
      _ = rhoC univ • Measure.dirac e := by rw [hrhoMass]
  have hetaC_dirac :
      etaC = etaC univ • Measure.dirac e := by
    calc
      etaC = etaC.restrict {e} := hetaSingleton.symm
      _ = etaC {e} • Measure.dirac e :=
        Measure.restrict_singleton etaC e
      _ = etaC univ • Measure.dirac e := by rw [hetaMass]
  have hinterMass :
      rho.restrict s univ = eta.restrict s univ :=
    congrArg (fun m : Measure X => m univ) hrestrict
  have hrhoSum :
      rho.restrict s univ + rhoC univ = rho univ := by
    simpa only [rhoC, Measure.add_apply, MeasurableSet.univ] using
      congrArg (fun m : Measure X => m univ)
        (Measure.restrict_add_restrict_compl (μ := rho) hs)
  have hetaSum :
      eta.restrict s univ + etaC univ = eta univ := by
    simpa only [etaC, Measure.add_apply, MeasurableSet.univ] using
      congrArg (fun m : Measure X => m univ)
        (Measure.restrict_add_restrict_compl (μ := eta) hs)
  have hcomplementMass : rhoC univ = etaC univ := by
    apply add_right_injective_of_ne_top
      (rho.restrict s univ) (measure_ne_top (rho.restrict s) univ)
    calc
      rho.restrict s univ + rhoC univ = rho univ := hrhoSum
      _ = eta univ := htotal
      _ = eta.restrict s univ + etaC univ := hetaSum.symm
      _ = rho.restrict s univ + etaC univ := by rw [hinterMass]
  calc
    rho = rho.restrict s + rhoC :=
      (Measure.restrict_add_restrict_compl (μ := rho) hs).symm
    _ = eta.restrict s + etaC := by
      rw [hrestrict, hrhoC_dirac, hetaC_dirac, hcomplementMass]
    _ = eta :=
      Measure.restrict_add_restrict_compl (μ := eta) hs

/-- Two Markov kernels agree almost everywhere when their restrictions to a
measurable interior agree and both complementary parts are allocated to the
same measurable endpoint. The endpoint need not be a global label of the
sampled point. -/
theorem markovKernel_ae_eq_of_restrict_eq_of_endpoint
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    {base : Measure R} {kappa eta : Kernel R X}
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (s : Set X) (hs : MeasurableSet s) (endpoint : R → X)
    (hrestrict :
      kappa.restrict hs =ᵐ[base] eta.restrict hs)
    (hkappa :
      ∀ᵐ r ∂base, ∀ᵐ x ∂kappa r, x ∉ s → x = endpoint r)
    (heta :
      ∀ᵐ r ∂base, ∀ᵐ x ∂eta r, x ∉ s → x = endpoint r) :
    kappa =ᵐ[base] eta := by
  filter_upwards [hrestrict, hkappa, heta] with r hr hkr her
  haveI : IsProbabilityMeasure (kappa r) :=
    (inferInstance : IsMarkovKernel kappa).isProbabilityMeasure r
  haveI : IsProbabilityMeasure (eta r) :=
    (inferInstance : IsMarkovKernel eta).isProbabilityMeasure r
  apply finiteMeasure_eq_of_restrict_eq_of_endpoint hs (endpoint r)
  · simp only [measure_univ]
  · simpa only [Kernel.restrict_apply] using hr
  · exact hkr
  · exact her

/-! ## Canonical target identification -/

/-- AP9.2 identifies the transport-set restrictions of target kernels from
any two supported couplings. -/
theorem target_restrict_transportSet_ae_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma eta : FiniteCoupling mu nu)
    (hgamma : IsSupported gamma Gamma)
    (heta : IsSupported eta Gamma) :
    (target D gamma).restrict D.transportSet_measurable
      =ᵐ[(sigma D : Measure (OrientedOpenRay n))]
        (target D eta).restrict D.transportSet_measurable := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel (target D gamma) :=
    target_isMarkovKernel D gamma
  letI : IsMarkovKernel (target D eta) :=
    target_isMarkovKernel D eta
  apply ap92_same_base_unique (pointRay D) (measurable_pointRay D)
  · exact
      (target_restrict_transportSet_reconstruction D gamma hgamma).trans
        (target_restrict_transportSet_reconstruction D eta heta).symm
  · exact target_restrict_transportSet_ae_fiber_eq D gamma hgamma
  · exact target_restrict_transportSet_ae_fiber_eq D eta heta

/-- The complete target kernels of any two supported couplings agree almost
everywhere. Interior mass is fixed by AP9.2; all remaining mass is forced to
the indexing ray's upper endpoint. -/
theorem target_ae_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma eta : FiniteCoupling mu nu)
    (hgamma : IsSupported gamma Gamma)
    (heta : IsSupported eta Gamma) :
    target D gamma
      =ᵐ[(sigma D : Measure (OrientedOpenRay n))]
        target D eta := by
  letI : IsMarkovKernel (target D gamma) :=
    target_isMarkovKernel D gamma
  letI : IsMarkovKernel (target D eta) :=
    target_isMarkovKernel D eta
  exact markovKernel_ae_eq_of_restrict_eq_of_endpoint
    (transportSet Gamma) D.transportSet_measurable upperEndpoint
    (target_restrict_transportSet_ae_eq
      D gamma eta hgamma heta)
    (target_endpoint_ae D gamma hgamma)
    (target_endpoint_ae D eta heta)

/-- Choose one supported coupling only to select a representative of the
canonical target conditional kernel. The following theorem proves that its
almost-everywhere class is independent of this witness. -/
noncomputable def canonicalTarget
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  target D gamma0

theorem canonicalTarget_isMarkovKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu) :
    IsMarkovKernel (canonicalTarget D gamma0) :=
  target_isMarkovKernel D gamma0

/-- Every supported coupling has the canonical target marginal kernel. -/
theorem target_ae_eq_canonicalTarget
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 gamma : FiniteCoupling mu nu)
    (hgamma0 : IsSupported gamma0 Gamma)
    (hgamma : IsSupported gamma Gamma) :
    target D gamma
      =ᵐ[(sigma D : Measure (OrientedOpenRay n))]
        canonicalTarget D gamma0 :=
  target_ae_eq D gamma gamma0 hgamma hgamma0

/-- The selected canonical target kernel reconstructs `nu`. -/
theorem canonicalTarget_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu)
    (hgamma0 : IsSupported gamma0 Gamma) :
    canonicalTarget D gamma0 ∘ₘ
        (sigma D : Measure (OrientedOpenRay n)) =
      (nu : Measure (Euclidean n)) :=
  target_reconstruction D gamma0 hgamma0

/-- Different supported witnesses select the same canonical target kernel
almost everywhere. -/
theorem canonicalTarget_ae_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 gamma1 : FiniteCoupling mu nu)
    (hgamma0 : IsSupported gamma0 Gamma)
    (hgamma1 : IsSupported gamma1 Gamma) :
    canonicalTarget D gamma0
      =ᵐ[(sigma D : Measure (OrientedOpenRay n))]
        canonicalTarget D gamma1 :=
  target_ae_eq D gamma0 gamma1 hgamma0 hgamma1

end MaximalRayKernelDisintegration

end ConcaveOTLimit
