import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementAssembly
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## The joint label-coordinate law -/

/-- The scalar coordinate of a point along the ray selected by its label. -/
def rayCoordinateAlongLabel
    {n : Nat}
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (x : Euclidean n) : Real :=
  rayCoordinate (pointLabel x) x

set_option maxHeartbeats 400000 in
theorem measurable_rayCoordinateAlongLabel
    {n : Nat}
    {pointLabel : Euclidean n -> OrientedOpenRay n}
    (hpointLabel : Measurable pointLabel) :
    Measurable (rayCoordinateAlongLabel pointLabel) := by
  let pair : Euclidean n -> OrientedOpenRay n × Euclidean n :=
    fun x => (pointLabel x, x)
  have hpair : Measurable pair :=
    hpointLabel.prodMk measurable_id
  exact measurable_rayCoordinate_uncurry.comp hpair

/-- Absolute continuity of the joint label-coordinate law with respect to
the label marginal times one-dimensional Lebesgue measure. This is an
explicit product-law formulation of the missing coarea input. -/
def RayCoordinateProductAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) : Prop :=
  Measure.map
      (fun x =>
        (pointLabel x, rayCoordinateAlongLabel pointLabel x))
      (mu : Measure (Euclidean n)) ≪
    (Measure.map pointLabel (mu : Measure (Euclidean n))).prod
      (volume : Measure Real)

/-- Absolute continuity of almost every canonical ray-coordinate
conditional with respect to one-dimensional Lebesgue measure. -/
def RayConditionalCoordinateAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) : Prop :=
  ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
    Measure.map (rayCoordinate R)
        (canonicalRaySourceKernel mu pointLabel R) ≪
      (volume : Measure Real)

/-- The exact atomlessness conclusion consumed by the raywise replacement
assembly, stated for a general measurable ray label. -/
def RayConditionalCoordinateAtomless
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) : Prop :=
  ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
    IsAtomlessFinite
      ((canonicalRaySourceConditional mu pointLabel R).map
        (rayCoordinate R))

/-- On almost every label fiber, pushing the canonical conditional through
the fixed ray coordinate agrees with conditioning the joint
label-coordinate random variable. -/
theorem canonicalRayCoordinateMeasure_eq_condDistrib
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel) :
    ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
      Measure.map (rayCoordinate R)
          (canonicalRaySourceKernel mu pointLabel R) =
        condDistrib (rayCoordinateAlongLabel pointLabel) pointLabel
          (mu : Measure (Euclidean n)) R := by
  letI : Nonempty (OrientedOpenRay n) := ⟨pointLabel 0⟩
  have hcoordinate :
      Measurable (rayCoordinateAlongLabel pointLabel) :=
    measurable_rayCoordinateAlongLabel hpointLabel
  have hcomp :
      condDistrib (rayCoordinateAlongLabel pointLabel) pointLabel
          (mu : Measure (Euclidean n)) =ᵐ[
            Measure.map pointLabel (mu : Measure (Euclidean n))]
        (canonicalRaySourceKernel mu pointLabel).map
          (rayCoordinateAlongLabel pointLabel) := by
    simpa only [canonicalRaySourceKernel, ap91Disintegration,
      Function.comp_id] using
      (condDistrib_comp
        (μ := (mu : Measure (Euclidean n)))
        (Y := (id : Euclidean n -> Euclidean n))
        pointLabel measurable_id.aemeasurable hcoordinate)
  have hfiber :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂canonicalRaySourceKernel mu pointLabel R,
          pointLabel x = R := by
    simpa only [canonicalRaySourceKernel] using
      ap91_ae_fiber_eq pointLabel
        (mu : Measure (Euclidean n)) hpointLabel
  filter_upwards [hcomp, hfiber] with R hcompR hfiberR
  calc
    Measure.map (rayCoordinate R)
        (canonicalRaySourceKernel mu pointLabel R) =
        Measure.map (rayCoordinateAlongLabel pointLabel)
          (canonicalRaySourceKernel mu pointLabel R) := by
      apply Measure.map_congr
      filter_upwards [hfiberR] with x hx
      simp only [rayCoordinateAlongLabel, hx]
    _ = ((canonicalRaySourceKernel mu pointLabel).map
          (rayCoordinateAlongLabel pointLabel)) R :=
      (Kernel.map_apply _ hcoordinate R).symm
    _ = condDistrib (rayCoordinateAlongLabel pointLabel) pointLabel
          (mu : Measure (Euclidean n)) R :=
      hcompR.symm

/-- Joint product absolute continuity disintegrates to absolute continuity
of almost every scalar coordinate conditional. The finite equivalent
`volume.toFinite` is used only because `kernel_of_compProd` requires a
finite comparison kernel. -/
theorem rayConditionalCoordinateAC_of_coordinateProductAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (hProduct : RayCoordinateProductAC mu pointLabel) :
    RayConditionalCoordinateAC mu pointLabel := by
  let coordinate := rayCoordinateAlongLabel pointLabel
  have hcoordinate : Measurable coordinate :=
    measurable_rayCoordinateAlongLabel hpointLabel
  have hProductFinite :
      Measure.map (fun x => (pointLabel x, coordinate x))
          (mu : Measure (Euclidean n)) ≪
        (Measure.map pointLabel (mu : Measure (Euclidean n))).prod
          (volume : Measure Real).toFinite := by
    apply hProduct.trans
    exact Measure.AbsolutelyContinuous.rfl.prod
      (absolutelyContinuous_toFinite (volume : Measure Real))
  have hCompProd :
      Measure.map pointLabel (mu : Measure (Euclidean n)) ⊗ₘ
          condDistrib coordinate pointLabel
            (mu : Measure (Euclidean n)) ≪
        Measure.map pointLabel (mu : Measure (Euclidean n)) ⊗ₘ
          Kernel.const (OrientedOpenRay n)
            (volume : Measure Real).toFinite := by
    rw [compProd_map_condDistrib hcoordinate.aemeasurable,
      Measure.compProd_const]
    exact hProductFinite
  have hConditionalFinite :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        condDistrib coordinate pointLabel
            (mu : Measure (Euclidean n)) R ≪
          (volume : Measure Real).toFinite := by
    simpa only [Kernel.const_apply] using
      hCompProd.kernel_of_compProd
  have hConditional :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        condDistrib coordinate pointLabel
            (mu : Measure (Euclidean n)) R ≪
          (volume : Measure Real) := by
    filter_upwards [hConditionalFinite] with R hR
    exact hR.trans
      (toFinite_absolutelyContinuous (volume : Measure Real))
  have hCoordinateEq :=
    canonicalRayCoordinateMeasure_eq_condDistrib
      mu pointLabel hpointLabel
  filter_upwards [hConditional, hCoordinateEq] with R hR hEq
  rw [hEq]
  exact hR

/-- Lebesgue absolute continuity immediately supplies the exact
atomlessness property used by the one-dimensional assembly. -/
theorem rayConditionalCoordinateAtomless_of_coordinateAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hCoordinate :
      RayConditionalCoordinateAC mu pointLabel) :
    RayConditionalCoordinateAtomless mu pointLabel := by
  filter_upwards [hCoordinate] with R hR
  intro t
  change
    Measure.map (rayCoordinate R)
      (canonicalRaySourceKernel mu pointLabel R) {t} = 0
  exact hR (by simp)

theorem rayConditionalCoordinateAtomless_of_coordinateProductAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (hProduct : RayCoordinateProductAC mu pointLabel) :
    RayConditionalCoordinateAtomless mu pointLabel :=
  rayConditionalCoordinateAtomless_of_coordinateAC mu pointLabel
    (rayConditionalCoordinateAC_of_coordinateProductAC
      mu pointLabel hpointLabel hProduct)

theorem rayConditionalCoordinateAtomless_of_hausdorffAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hCarrier :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂canonicalRaySourceKernel mu pointLabel R,
          x ∈ R.carrier)
    (hHausdorff :
      RayConditionalHausdorffAC mu pointLabel) :
    RayConditionalCoordinateAtomless mu pointLabel := by
  filter_upwards [hCarrier, hHausdorff] with
      R hRCarrier hRHausdorff
  have hRAtomless :
      IsAtomlessFinite
        (canonicalRaySourceConditional mu pointLabel R) := by
    apply isAtomlessFinite_of_absolutelyContinuous_hausdorff
    simpa only [canonicalRaySourceConditional_toMeasure] using
      hRHausdorff
  exact isAtomlessFinite_map_of_injOn_ae
    (canonicalRaySourceConditional mu pointLabel R)
    (rayCoordinate R) (measurable_rayCoordinate R)
    R.carrier (by
      simpa only [canonicalRaySourceConditional_toMeasure] using
        hRCarrier)
    (rayCoordinate_injOn_carrier R) hRAtomless

/-! ## Mapping coordinate absolute continuity back to a ray -/

theorem orientedOpenRay_point_isometry
    {n : Nat} (R : OrientedOpenRay n) :
    Isometry R.point := by
  apply Isometry.of_dist_eq
  intro s t
  simp only [OrientedOpenRay.point, dist_eq_norm,
    add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul]
  have hnorm : ‖R.direction‖ = 1 := by
    simpa only [OrientedOpenRay.direction] using R.property.1
  rw [hnorm, mul_one]

/-- A measure carried by one ray is Hausdorff-absolutely-continuous as soon
as its scalar coordinate pushforward is Lebesgue-absolutely-continuous. -/
theorem absolutelyContinuous_hausdorffMeasure_one_of_coordinate
    {n : Nat} (R : OrientedOpenRay n)
    (eta : Measure (Euclidean n))
    (hCarrier :
      ∀ᵐ x ∂eta, x ∈ R.carrier)
    (hCoordinate :
      Measure.map (rayCoordinate R) eta ≪
        (volume : Measure Real)) :
    eta ≪ Measure.hausdorffMeasure 1 := by
  have hFixed :
      (R.point ∘ rayCoordinate R) =ᵐ[eta]
        (id : Euclidean n -> Euclidean n) := by
    filter_upwards [hCarrier] with x hx
    obtain ⟨t, _htLower, _htUpper, rfl⟩ := hx
    change R.point (rayCoordinate R (R.point t)) = R.point t
    rw [rayCoordinate_point_apply]
  have hMapBack :
      eta =
        (Measure.map (rayCoordinate R) eta).map R.point := by
    calc
      eta = Measure.map id eta := Measure.map_id.symm
      _ = Measure.map (R.point ∘ rayCoordinate R) eta :=
        Measure.map_congr hFixed.symm
      _ = (Measure.map (rayCoordinate R) eta).map R.point :=
        (Measure.map_map
          (OrientedOpenRay.measurable_point R)
          (measurable_rayCoordinate R)).symm
  have hReference :
      (volume : Measure Real).map R.point ≪
        Measure.hausdorffMeasure 1 := by
    rw [← hausdorffMeasure_real,
      (orientedOpenRay_point_isometry R).map_hausdorffMeasure
        (Or.inl zero_le_one)]
    exact Measure.absolutelyContinuous_restrict
  rw [hMapBack]
  exact
    (hCoordinate.map (OrientedOpenRay.measurable_point R)).trans
      hReference

/-- Coordinate absolute continuity plus canonical carrier concentration
recovers the original Hausdorff-absolute-continuity coarea conclusion. -/
theorem rayConditionalHausdorffAC_of_coordinateAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hCarrier :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂canonicalRaySourceKernel mu pointLabel R,
          x ∈ R.carrier)
    (hCoordinate :
      RayConditionalCoordinateAC mu pointLabel) :
    RayConditionalHausdorffAC mu pointLabel := by
  filter_upwards [hCarrier, hCoordinate] with R hRCarrier hRCoordinate
  exact absolutelyContinuous_hausdorffMeasure_one_of_coordinate
    R (canonicalRaySourceKernel mu pointLabel R)
    hRCarrier hRCoordinate

theorem rayConditionalHausdorffAC_of_coordinateProductAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (hCarrier :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂canonicalRaySourceKernel mu pointLabel R,
          x ∈ R.carrier)
    (hProduct : RayCoordinateProductAC mu pointLabel) :
    RayConditionalHausdorffAC mu pointLabel :=
  rayConditionalHausdorffAC_of_coordinateAC mu pointLabel hCarrier
    (rayConditionalCoordinateAC_of_coordinateProductAC
      mu pointLabel hpointLabel hProduct)

/-! ## Geometric boundary formulations -/

/-- Membership in one of the compact regularity pieces implies membership
in the open transport set. -/
theorem mem_transportSet_of_mem_compactPiece
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    {x : Euclidean n}
    (hx : ∃ k, x ∈ hRegularity.compactPiece k) :
    x ∈ transportSet Gamma := by
  obtain ⟨k, hxk⟩ := hx
  have hxUnion :
      x ∈ iUnion hRegularity.compactPiece :=
    mem_iUnion_of_mem k hxk
  rw [hRegularity.compactPieceCover] at hxUnion
  exact hxUnion.1

/-- Full source mass on the regularity pieces and maximality of the label
put almost every canonical conditional on its labeled ray carrier. -/
theorem canonicalRaySource_carrier_ae_of_compactPieces
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (hpointLabel :
      Measurable
        (RayLabelGeometry.pointRay Gamma pi defaultRay))
    (hCompact :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∃ k, x ∈ hRegularity.compactPiece k) :
    ∀ᵐ R ∂Measure.map
        (RayLabelGeometry.pointRay Gamma pi defaultRay)
        (mu : Measure (Euclidean n)),
      ∀ᵐ x ∂canonicalRaySourceKernel mu
          (RayLabelGeometry.pointRay Gamma pi defaultRay) R,
        x ∈ R.carrier := by
  letI : Nonempty (OrientedOpenRay n) := ⟨defaultRay⟩
  let pointLabel : Euclidean n -> OrientedOpenRay n :=
    RayLabelGeometry.pointRay Gamma pi defaultRay
  have hSourceCarrier :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ (pointLabel x).carrier := by
    filter_upwards [hCompact] with x hx
    have hxTransport :
        x ∈ transportSet Gamma :=
      mem_transportSet_of_mem_compactPiece hRegularity hx
    change
      x ∈
        (RayLabelGeometry.pointRay Gamma pi defaultRay x).carrier
    rw [RayLabelGeometry.pointRay_of_mem pi defaultRay hxTransport]
    exact (hpi ⟨x, hxTransport⟩).2
  simpa only [canonicalRaySourceKernel] using
    ap91_ae_mem_indexed_fiber pointLabel
      (mu : Measure (Euclidean n)) hpointLabel
      (fun R => R.carrier) hSourceCarrier

/-- Geometric producer boundary with an explicit joint-product conclusion.
Proving this proposition is precisely the codimension-one coarea step. -/
def CountablyLipschitzRayCoordinateProductPremise
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n) : Prop :=
  IsMaximalRayAssignment Gamma pi ->
    Measurable (RayLabelGeometry.pointRay Gamma pi defaultRay) ->
      (mu : Measure (Euclidean n)) ≪ volume ->
        (∀ᵐ x ∂(mu : Measure (Euclidean n)),
          ∃ k, x ∈ hRegularity.compactPiece k) ->
          RayCoordinateProductAC mu
            (RayLabelGeometry.pointRay Gamma pi defaultRay)

/-- Weakest application-facing boundary: it asks only for coordinate
atomlessness of the canonical conditionals, exactly as consumed downstream. -/
def CountablyLipschitzRayCoordinateAtomlessPremise
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n) : Prop :=
  IsMaximalRayAssignment Gamma pi ->
    Measurable (RayLabelGeometry.pointRay Gamma pi defaultRay) ->
      (mu : Measure (Euclidean n)) ≪ volume ->
        (∀ᵐ x ∂(mu : Measure (Euclidean n)),
          ∃ k, x ∈ hRegularity.compactPiece k) ->
          RayConditionalCoordinateAtomless mu
            (RayLabelGeometry.pointRay Gamma pi defaultRay)

/-- The explicit joint-product coarea boundary implies the existing
Hausdorff-conditional coarea boundary. -/
theorem countablyLipschitzRayCoareaPremise_of_coordinateProduct
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    (hProduct :
      CountablyLipschitzRayCoordinateProductPremise
        mu Gamma hRegularity pi defaultRay) :
    CountablyLipschitzRayCoareaPremise
      mu Gamma hRegularity pi defaultRay := by
  intro hpi hpointLabel hmuAC hCompact
  have hCarrier :=
    canonicalRaySource_carrier_ae_of_compactPieces
      hRegularity pi hpi defaultRay hpointLabel hCompact
  exact rayConditionalHausdorffAC_of_coordinateProductAC
    mu (RayLabelGeometry.pointRay Gamma pi defaultRay)
    hpointLabel hCarrier
    (hProduct hpi hpointLabel hmuAC hCompact)

/-- The existing Hausdorff boundary implies the weaker atomlessness
boundary once the already-proved carrier concentration is supplied. -/
theorem coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity pi defaultRay) :
    CountablyLipschitzRayCoordinateAtomlessPremise
      mu Gamma hRegularity pi defaultRay := by
  intro hpi hpointLabel hmuAC hCompact
  have hCarrier :=
    canonicalRaySource_carrier_ae_of_compactPieces
      hRegularity pi hpi defaultRay hpointLabel hCompact
  exact rayConditionalCoordinateAtomless_of_hausdorffAC
    mu (RayLabelGeometry.pointRay Gamma pi defaultRay)
    hCarrier (hCoarea hpi hpointLabel hmuAC hCompact)

theorem coordinateAtomlessPremise_of_coordinateProduct
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    (hProduct :
      CountablyLipschitzRayCoordinateProductPremise
        mu Gamma hRegularity pi defaultRay) :
    CountablyLipschitzRayCoordinateAtomlessPremise
      mu Gamma hRegularity pi defaultRay := by
  intro hpi hpointLabel hmuAC hCompact
  exact rayConditionalCoordinateAtomless_of_coordinateProductAC
    mu (RayLabelGeometry.pointRay Gamma pi defaultRay)
    hpointLabel (hProduct hpi hpointLabel hmuAC hCompact)

/-! ## Application and maximal-ray adapters -/

/-- The weak coordinate-atomlessness boundary is sufficient for the exact
conclusion of `rayConditionalAtomlessness_of_countablyLipschitzCoarea`. -/
theorem rayConditionalAtomlessness_of_coordinateAtomlessPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hTransportMeasurable :
      MeasurableSet (transportSet Gamma))
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpiMeasurable : Measurable pi)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity pi defaultRay) :
    RayConditionalCoordinateAtomless mu
      (RayLabelGeometry.pointRay Gamma pi defaultRay) := by
  have hpointLabel :
      Measurable
        (RayLabelGeometry.pointRay Gamma pi defaultRay) :=
    RayLabelGeometry.measurable_pointRay
      hTransportMeasurable pi hpiMeasurable defaultRay
  have hSourceTransport :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ transportSet Gamma :=
    source_mem_transportSet_ae hTransportMeasurable hDiagonal
      hRegularity.leftEndpointNegligible gamma hSupported
  have hSourceCompact :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∃ k, x ∈ hRegularity.compactPiece k :=
    source_mem_compactPiece_ae hRegularity hSourceTransport
  exact hAtomless hpi hpointLabel hmuAC hSourceCompact

theorem maximalRaySource_coordinateAtomless_of_conditional
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hAtomless :
      RayConditionalCoordinateAtomless mu D.pointRay) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsAtomlessFinite
        ((maximalRaySourceFiber D R).map
          (rayCoordinate R)) := by
  simpa [RayConditionalCoordinateAtomless,
    MaximalRayKernelDisintegration.sigma,
    MaximalRayKernelDisintegration.pointRay,
    MaximalRayKernelDisintegration.source,
    maximalRaySourceFiber,
    canonicalRaySourceConditional,
    canonicalRaySourceKernel] using hAtomless

theorem maximalRaySource_coordinateAtomless_of_coordinateProductAC
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hProduct : RayCoordinateProductAC mu D.pointRay) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsAtomlessFinite
        ((maximalRaySourceFiber D R).map
          (rayCoordinate R)) := by
  apply maximalRaySource_coordinateAtomless_of_conditional D
  exact rayConditionalCoordinateAtomless_of_coordinateProductAC
    mu D.pointRay D.measurable_pointRay hProduct

theorem maximalRaySource_coordinateAtomless_of_weakPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsAtomlessFinite
        ((maximalRaySourceFiber D R).map
          (rayCoordinate R)) := by
  apply maximalRaySource_coordinateAtomless_of_conditional D
  exact rayConditionalAtomlessness_of_coordinateAtomlessPremise
    D.transportSet_measurable D.diagonalFree hRegularity
    D.rayAssignment D.rayAssignment_measurable
    D.rayAssignment_isMaximal D.defaultRay gamma hSupported
    hmuAC hAtomless

theorem maximalRaySource_coordinateAtomless_of_coordinateProductPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hProduct :
      CountablyLipschitzRayCoordinateProductPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsAtomlessFinite
        ((maximalRaySourceFiber D R).map
          (rayCoordinate R)) := by
  exact maximalRaySource_coordinateAtomless_of_weakPremise
    D hRegularity gamma hSupported hmuAC
    (coordinateAtomlessPremise_of_coordinateProduct
      mu Gamma hRegularity D.rayAssignment D.defaultRay hProduct)

end ConcaveOTLimit
