import Theorems.Thm_ConcaveOTLimit_labeledCouplingDisintegration
import Theorems.Thm_ConcaveOTLimit_rayLabelGeometry
import Mathlib.MeasureTheory.Measure.Hausdorff

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Generic absolute-continuity and atomlessness adapters -/

/-- Absolute continuity transfers across almost-everywhere equality of
kernel fibers. This is the final uniqueness step in the AP 9.4 argument. -/
theorem ap94_absoluteContinuity_transfer
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    {sigma : Measure R} {kappa eta : Kernel R X}
    {reference : R -> Measure X}
    (hkappa : kappa =ᵐ[sigma] eta)
    (heta : ∀ᵐ r ∂sigma, eta r ≪ reference r) :
    ∀ᵐ r ∂sigma, kappa r ≪ reference r := by
  filter_upwards [hkappa, heta] with r hr hac
  simpa [hr] using hac

/-- Absolute continuity with respect to a measure without atoms preserves
nullity of singleton sets. -/
theorem noAtoms_of_absolutelyContinuous
    {X : Type*} [MeasurableSpace X]
    {mu reference : Measure X} [NoAtoms reference]
    (hmu : mu ≪ reference) :
    NoAtoms mu :=
  ⟨fun x => hmu (measure_singleton x)⟩

/-- A finite measure absolutely continuous with respect to positive
dimensional Hausdorff measure has no point masses. -/
theorem isAtomlessFinite_of_absolutelyContinuous_hausdorff
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : FiniteMeasure X)
    (hmu :
      (mu : Measure X) ≪ Measure.hausdorffMeasure 1) :
    IsAtomlessFinite mu := by
  letI : NoAtoms (Measure.hausdorffMeasure 1 : Measure X) :=
    Measure.noAtoms_hausdorff X zero_lt_one
  letI : NoAtoms (mu : Measure X) :=
    noAtoms_of_absolutelyContinuous hmu
  exact fun x => measure_singleton x

/-- A measurable pushforward of an atomless finite measure is atomless when
the map is injective on a full-measure set. -/
theorem isAtomlessFinite_map_of_injOn_ae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (mu : FiniteMeasure X) (f : X -> Y) (hf : Measurable f)
    (s : Set X) (hs : ∀ᵐ x ∂(mu : Measure X), x ∈ s)
    (hinjective : Set.InjOn f s)
    (hmu : IsAtomlessFinite mu) :
    IsAtomlessFinite (mu.map f) := by
  intro y
  change Measure.map f (mu : Measure X) {y} = 0
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  by_cases hexists : ∃ x, x ∈ s ∧ f x = y
  · obtain ⟨x0, hx0s, hx0f⟩ := hexists
    have hpreimage :
        ∀ᵐ x ∂(mu : Measure X),
          x ∈ f ⁻¹' ({y} : Set Y) ↔ x ∈ ({x0} : Set X) := by
      filter_upwards [hs] with x hxs
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hxf
        apply hinjective hxs hx0s
        exact hxf.trans hx0f.symm
      · intro hxx0
        simpa [hxx0] using hx0f
    have hpreimageEq :
        (f ⁻¹' ({y} : Set Y) : Set X) =ᵐ[(mu : Measure X)]
          ({x0} : Set X) :=
      hpreimage.mono fun _ hx => propext hx
    rw [measure_congr hpreimageEq, hmu x0]
  · have hpreimage :
        ∀ᵐ x ∂(mu : Measure X),
          x ∈ f ⁻¹' ({y} : Set Y) ↔ x ∈ (∅ : Set X) := by
      filter_upwards [hs] with x hxs
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hxf
      exact hexists ⟨x, hxs, hxf⟩
    have hpreimageEq :
        (f ⁻¹' ({y} : Set Y) : Set X) =ᵐ[(mu : Measure X)]
          (∅ : Set X) :=
      hpreimage.mono fun _ hx => propext hx
    rw [measure_congr hpreimageEq, measure_empty]

/-! ## Canonical source disintegration and uniqueness -/

/-- The canonical source disintegration along a total ray label. -/
noncomputable def canonicalRaySourceKernel
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  ap91Disintegration pointLabel (mu : Measure (Euclidean n))

/-- Every canonical source conditional is bundled as a finite measure. -/
noncomputable def canonicalRaySourceConditional
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (R : OrientedOpenRay n) :
    FiniteMeasure (Euclidean n) := by
  letI : IsMarkovKernel (canonicalRaySourceKernel mu pointLabel) := by
    simpa only [canonicalRaySourceKernel] using
      ap91Disintegration_isMarkovKernel pointLabel
        (mu : Measure (Euclidean n))
  exact ⟨canonicalRaySourceKernel mu pointLabel R, inferInstance⟩

@[simp]
theorem canonicalRaySourceConditional_toMeasure
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (R : OrientedOpenRay n) :
    (canonicalRaySourceConditional mu pointLabel R :
        Measure (Euclidean n)) =
      canonicalRaySourceKernel mu pointLabel R :=
  rfl

theorem canonicalRaySourceKernel_isMarkovKernel
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) :
    IsMarkovKernel (canonicalRaySourceKernel mu pointLabel) := by
  simpa only [canonicalRaySourceKernel] using
    ap91Disintegration_isMarkovKernel pointLabel
      (mu : Measure (Euclidean n))

/-- Same-base reconstruction and concentration on the same label fibers
identify any finite reference disintegration with the canonical one. -/
theorem canonicalRaySourceKernel_ae_eq_of_reconstruction
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (eta : Kernel (OrientedOpenRay n) (Euclidean n))
    [IsFiniteKernel eta]
    (hreconstruct :
      eta ∘ₘ Measure.map pointLabel
          (mu : Measure (Euclidean n)) =
        (mu : Measure (Euclidean n)))
    (hetaFiber :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂eta R, pointLabel x = R) :
    eta =ᵐ[Measure.map pointLabel (mu : Measure (Euclidean n))]
      canonicalRaySourceKernel mu pointLabel := by
  letI : Nonempty (OrientedOpenRay n) := ⟨pointLabel 0⟩
  letI : IsMarkovKernel (canonicalRaySourceKernel mu pointLabel) :=
    canonicalRaySourceKernel_isMarkovKernel mu pointLabel
  apply ap92_same_base_unique pointLabel hpointLabel
  · exact hreconstruct.trans
      (ap91_reconstruction pointLabel
        (mu : Measure (Euclidean n)) hpointLabel).symm
  · exact hetaFiber
  · simpa only [canonicalRaySourceKernel] using
      ap91_ae_fiber_eq pointLabel
        (mu : Measure (Euclidean n)) hpointLabel

/-- A Hausdorff-absolutely-continuous reference disintegration transfers
that property to the canonical source disintegration by uniqueness. -/
theorem canonicalRaySourceKernel_hausdorffAC_of_reference
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (eta : Kernel (OrientedOpenRay n) (Euclidean n))
    [IsFiniteKernel eta]
    (hreconstruct :
      eta ∘ₘ Measure.map pointLabel
          (mu : Measure (Euclidean n)) =
        (mu : Measure (Euclidean n)))
    (hetaFiber :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂eta R, pointLabel x = R)
    (hetaAC :
      ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
        eta R ≪ Measure.hausdorffMeasure 1) :
    ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
      canonicalRaySourceKernel mu pointLabel R ≪
        Measure.hausdorffMeasure 1 := by
  letI : Nonempty (OrientedOpenRay n) := ⟨pointLabel 0⟩
  exact ap94_absoluteContinuity_transfer
    (canonicalRaySourceKernel_ae_eq_of_reconstruction
      mu pointLabel hpointLabel eta hreconstruct hetaFiber).symm
    hetaAC

/-- A source property indexed by its own label disintegrates into the
corresponding indexed property on almost every canonical fiber. -/
theorem ap91_ae_mem_indexed_fiber
    {X R : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]
    (pointLabel : X -> R) (lambda : Measure X)
    [IsFiniteMeasure lambda] (hpointLabel : Measurable pointLabel)
    (s : R -> Set X)
    (hmem : ∀ᵐ x ∂lambda, x ∈ s (pointLabel x)) :
    ∀ᵐ r ∂lambda.map pointLabel,
      ∀ᵐ x ∂ap91Disintegration pointLabel lambda r, x ∈ s r := by
  have hIndexed :
      ∀ᵐ r ∂lambda.map pointLabel,
        ∀ᵐ x ∂ap91Disintegration pointLabel lambda r,
          x ∈ s (pointLabel x) := by
    apply Measure.ae_ae_of_ae_comp
    rw [ap91_reconstruction pointLabel lambda hpointLabel]
    exact hmem
  filter_upwards
      [hIndexed, ap91_ae_fiber_eq pointLabel lambda hpointLabel] with
      r hr hlabel
  filter_upwards [hr, hlabel] with x hx hxl
  simpa only [hxl] using hx

/-! ## Transporting the regularity package to an absolutely continuous source -/

namespace RayRegularityHypotheses

/-- Null-set fields in the ray regularity package pass from a reference
measure to every absolutely continuous measure. All geometric data and
compact Lipschitz pieces are unchanged. -/
def of_absolutelyContinuous
    {n : Nat} {rho lambda : Measure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity : RayRegularityHypotheses rho Gamma)
    (hlambda : lambda ≪ rho) :
    RayRegularityHypotheses lambda Gamma where
  noCrossing := hRegularity.noCrossing
  directionField := hRegularity.directionField
  directionAgrees := hRegularity.directionAgrees
  leftEndpointNegligible :=
    hlambda hRegularity.leftEndpointNegligible
  exceptional := hRegularity.exceptional
  exceptionalNegligible :=
    hlambda hRegularity.exceptionalNegligible
  exceptionalSubset := hRegularity.exceptionalSubset
  compactPiece := hRegularity.compactPiece
  compactPieceMonotone := hRegularity.compactPieceMonotone
  compactPieceIsCompact := hRegularity.compactPieceIsCompact
  compactPieceCover := hRegularity.compactPieceCover
  directionLipschitz := hRegularity.directionLipschitz

@[simp]
theorem of_absolutelyContinuous_directionField
    {n : Nat} {rho lambda : Measure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity : RayRegularityHypotheses rho Gamma)
    (hlambda : lambda ≪ rho) :
    (hRegularity.of_absolutelyContinuous hlambda).directionField =
      hRegularity.directionField :=
  rfl

@[simp]
theorem of_absolutelyContinuous_compactPiece
    {n : Nat} {rho lambda : Measure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity : RayRegularityHypotheses rho Gamma)
    (hlambda : lambda ≪ rho) :
    (hRegularity.of_absolutelyContinuous hlambda).compactPiece =
      hRegularity.compactPiece :=
  rfl

end RayRegularityHypotheses

/-! ## Source mass on the countably Lipschitz ray exhaustion -/

/-- A source marginal of a coupling carried by a non-diagonal transport
support lies in the open transport set almost everywhere. -/
theorem source_mem_transportSet_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hTransport : MeasurableSet (transportSet Gamma))
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hLeftEndpointNegligible :
      (mu : Measure (Euclidean n))
        (leftTransportSet Gamma \ transportSet Gamma) = 0)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      x ∈ transportSet Gamma := by
  have hSourceGood :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ leftTransportSet Gamma -> x ∈ transportSet Gamma := by
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
        z.1 ∈ leftTransportSet Gamma ->
          z.1 ∈ transportSet Gamma :=
    (finiteCouplingMarginalAeTransfer
      gamma hSourceGood hTargetTrivial).1
  have hPlanTransport :
      ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)),
        z.1 ∈ transportSet Gamma := by
    filter_upwards [hSupported, hSourcePlan] with z hzGamma hzSource
    have hne : z.1 ≠ z.2 := by
      intro heq
      have hpair : z = (z.1, z.1) := by
        apply Prod.ext
        · rfl
        · exact heq.symm
      exact hDiagonal z.1 (hpair ▸ hzGamma)
    exact hzSource (fst_mem_leftTransportSet hzGamma hne)
  have hmarginal :
      Measure.map (Prod.fst :
          Euclidean n × Euclidean n -> Euclidean n)
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)) =
        (mu : Measure (Euclidean n)) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (Euclidean n) =>
        (eta : Measure (Euclidean n))) gamma.property.1
  have hMapped :
      ∀ᵐ x ∂Measure.map (Prod.fst :
          Euclidean n × Euclidean n -> Euclidean n)
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)),
        x ∈ transportSet Gamma :=
    (ae_map_iff measurable_fst.aemeasurable hTransport).2
      hPlanTransport
  rwa [hmarginal] at hMapped

/-- The regularity package's compact pieces cover the source marginal
almost everywhere. Each such piece carries the supplied Lipschitz direction
bound. -/
theorem source_mem_compactPiece_ae
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hTransport :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ transportSet Gamma) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      ∃ k, x ∈ hRegularity.compactPiece k := by
  have hNotExceptional :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∉ hRegularity.exceptional :=
    measure_eq_zero_iff_ae_notMem.mp
      hRegularity.exceptionalNegligible
  filter_upwards [hTransport, hNotExceptional] with x hxT hxN
  have hxUnion :
      x ∈ iUnion hRegularity.compactPiece := by
    rw [hRegularity.compactPieceCover]
    exact ⟨hxT, hxN⟩
  exact mem_iUnion.mp hxUnion

/-! ## The maximal-ray label has the supplied Lipschitz direction -/

/-- On the transport set, the direction of the assigned maximal ray is the
regularity package's canonical direction field. -/
theorem pointRay_direction_eq_directionField_of_mem
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    {x : Euclidean n} (hx : x ∈ transportSet Gamma) :
    (RayLabelGeometry.pointRay Gamma pi defaultRay x).direction =
      hRegularity.directionField x := by
  rw [RayLabelGeometry.pointRay_of_mem pi defaultRay hx]
  obtain ⟨a, b, hab, _hne, hxab, hdir⟩ :=
    (hpi ⟨x, hx⟩).1.1 x (hpi ⟨x, hx⟩).2
  exact hdir.symm.trans
    (hRegularity.directionAgrees x hx a b hab hxab).symm

/-- Consequently, the direction read from the measurable maximal-ray label
is Lipschitz on every compact piece in the regularity exhaustion. -/
theorem pointRay_direction_lipschitzOn_compactPiece
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (k : Nat) :
    ∃ L : NNReal,
      LipschitzOnWith L
        (fun x =>
          (RayLabelGeometry.pointRay
            Gamma pi defaultRay x).direction)
        (hRegularity.compactPiece k) := by
  obtain ⟨L, hL⟩ := hRegularity.directionLipschitz k
  refine ⟨L, ?_⟩
  intro x hx y hy
  have hxT : x ∈ transportSet Gamma := by
    have hxUnion :
        x ∈ iUnion hRegularity.compactPiece :=
      mem_iUnion_of_mem k hx
    rw [hRegularity.compactPieceCover] at hxUnion
    exact hxUnion.1
  have hyT : y ∈ transportSet Gamma := by
    have hyUnion :
        y ∈ iUnion hRegularity.compactPiece :=
      mem_iUnion_of_mem k hy
    rw [hRegularity.compactPieceCover] at hyUnion
    exact hyUnion.1
  change
    edist
        (RayLabelGeometry.pointRay
          Gamma pi defaultRay x).direction
        (RayLabelGeometry.pointRay
          Gamma pi defaultRay y).direction ≤
      (L : ENNReal) * edist x y
  rw [pointRay_direction_eq_directionField_of_mem
      hRegularity pi hpi defaultRay hxT,
    pointRay_direction_eq_directionField_of_mem
      hRegularity pi hpi defaultRay hyT]
  exact hL hx hy

/-- Distinct maximal open transport-ray carriers are disjoint. This is the
partition condition used by the transport-ray coarea theorem. -/
theorem disjoint_maximalRay_carriers_of_ne
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    {R S : OrientedOpenRay n}
    (hR : R.IsMaximalTransportRay Gamma)
    (hS : S.IsMaximalTransportRay Gamma)
    (hne : R ≠ S) :
    Disjoint R.carrier S.carrier := by
  rw [Set.disjoint_left]
  intro x hxR hxS
  obtain ⟨a, b, hab, hane, hxab, hdirR⟩ :=
    hR.1 x hxR
  have hxT : x ∈ transportSet Gamma :=
    ⟨(a, b), hab, hane, hxab⟩
  obtain ⟨c, d, hcd, _hcne, hxcd, hdirS⟩ :=
    hS.1 x hxS
  have hRfield :
      R.direction = hRegularity.directionField x :=
    hdirR.symm.trans
      (hRegularity.directionAgrees x hxT a b hab hxab).symm
  have hSfield :
      S.direction = hRegularity.directionField x :=
    hdirS.symm.trans
      (hRegularity.directionAgrees x hxT c d hcd hxcd).symm
  exact hne
    (RayLabelGeometry.maximalRay_eq_of_common_carrier_point
      hR hS (hRfield.trans hSfield.symm) hxR hxS)

/-! ## Ray-coordinate injectivity -/

theorem rayCoordinate_point_apply
    {n : Nat} (R : OrientedOpenRay n) (t : Real) :
    rayCoordinate R (R.point t) = t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  unfold rayCoordinate OrientedOpenRay.point
  rw [add_sub_cancel_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hnorm]
  norm_num

/-- Ray coordinates are injective on the carrier of one oriented ray. -/
theorem rayCoordinate_injOn_carrier
    {n : Nat} (R : OrientedOpenRay n) :
    Set.InjOn (rayCoordinate R) R.carrier := by
  intro x hx y hy hxy
  obtain ⟨s, _hsl, _hsu, rfl⟩ := hx
  obtain ⟨t, _htl, _htu, rfl⟩ := hy
  have hst : s = t := by
    simpa only [rayCoordinate_point_apply] using hxy
  rw [hst]

/-! ## The coarea boundary and its atomlessness consequence -/

/-- The exact Hausdorff absolute-continuity conclusion needed from
codimension-one coarea for the canonical source disintegration. -/
def RayConditionalHausdorffAC
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) : Prop :=
  ∀ᵐ R ∂Measure.map pointLabel (mu : Measure (Euclidean n)),
    canonicalRaySourceKernel mu pointLabel R ≪
      Measure.hausdorffMeasure 1

/-- Public boundary for the missing AP 9.4 coarea theorem, specialized to
the existing regularity package and maximal-ray labels. All premises before
the final Hausdorff-AC conclusion are discharged below in the application. -/
def CountablyLipschitzRayCoareaPremise
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
          RayConditionalHausdorffAC mu
            (RayLabelGeometry.pointRay Gamma pi defaultRay)

/-- Conditional source atomlessness on maximal rays, with the sole external
analytic premise isolated as `CountablyLipschitzRayCoareaPremise`. -/
theorem rayConditionalAtomlessness_of_countablyLipschitzCoarea
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
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity pi defaultRay) :
    ∀ᵐ R ∂Measure.map
        (RayLabelGeometry.pointRay Gamma pi defaultRay)
        (mu : Measure (Euclidean n)),
      IsAtomlessFinite
        ((canonicalRaySourceConditional mu
          (RayLabelGeometry.pointRay Gamma pi defaultRay) R).map
            (rayCoordinate R)) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨defaultRay⟩
  let pointLabel : Euclidean n -> OrientedOpenRay n :=
    RayLabelGeometry.pointRay Gamma pi defaultRay
  have hpointLabel : Measurable pointLabel := by
    exact RayLabelGeometry.measurable_pointRay
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
  have hSourceCarrier :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ (pointLabel x).carrier := by
    filter_upwards [hSourceTransport] with x hx
    change x ∈
      (RayLabelGeometry.pointRay Gamma pi defaultRay x).carrier
    rw [RayLabelGeometry.pointRay_of_mem pi defaultRay hx]
    exact (hpi ⟨x, hx⟩).2
  have hConditionalCarrier :
      ∀ᵐ R ∂Measure.map pointLabel
          (mu : Measure (Euclidean n)),
        ∀ᵐ x ∂canonicalRaySourceKernel mu pointLabel R,
          x ∈ R.carrier := by
    simpa only [canonicalRaySourceKernel] using
      ap91_ae_mem_indexed_fiber pointLabel
        (mu : Measure (Euclidean n)) hpointLabel
        (fun R => R.carrier) hSourceCarrier
  have hConditionalAC :
      RayConditionalHausdorffAC mu pointLabel := by
    exact hCoarea hpi hpointLabel hmuAC hSourceCompact
  filter_upwards [hConditionalAC, hConditionalCarrier] with
      R hRAC hRCarrier
  have hRAtomless :
      IsAtomlessFinite
        (canonicalRaySourceConditional mu pointLabel R) := by
    apply isAtomlessFinite_of_absolutelyContinuous_hausdorff
    simpa only [canonicalRaySourceConditional_toMeasure] using hRAC
  exact isAtomlessFinite_map_of_injOn_ae
    (canonicalRaySourceConditional mu pointLabel R)
    (rayCoordinate R) (measurable_rayCoordinate R)
    R.carrier (by
      simpa only [canonicalRaySourceConditional_toMeasure] using
        hRCarrier)
    (rayCoordinate_injOn_carrier R) hRAtomless

/-- Version aligned with the contact-set regularity producer: regularity
proved relative to volume transfers to `mu` using `mu ≪ volume`, after which
the same coarea boundary yields conditional coordinate atomlessness. -/
theorem rayConditionalAtomlessness_of_volumeRegularity
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hTransportMeasurable :
      MeasurableSet (transportSet Gamma))
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularityVolume :
      RayRegularityHypotheses
        (volume : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpiMeasurable : Measurable pi)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma
          (hRegularityVolume.of_absolutelyContinuous hmuAC)
          pi defaultRay) :
    ∀ᵐ R ∂Measure.map
        (RayLabelGeometry.pointRay Gamma pi defaultRay)
        (mu : Measure (Euclidean n)),
      IsAtomlessFinite
        ((canonicalRaySourceConditional mu
          (RayLabelGeometry.pointRay Gamma pi defaultRay) R).map
            (rayCoordinate R)) := by
  exact rayConditionalAtomlessness_of_countablyLipschitzCoarea
    hTransportMeasurable hDiagonal
    (hRegularityVolume.of_absolutelyContinuous hmuAC)
    pi hpiMeasurable hpi defaultRay gamma hSupported hmuAC hCoarea

end ConcaveOTLimit
