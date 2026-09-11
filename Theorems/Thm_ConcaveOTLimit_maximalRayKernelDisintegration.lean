import Theorems.Thm_ConcaveOTLimit_rayLabelGeometry
import Theorems.Thm_ConcaveOTLimit_labeledCouplingDisintegration
import Theorems.Thm_ConcaveOTLimit_orientedOpenRayStandardBorel
import Theorems.Thm_ConcaveOTLimit_kernelDisintegration
import Theorems.Thm_ConcaveOTLimit_kernelDisintegrationUniqueness

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

private theorem source_mem_transportSet_ae_of_package
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
          Euclidean n × Euclidean n → Euclidean n)
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)) =
        (mu : Measure (Euclidean n)) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (Euclidean n) =>
        (eta : Measure (Euclidean n))) gamma.property.1
  have hMapped :
      ∀ᵐ x ∂Measure.map (Prod.fst :
          Euclidean n × Euclidean n → Euclidean n)
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)),
        x ∈ transportSet Gamma :=
    (ae_map_iff measurable_fst.aemeasurable hTransport).2 hPlanTransport
  rwa [hmarginal] at hMapped

private theorem exists_supported_pair_of_positiveMass
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hPositive : 0 < mu.mass)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∃ z : Euclidean n × Euclidean n, z ∈ Gamma := by
  have hmarginal :
      Measure.map (Prod.fst :
          Euclidean n × Euclidean n → Euclidean n)
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)) =
        (mu : Measure (Euclidean n)) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (Euclidean n) =>
        (eta : Measure (Euclidean n))) gamma.property.1
  have hmuUniv : (mu : Measure (Euclidean n)) univ ≠ 0 := by
    rw [← FiniteMeasure.ennreal_mass]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hPositive)
  have hplanUniv :
      (gamma.plan :
        Measure (Euclidean n × Euclidean n)) univ ≠ 0 := by
    have huniv :
        (gamma.plan :
            Measure (Euclidean n × Euclidean n)) univ =
          (mu : Measure (Euclidean n)) univ := by
      calc
        (gamma.plan :
            Measure (Euclidean n × Euclidean n)) univ =
            Measure.map (Prod.fst :
              Euclidean n × Euclidean n → Euclidean n)
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) univ := by
              rw [Measure.map_apply measurable_fst MeasurableSet.univ]
              simp
        _ = (mu : Measure (Euclidean n)) univ := by rw [hmarginal]
    rw [huniv]
    exact hmuUniv
  have hSupported' :
      ∀ᵐ z ∂(gamma.plan :
          Measure (Euclidean n × Euclidean n)).restrict univ,
        z ∈ Gamma := by
    simpa using hSupported
  obtain ⟨z, _hzUniv, hzGamma⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hplanUniv hSupported'
  exact ⟨z, hzGamma⟩

/-- A concrete measurable maximal-ray labeling, with the source-fullness and
universal supported-coupling compatibility needed by the kernel package. -/
structure MaximalRayKernelDisintegration
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n)) where
  defaultRay : OrientedOpenRay n
  transportSet_measurable : MeasurableSet (transportSet Gamma)
  rayAssignment : transportSet Gamma → OrientedOpenRay n
  rayAssignment_measurable : Measurable rayAssignment
  diagonalFree : ∀ x, (x, x) ∉ Gamma
  noCrossing : NoCrossing Gamma
  rayAssignment_isMaximal :
    IsMaximalRayAssignment Gamma rayAssignment
  pointRay_measurable :
    Measurable
      (RayLabelGeometry.pointRay Gamma rayAssignment defaultRay)
  pairRay_measurable :
    Measurable
      (RayLabelGeometry.pairRay Gamma rayAssignment defaultRay)
  label_compatibility :
    ∀ gamma : FiniteCoupling mu nu,
      IsSupported gamma Gamma →
        RayLabelGeometry.pairRay Gamma rayAssignment defaultRay
          =ᵐ[(gamma.plan :
            Measure (Euclidean n × Euclidean n))]
          fun z =>
            RayLabelGeometry.pointRay Gamma rayAssignment defaultRay z.1
  source_mem_transportSet :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      x ∈ transportSet Gamma

namespace MaximalRayKernelDisintegration

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

/-- The selected total measurable label of source points. -/
def pointRay
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    Euclidean n → OrientedOpenRay n :=
  RayLabelGeometry.pointRay Gamma D.rayAssignment D.defaultRay

/-- The selected total measurable midpoint label of source-target pairs. -/
def pairRay
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    Euclidean n × Euclidean n → OrientedOpenRay n :=
  RayLabelGeometry.pairRay Gamma D.rayAssignment D.defaultRay

/-- The common finite base measure of all supported coupling components. -/
noncomputable def sigma
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    FiniteMeasure (OrientedOpenRay n) :=
  mu.map (pointRay D)

/-- The canonical AP9.1 source disintegration over maximal-ray labels. -/
noncomputable def source
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  ap91Disintegration (pointRay D) (mu : Measure (Euclidean n))

/-- The pair-labeled AP9.1 component of a finite coupling. -/
noncomputable def component
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n) :=
  labeledCouplingComponent (pairRay D) gamma

theorem measurable_pointRay
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    Measurable (pointRay D) :=
  D.pointRay_measurable

theorem measurable_pairRay
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    Measurable (pairRay D) :=
  D.pairRay_measurable

@[simp]
theorem sigma_toMeasure
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    (sigma D : Measure (OrientedOpenRay n)) =
      Measure.map (pointRay D) (mu : Measure (Euclidean n)) :=
  rfl

theorem source_isMarkovKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    IsMarkovKernel (source D) := by
  simpa only [source] using
    ap91Disintegration_isMarkovKernel
      (pointRay D) (mu : Measure (Euclidean n))

theorem component_isMarkovKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    IsMarkovKernel (component D gamma) := by
  simpa only [component] using
    labeledCouplingComponent_isMarkovKernel (pairRay D) gamma

theorem pairRay_eq_pointRay_fst_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    pairRay D =ᵐ[(gamma.plan :
      Measure (Euclidean n × Euclidean n))]
        fun z => pointRay D z.1 :=
  D.label_compatibility gamma hSupported

/-- Every supported coupling has the source-label pushforward `sigma`. -/
theorem component_commonBase
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    gamma.plan.map (pairRay D) = sigma D := by
  simpa only [sigma] using
    labeledCoupling_source_commonBase gamma
      (pairRay D) (pointRay D) (measurable_pointRay D)
      (pairRay_eq_pointRay_fst_ae D gamma hSupported)

theorem component_commonBase_measure
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    Measure.map (pairRay D)
        (gamma.plan : Measure (Euclidean n × Euclidean n)) =
      (sigma D : Measure (OrientedOpenRay n)) := by
  simpa only [FiniteMeasure.toMeasure_map] using congrArg
    (fun eta : FiniteMeasure (OrientedOpenRay n) =>
      (eta : Measure (OrientedOpenRay n)))
    (component_commonBase D gamma hSupported)

theorem source_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    source D ∘ₘ (sigma D : Measure (OrientedOpenRay n)) =
      (mu : Measure (Euclidean n)) := by
  simpa only [source, sigma, FiniteMeasure.toMeasure_map] using
    ap91_reconstruction (pointRay D)
      (mu : Measure (Euclidean n)) (measurable_pointRay D)

/-- Every supported coupling is reconstructed from its pair components over
the same source-determined base `sigma`. -/
theorem component_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    component D gamma
        ∘ₘ (sigma D : Measure (OrientedOpenRay n)) =
      (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
  simpa only [component, sigma, FiniteMeasure.toMeasure_map] using
    labeledCouplingComponent_reconstruction_source gamma
      (pairRay D) (pointRay D) (measurable_pairRay D)
      (measurable_pointRay D)
      (pairRay_eq_pointRay_fst_ae D gamma hSupported)

theorem component_map_fst_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    (component D gamma).map Prod.fst
        ∘ₘ (sigma D : Measure (OrientedOpenRay n)) =
      (mu : Measure (Euclidean n)) := by
  simpa only [component, sigma, FiniteMeasure.toMeasure_map] using
    labeledCouplingComponent_source_reconstruction gamma
      (pairRay D) (pointRay D) (measurable_pairRay D)
      (measurable_pointRay D)
      (pairRay_eq_pointRay_fst_ae D gamma hSupported)

/-- The second marginal of each individual component kernel reconstructs
`nu`; no coupling-independent target kernel is asserted. -/
theorem component_map_snd_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    (component D gamma).map Prod.snd
        ∘ₘ (sigma D : Measure (OrientedOpenRay n)) =
      (nu : Measure (Euclidean n)) := by
  calc
    (component D gamma).map Prod.snd
          ∘ₘ (sigma D : Measure (OrientedOpenRay n)) =
        (component D gamma
          ∘ₘ (sigma D : Measure (OrientedOpenRay n))).map Prod.snd :=
      (Measure.map_comp _ _ measurable_snd).symm
    _ = Measure.map Prod.snd
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)) := by
      rw [component_reconstruction D gamma hSupported]
    _ = (nu : Measure (Euclidean n)) := by
      simpa [secondMarginal, FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure (Euclidean n) =>
          (eta : Measure (Euclidean n))) gamma.property.2

/-- The first marginal kernel of every supported coupling component is the
canonical source kernel over `sigma`. -/
theorem component_map_fst_ae_eq_source
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    (component D gamma).map Prod.fst
      =ᵐ[(sigma D : Measure (OrientedOpenRay n))]
        source D := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  simpa only [component, source, sigma, FiniteMeasure.toMeasure_map] using
    labeledCouplingComponent_map_fst_ae_eq gamma
      (pairRay D) (pointRay D) (measurable_pairRay D)
      (measurable_pointRay D)
      (pairRay_eq_pointRay_fst_ae D gamma hSupported)

/-- Almost every canonical source conditional is carried by its literal
point-label fiber. -/
theorem source_ae_fiber_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ x ∂source D R, pointRay D x = R := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  simpa only [source, sigma, FiniteMeasure.toMeasure_map] using
    ap91_ae_fiber_eq (pointRay D)
      (mu : Measure (Euclidean n)) (measurable_pointRay D)

theorem source_fiber_concentration
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      source D R ((pointRay D) ⁻¹' {R}) = 1 := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  simpa only [source, sigma, FiniteMeasure.toMeasure_map] using
    ap91_fiber_concentration (pointRay D)
      (mu : Measure (Euclidean n)) (measurable_pointRay D)

/-- Almost every pair component is carried by its literal midpoint-label
fiber, after rebasing from the pair pushforward to `sigma`. -/
theorem component_ae_fiber_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂component D gamma R, pairRay D z = R := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  have hFiber :=
    ap91_ae_fiber_eq (pairRay D)
      (gamma.plan : Measure (Euclidean n × Euclidean n))
      (measurable_pairRay D)
  rw [component_commonBase_measure D gamma hSupported] at hFiber
  simpa only [component] using hFiber

theorem component_fiber_concentration
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      component D gamma R ((pairRay D) ⁻¹' {R}) = 1 := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  have hFiber :=
    ap91_fiber_concentration (pairRay D)
      (gamma.plan : Measure (Euclidean n × Euclidean n))
      (measurable_pairRay D)
  rw [component_commonBase_measure D gamma hSupported] at hFiber
  simpa only [component] using hFiber

theorem pointRay_isMaximal_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      (pointRay D x).IsMaximalTransportRay Gamma := by
  filter_upwards [D.source_mem_transportSet] with x hx
  rw [pointRay, RayLabelGeometry.pointRay_of_mem
    D.rayAssignment D.defaultRay hx]
  exact (D.rayAssignment_isMaximal ⟨x, hx⟩).1

theorem point_mem_pointRay_carrier_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      x ∈ (pointRay D x).carrier := by
  filter_upwards [D.source_mem_transportSet] with x hx
  rw [pointRay, RayLabelGeometry.pointRay_of_mem
    D.rayAssignment D.defaultRay hx]
  exact (D.rayAssignment_isMaximal ⟨x, hx⟩).2

/-- Canonical source fibers live on the carriers of their indexing maximal
rays. -/
theorem source_on_ray_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ x ∂source D R, x ∈ R.carrier := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel (source D) := source_isMarkovKernel D
  have hIndexed :
      ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
        ∀ᵐ x ∂source D R, x ∈ (pointRay D x).carrier := by
    apply Measure.ae_ae_of_ae_comp
    rw [source_reconstruction D]
    exact point_mem_pointRay_carrier_ae D
  filter_upwards [hIndexed, source_ae_fiber_eq D] with R hmem hlabel
  filter_upwards [hmem, hlabel] with x hx hxl
  simpa only [hxl] using hx

/-- The source-determined base is concentrated on maximal transport rays. -/
theorem ray_isMaximal_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      R.IsMaximalTransportRay Gamma := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel (source D) := source_isMarkovKernel D
  have hIndexed :
      ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
        ∀ᵐ x ∂source D R,
          (pointRay D x).IsMaximalTransportRay Gamma := by
    apply Measure.ae_ae_of_ae_comp
    rw [source_reconstruction D]
    exact pointRay_isMaximal_ae D
  have hAtRay :
      ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
        ∀ᵐ _x ∂source D R,
          R.IsMaximalTransportRay Gamma := by
    filter_upwards [hIndexed, source_ae_fiber_eq D] with R hmax hlabel
    filter_upwards [hmax, hlabel] with x hx hxl
    simpa only [hxl] using hx
  filter_upwards [hAtRay] with R hR
  have hprob :
      IsProbabilityMeasure (source D R) :=
    (source_isMarkovKernel D).isProbabilityMeasure R
  have hnonzero : source D R univ ≠ 0 := by
    rw [hprob.measure_univ]
    exact one_ne_zero
  have hR' :
      ∀ᵐ _x ∂(source D R).restrict univ,
        R.IsMaximalTransportRay Gamma := by
    simpa only [Measure.restrict_univ] using hR
  obtain ⟨_x, _hxUniv, hxMaximal⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := source D R) (s := univ) hnonzero hR'
  exact hxMaximal

/-- Globally, a supported pair is labeled by a maximal ray whose closure
contains both endpoints. -/
theorem pairRay_geometry_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)),
      (pairRay D z).IsMaximalTransportRay Gamma ∧
        z.1 ∈ closure (pairRay D z).carrier ∧
        z.2 ∈ closure (pairRay D z).carrier := by
  filter_upwards [hSupported] with z hzGamma
  rcases z with ⟨x, y⟩
  have hne : x ≠ y := by
    intro hxy
    subst y
    exact D.diagonalFree x hzGamma
  have hm :
      midpoint Real x y ∈ transportSet Gamma :=
    midpoint_mem_transportSet hzGamma hne
  have hlabel :
      pairRay D (x, y) =
        D.rayAssignment ⟨midpoint Real x y, hm⟩ := by
    exact RayLabelGeometry.pairRay_of_mem
      D.rayAssignment D.defaultRay hzGamma hne
  rw [hlabel]
  exact
    ⟨(D.rayAssignment_isMaximal
        ⟨midpoint Real x y, hm⟩).1,
      RayLabelGeometry.pair_endpoints_mem_closure_assignedMidpointRay
        D.noCrossing D.rayAssignment
        D.rayAssignment_isMaximal hzGamma hne⟩

/-- Almost every conditional component pair has both endpoints in the
closure of its indexing maximal ray. -/
theorem component_endpoints_mem_closure_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂component D gamma R,
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel (component D gamma) :=
    component_isMarkovKernel D gamma
  have hIndexed :
      ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂component D gamma R,
          (pairRay D z).IsMaximalTransportRay Gamma ∧
            z.1 ∈ closure (pairRay D z).carrier ∧
            z.2 ∈ closure (pairRay D z).carrier := by
    apply Measure.ae_ae_of_ae_comp
    rw [component_reconstruction D gamma hSupported]
    exact pairRay_geometry_ae D gamma hSupported
  filter_upwards
      [hIndexed, component_ae_fiber_eq D gamma hSupported] with
      R hgeometry hlabel
  filter_upwards [hgeometry, hlabel] with z hz hzl
  simpa only [hzl] using hz.2

theorem component_on_maximalRay_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(sigma D : Measure (OrientedOpenRay n)),
      R.IsMaximalTransportRay Gamma ∧
        ∀ᵐ z ∂component D gamma R,
          z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier := by
  filter_upwards
      [ray_isMaximal_ae D,
        component_endpoints_mem_closure_ae
          D gamma hSupported] with R hmax hendpoints
  exact ⟨hmax, hendpoints⟩

end MaximalRayKernelDisintegration

/-- Paper-Theorem-2 inputs produce a concrete maximal-ray kernel
disintegration. Positive source mass is used only to choose a default
nondegenerate ray; all supported couplings then use the same labels and
source base. -/
theorem existsMaximalRayKernelDisintegration
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hInput :
      ∃ gamma : FiniteCoupling mu nu,
        IsSupported gamma Gamma) :
    Nonempty
      (MaximalRayKernelDisintegration n mu nu Gamma) := by
  obtain ⟨gamma0, hgamma0⟩ := hInput
  obtain ⟨⟨x, y⟩, hxyGamma⟩ :=
    exists_supported_pair_of_positiveMass
      hMarginals.positiveMass gamma0 hgamma0
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hDiagonal x hxyGamma
  let defaultRay : OrientedOpenRay n :=
    RayLabelGeometry.transportSegmentRay x y hxy
  obtain
      ⟨hTransport, pi, hpiMeasurable, hpi, hpointMeasurable,
        hpairMeasurable, hcompatibility⟩ :=
    RayLabelGeometry.borelMaximalRayLabels_with_ae_compatibility
      n mu nu Gamma hSigma hDiagonal hRegularity defaultRay
  have hSourceTransport :
      ∀ᵐ z ∂(mu : Measure (Euclidean n)),
        z ∈ transportSet Gamma :=
    source_mem_transportSet_ae_of_package hTransport hDiagonal
      hRegularity.leftEndpointNegligible gamma0 hgamma0
  exact
    ⟨{
      defaultRay := defaultRay
      transportSet_measurable := hTransport
      rayAssignment := pi
      rayAssignment_measurable := hpiMeasurable
      diagonalFree := hDiagonal
      noCrossing := hRegularity.noCrossing
      rayAssignment_isMaximal := hpi
      pointRay_measurable := hpointMeasurable
      pairRay_measurable := hpairMeasurable
      label_compatibility := hcompatibility
      source_mem_transportSet := hSourceTransport
    }⟩

end ConcaveOTLimit
