import Theorems.Thm_ConcaveOTLimit_fiberwiseKernelMinimality
import Theorems.Thm_ConcaveOTLimit_measurableEndpointAllocation

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped BoundedContinuousFunction ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-!
# Rational-gap measurable fiber improvements

This module reduces `FiberwiseImprovementSelectionPremise` to one explicit
measurable-selection interface.  The reduction uses a countable family of
positive rational gaps and patches a selected measure-valued map into the
current component with `Kernel.piecewise`.

The remaining interface is deliberately phrased in the Giry measurable
space on `Measure (X × Y)`, which is exactly the measurable space used by
`Kernel`.  No multifunction measurable-selection theorem producing such a
map is available in the pinned Mathlib revision.
-/

section RationalGap

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]

/-- A countable sequence of strictly positive gaps converging to zero. -/
def fiberRationalImprovementGap (k : Nat) : Real :=
  1 / ((k : Real) + 1)

theorem fiberRationalImprovementGap_pos (k : Nat) :
    0 < fiberRationalImprovementGap k := by
  unfold fiberRationalImprovementGap
  positivity

/-- Fibers admitting a feasible competitor which improves the current
component by at least the `k`-th positive rational gap. -/
def fiberRationalGapBadSet
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (component : Kernel R (X × Y))
    (k : Nat) : Set R :=
  {r |
    ∃ eta : Measure (X × Y),
      eta ∈ fiberCouplingSet source target carrier r ∧
        fiberMeasureCost cost r eta +
            fiberRationalImprovementGap k ≤
          fiberKernelCost cost component r}

/-- The exact output required from a measurable-selection theorem at one
rational gap.  Only values on the bad set are constrained; the selected
map may be arbitrary elsewhere because it will be patched with the current
component. -/
structure FiberwiseRationalGapSelectionData
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (component : Kernel R (X × Y))
    (k : Nat) where
  badMeasurable :
    MeasurableSet
      (fiberRationalGapBadSet source target carrier cost component k)
  selector : R -> Measure (X × Y)
  selectorMeasurable : Measurable selector
  selectorSpec :
    ∀ r ∈ fiberRationalGapBadSet
        source target carrier cost component k,
      selector r ∈ fiberCouplingSet source target carrier r ∧
        fiberMeasureCost cost r (selector r) +
            fiberRationalImprovementGap k ≤
          fiberKernelCost cost component r

/-- Weak measurable-selection premise isolated by the rational-gap
argument.  It asks for neither an argmin nor a selector shared by different
gaps. -/
def FiberwiseRationalGapMeasurableSelectionPremise
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real) : Prop :=
  ∀ (component : Kernel R (X × Y)),
    IsMarkovKernel component ->
      ∀ k : Nat,
        Nonempty
          (FiberwiseRationalGapSelectionData
            source target carrier cost component k)

namespace FiberwiseRationalGapSelectionData

variable
    {source : Kernel R X} {target : Kernel R Y}
    {carrier : Set (R × (X × Y))}
    {cost : R × (X × Y) -> Real}
    {component : Kernel R (X × Y)}
    {k : Nat}

/-- Regard the selected Giry-measurable map as a kernel.  It need not be
Markov away from the bad set. -/
def selectorKernel
    (data :
      FiberwiseRationalGapSelectionData
        source target carrier cost component k) :
    Kernel R (X × Y) where
  toFun := data.selector
  measurable' := data.selectorMeasurable

@[simp]
theorem selectorKernel_apply
    (data :
      FiberwiseRationalGapSelectionData
        source target carrier cost component k)
    (r : R) :
    data.selectorKernel r = data.selector r :=
  rfl

/-- Use the selector exactly on the measurable rational-gap bad set and
retain the current component everywhere else. -/
def replacement
    (data :
      FiberwiseRationalGapSelectionData
        source target carrier cost component k) :
    Kernel R (X × Y) := by
  classical
  exact Kernel.piecewise data.badMeasurable data.selectorKernel component

theorem replacement_apply_of_mem
    (data :
      FiberwiseRationalGapSelectionData
        source target carrier cost component k)
    {r : R}
    (hr :
      r ∈ fiberRationalGapBadSet
        source target carrier cost component k) :
    data.replacement r = data.selector r := by
  classical
  rw [replacement, Kernel.piecewise_apply, if_pos hr]
  rfl

theorem replacement_apply_of_notMem
    (data :
      FiberwiseRationalGapSelectionData
        source target carrier cost component k)
    {r : R}
    (hr :
      r ∉ fiberRationalGapBadSet
        source target carrier cost component k) :
    data.replacement r = component r := by
  classical
  rw [replacement, Kernel.piecewise_apply, if_neg hr]

theorem replacement_isMarkovKernel
    (data :
      FiberwiseRationalGapSelectionData
        source target carrier cost component k)
    (hsource : IsMarkovKernel source)
    (hcomponent : IsMarkovKernel component) :
    IsMarkovKernel data.replacement := by
  constructor
  intro r
  by_cases hr :
      r ∈ fiberRationalGapBadSet
        source target carrier cost component k
  · rw [data.replacement_apply_of_mem hr]
    have hmap := (data.selectorSpec r hr).1.1
    constructor
    calc
      data.selector r univ =
          (data.selector r).map Prod.fst univ := by
            rw [Measure.map_apply measurable_fst MeasurableSet.univ]
            simp
      _ = source r univ := by rw [hmap]
      _ = 1 := (hsource.isProbabilityMeasure r).measure_univ
  · rw [data.replacement_apply_of_notMem hr]
    exact hcomponent.isProbabilityMeasure r

end FiberwiseRationalGapSelectionData

/-- Failure of a.e. fiberwise minimality is already witnessed, frequently,
at one uniform rational gap.  This step uses only countability and the
Archimedean property; no measurability of the bad sets is needed. -/
theorem exists_frequently_fiberRationalGapBadSet_of_not_ae_minimizer
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (sigma : FiniteMeasure R)
    (component : Kernel R (X × Y))
    (hfeasible :
      ∀ᵐ r ∂(sigma : Measure R),
        component r ∈ fiberCouplingSet source target carrier r)
    (hnot :
      ¬ ∀ᵐ r ∂(sigma : Measure R),
        IsMinimizerOn
          (fiberCouplingSet source target carrier r)
          (fiberMeasureCost cost r) (component r)) :
    ∃ k : Nat,
      ∃ᵐ r ∂(sigma : Measure R),
        r ∈ fiberRationalGapBadSet
          source target carrier cost component k := by
  by_contra hnone
  have hnone' :
      ∀ k : Nat,
        ¬ ∃ᵐ r ∂(sigma : Measure R),
          r ∈ fiberRationalGapBadSet
            source target carrier cost component k := by
    simpa only [not_exists] using hnone
  have havoid :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ k : Nat,
          r ∉ fiberRationalGapBadSet
            source target carrier cost component k := by
    rw [ae_all_iff]
    intro k
    exact not_frequently.mp (hnone' k)
  apply hnot
  filter_upwards [hfeasible, havoid] with r hrFeasible hrAvoid
  refine ⟨hrFeasible, ?_⟩
  intro eta heta
  by_contra hle
  have hlt :
      fiberMeasureCost cost r eta <
        fiberMeasureCost cost r (component r) :=
    lt_of_not_ge hle
  obtain ⟨k, hk⟩ :=
    exists_nat_one_div_lt
      (sub_pos.mpr hlt)
  have hgap :
      fiberMeasureCost cost r eta +
          fiberRationalImprovementGap k ≤
        fiberKernelCost cost component r := by
    unfold fiberRationalImprovementGap fiberKernelCost
    linarith
  exact hrAvoid k ⟨eta, heta, hgap⟩

/-- All logic after measurable selection: choose one non-null rational-gap
bad set, patch its selector into the component, and obtain the replacement
required by `FiberwiseImprovementSelectionPremise`. -/
theorem fiberwiseImprovementSelectionPremise_of_rationalGapSelection
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (hsource : IsMarkovKernel source)
    (hselection :
      FiberwiseRationalGapMeasurableSelectionPremise
        source target carrier cost) :
    FiberwiseImprovementSelectionPremise
      sigma source target carrier cost := by
  intro component hcomponent hfeasible hnot
  obtain ⟨k, hkFrequently⟩ :=
    exists_frequently_fiberRationalGapBadSet_of_not_ae_minimizer
      source target carrier cost sigma component hfeasible hnot
  let data :=
    Classical.choice (hselection component hcomponent k)
  let replacement := data.replacement
  have hreplacementMarkov :
      IsMarkovKernel replacement :=
    data.replacement_isMarkovKernel hsource hcomponent
  refine
    ⟨replacement, hreplacementMarkov, ?_, ?_, ?_⟩
  · filter_upwards [hfeasible] with r hrFeasible
    by_cases hr :
        r ∈ fiberRationalGapBadSet
          source target carrier cost component k
    · rw [show replacement r = data.selector r by
        exact data.replacement_apply_of_mem hr]
      exact (data.selectorSpec r hr).1
    · rw [show replacement r = component r by
        exact data.replacement_apply_of_notMem hr]
      exact hrFeasible
  · exact Eventually.of_forall fun r => by
      by_cases hr :
          r ∈ fiberRationalGapBadSet
            source target carrier cost component k
      · change
          fiberMeasureCost cost r (replacement r) ≤
            fiberMeasureCost cost r (component r)
        rw [show replacement r = data.selector r by
          exact data.replacement_apply_of_mem hr]
        exact
          (le_add_of_nonneg_right
            (fiberRationalImprovementGap_pos k).le).trans
            (data.selectorSpec r hr).2
      · change
          fiberMeasureCost cost r (replacement r) ≤
            fiberMeasureCost cost r (component r)
        rw [show replacement r = component r by
          exact data.replacement_apply_of_notMem hr]
  · intro heq
    obtain ⟨r, hrBad, hrEq⟩ :=
      (hkFrequently.and_eventually heq).exists
    have hstrict :
        fiberKernelCost cost replacement r <
          fiberKernelCost cost component r := by
      change
        fiberMeasureCost cost r (replacement r) <
          fiberMeasureCost cost r (component r)
      rw [show replacement r = data.selector r by
        exact data.replacement_apply_of_mem hrBad]
      have hgap := (data.selectorSpec r hrBad).2
      have hgapPos := fiberRationalImprovementGap_pos k
      unfold fiberKernelCost at hgap
      linarith
    exact hstrict.ne hrEq

end RationalGap

section FixedRayCompactFibers

variable {R X : Type*}
  [MeasurableSpace R] [MeasurableSpace X]

/-- A Markov-kernel value bundled as a finite measure. -/
def markovKernelValueFiniteMeasure
    (kernel : Kernel R X) [IsMarkovKernel kernel]
    (r : R) : FiniteMeasure X :=
  ⟨kernel r, inferInstance⟩

@[simp]
theorem markovKernelValueFiniteMeasure_toMeasure
    (kernel : Kernel R X) [IsMarkovKernel kernel]
    (r : R) :
    (markovKernelValueFiniteMeasure kernel r : Measure X) = kernel r :=
  rfl

/-- The closed forward half-space in one fixed oriented ray coordinate. -/
def fixedRayForwardRelation
    {n : Nat} (R : OrientedOpenRay n) :
    Set (Euclidean n × Euclidean n) :=
  {z | rayCoordinate R z.1 ≤ rayCoordinate R z.2}

theorem isClosed_fixedRayForwardRelation
    {n : Nat} (R : OrientedOpenRay n) :
    IsClosed (fixedRayForwardRelation R) := by
  exact isClosed_le
    ((continuous_rayCoordinate R).comp continuous_fst)
    ((continuous_rayCoordinate R).comp continuous_snd)

/-- Fixed-marginal finite couplings carried by one ray's forward
half-space. -/
def fixedRayForwardFiniteCouplingSet
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n) :
    Set
      (FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R)) :=
  {gamma | IsSupported gamma (fixedRayForwardRelation R)}

/-- Every individual forward coupling fiber is compact in the inherited
weak topology. -/
theorem isCompact_fixedRayForwardFiniteCouplingSet
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n) :
    IsCompact (fixedRayForwardFiniteCouplingSet source target R) := by
  exact isCompact_finiteCouplingSupportedOnClosed
    (markovKernelValueFiniteMeasure source R)
    (markovKernelValueFiniteMeasure target R)
    (isClosed_fixedRayForwardRelation R)

/-- A bundled finite coupling in the compact fixed-ray fiber gives exactly
a measure in the kernel-level fiber coupling set. -/
theorem fixedRayForwardFiniteCoupling_plan_mem_fiberCouplingSet
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n)
    (gamma :
      FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R))
    (hgamma :
      gamma ∈ fixedRayForwardFiniteCouplingSet source target R) :
    (gamma.plan : Measure (Euclidean n × Euclidean n)) ∈
      fiberCouplingSet source target (rayForwardFiberCarrier n) R := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (Euclidean n) =>
        (eta : Measure (Euclidean n))) gamma.property.1
  · simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (Euclidean n) =>
        (eta : Measure (Euclidean n))) gamma.property.2
  · simpa [fixedRayForwardFiniteCouplingSet,
      fixedRayForwardRelation, rayForwardFiberCarrier] using hgamma

/-- Conversely, every measure in a ray-forward kernel fiber can be bundled
as a member of the compact finite-coupling fiber. -/
theorem exists_fixedRayForwardFiniteCoupling_of_mem_fiberCouplingSet
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n)
    (eta : Measure (Euclidean n × Euclidean n))
    (heta :
      eta ∈ fiberCouplingSet
        source target (rayForwardFiberCarrier n) R) :
    ∃ gamma :
        FiniteCoupling
          (markovKernelValueFiniteMeasure source R)
          (markovKernelValueFiniteMeasure target R),
      gamma ∈ fixedRayForwardFiniteCouplingSet source target R ∧
        (gamma.plan : Measure (Euclidean n × Euclidean n)) = eta := by
  have hetaProbability : IsProbabilityMeasure eta := by
    constructor
    calc
      eta univ = eta.map Prod.fst univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        simp
      _ = source R univ := by rw [heta.1]
      _ = 1 := measure_univ
  letI : IsProbabilityMeasure eta := hetaProbability
  let etaFinite : FiniteMeasure (Euclidean n × Euclidean n) :=
    ⟨eta, inferInstance⟩
  let gamma :
      FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R) :=
    ⟨etaFinite, by
      constructor
      · apply FiniteMeasure.toMeasure_injective
        simpa [firstMarginal, etaFinite] using heta.1
      · apply FiniteMeasure.toMeasure_injective
        simpa [secondMarginal, etaFinite] using heta.2.1⟩
  refine ⟨gamma, ?_, rfl⟩
  simpa [fixedRayForwardFiniteCouplingSet,
    fixedRayForwardRelation, rayForwardFiberCarrier,
    gamma, etaFinite] using heta.2.2

/-- The strict-exponential point cost on one fixed ray, bundled as a
bounded continuous function. -/
def fixedRayStrictExponentialCostBcf
    {n : Nat} (R : OrientedOpenRay n) :
    (Euclidean n × Euclidean n) →ᵇ Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => rayStrictExponentialFiberCost (R, z))
    (continuous_rayStrictExponentialFiberCost.comp
      (continuous_const.prodMk continuous_id))
    1
    (fun z => norm_rayStrictExponentialFiberCost_le_one (R, z))

@[simp]
theorem fixedRayStrictExponentialCostBcf_apply
    {n : Nat} (R : OrientedOpenRay n)
    (z : Euclidean n × Euclidean n) :
    fixedRayStrictExponentialCostBcf R z =
      rayStrictExponentialFiberCost (R, z) :=
  rfl

/-- Strict-exponential cost of a bundled coupling in one fixed ray fiber. -/
def fixedRayFiniteCouplingCost
    {n : Nat}
    {source target :
      Kernel (OrientedOpenRay n) (Euclidean n)}
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n)
    (gamma :
      FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R)) : Real :=
  ∫ z, rayStrictExponentialFiberCost (R, z)
    ∂(gamma.plan : Measure (Euclidean n × Euclidean n))

theorem continuous_fixedRayFiniteCouplingCost
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n) :
    Continuous
      (fixedRayFiniteCouplingCost
        (source := source) (target := target) R) := by
  simpa [fixedRayFiniteCouplingCost] using
    (FiniteMeasure.continuous_integral_boundedContinuousFunction
      (fixedRayStrictExponentialCostBcf R)).comp
        (continuous_subtype_val :
          Continuous
            (fun gamma :
                FiniteCoupling
                  (markovKernelValueFiniteMeasure source R)
                  (markovKernelValueFiniteMeasure target R) =>
              gamma.plan))

/-- The compact section of feasible fixed-ray couplings which improve a
specified component by one fixed rational gap. -/
def fixedRayRationalGapFiniteCouplingSet
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    Set
      (FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R)) :=
  {gamma |
    gamma ∈ fixedRayForwardFiniteCouplingSet source target R ∧
      fixedRayFiniteCouplingCost
          (source := source) (target := target) R gamma +
          fiberRationalImprovementGap k ≤
        fiberKernelCost rayStrictExponentialFiberCost component R}

/-- Rational-gap competitor sections are compact: feasibility is compact
and the cost-gap inequality is weakly closed. -/
theorem isCompact_fixedRayRationalGapFiniteCouplingSet
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    IsCompact
      (fixedRayRationalGapFiniteCouplingSet
        source target component R k) := by
  have hclosed :
      IsClosed
        {gamma :
            FiniteCoupling
              (markovKernelValueFiniteMeasure source R)
              (markovKernelValueFiniteMeasure target R) |
          fixedRayFiniteCouplingCost
              (source := source) (target := target) R gamma +
              fiberRationalImprovementGap k ≤
            fiberKernelCost
              rayStrictExponentialFiberCost component R} :=
    isClosed_le
      ((continuous_fixedRayFiniteCouplingCost source target R).add
        continuous_const)
      continuous_const
  exact
    (isCompact_fixedRayForwardFiniteCouplingSet source target R).inter_right
      hclosed

end FixedRayCompactFibers

section RaySpecialization

/-- Rational-gap selector interface for the strict-exponential forward
problem on oriented rays. -/
def RayForwardRationalGapMeasurableSelectionPremise
    {n : Nat}
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n)) : Prop :=
  FiberwiseRationalGapMeasurableSelectionPremise
    source target (rayForwardFiberCarrier n)
      rayStrictExponentialFiberCost

theorem rayForwardFiberwiseImprovementSelectionPremise_of_rationalGapSelection
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source]
    (hselection :
      RayForwardRationalGapMeasurableSelectionPremise source target) :
    RayForwardFiberwiseImprovementSelectionPremise sigma source target := by
  exact fiberwiseImprovementSelectionPremise_of_rationalGapSelection
    sigma source target (rayForwardFiberCarrier n)
      rayStrictExponentialFiberCost
      (inferInstance : IsMarkovKernel source) hselection

namespace MaximalRayKernelDisintegration

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

private theorem pairRay_coordinate_forward_of_mem_for_selection
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    {x y : Euclidean n} (hxy : (x, y) ∈ Gamma) :
    rayCoordinate (D.pairRay (x, y)) x ≤
      rayCoordinate (D.pairRay (x, y)) y := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact D.diagonalFree x hxy
  have hmOpen :
      midpoint Real x y ∈ openSegment Real x y :=
    midpoint_mem_openSegment x y
  have hmne : midpoint Real x y ≠ y := by
    intro hm
    rw [hm] at hmOpen
    exact hne (right_mem_openSegment_iff.mp hmOpen)
  have hdirection :
      (D.pairRay (x, y)).direction = rayDirection x y := by
    rw [MaximalRayKernelDisintegration.pairRay,
      RayLabelGeometry.pairRay_of_mem
        D.rayAssignment D.defaultRay hxy hne]
    exact
      RayLabelGeometry.assignedRay_direction_eq_of_mem_segment_ne_right
        D.noCrossing D.rayAssignment D.rayAssignment_isMaximal
        hxy hne (midpoint_mem_transportSet hxy hne)
        (openSegment_subset_segment Real x y hmOpen) hmne
  have hnorm : 0 < ‖y - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hinner :
      inner Real (y - x) (NormedSpace.normalize (y - x)) =
        ‖y - x‖ := by
    rw [NormedSpace.normalize, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  have hinner' :
      inner Real (y - x) (rayDirection x y) = ‖y - x‖ := by
    simpa only [rayDirection] using hinner
  have hcoordinate :
      rayCoordinate (D.pairRay (x, y)) y =
        rayCoordinate (D.pairRay (x, y)) x + ‖y - x‖ := by
    unfold rayCoordinate
    rw [hdirection]
    have hsub :
        y - (D.pairRay (x, y)).anchor =
          (x - (D.pairRay (x, y)).anchor) + (y - x) := by
      module
    rw [hsub, inner_add_left, hinner']
  rw [hcoordinate]
  exact le_add_of_nonneg_right (norm_nonneg _)

private theorem pairRay_coordinate_forward_ae_for_selection
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)),
      rayCoordinate (D.pairRay z) z.1 ≤
        rayCoordinate (D.pairRay z) z.2 := by
  filter_upwards [hSupported] with z hz
  exact pairRay_coordinate_forward_of_mem_for_selection D hz

private theorem component_coordinate_forward_ae_for_selection
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂D.component gamma R,
        rayCoordinate R z.1 ≤ rayCoordinate R z.2 := by
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  have hIndexed :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂D.component gamma R,
          rayCoordinate (D.pairRay z) z.1 ≤
            rayCoordinate (D.pairRay z) z.2 := by
    apply Measure.ae_ae_of_ae_comp
    rw [D.component_reconstruction gamma hSupported]
    exact pairRay_coordinate_forward_ae_for_selection D gamma hSupported
  filter_upwards
      [hIndexed, D.component_ae_fiber_eq gamma hSupported] with
      R hForward hLabel
  filter_upwards [hForward, hLabel] with z hz hR
  simpa only [hR] using hz

/-- The sole remaining measurable-selection interface for the canonical
source and target ray kernels. -/
def CanonicalRayForwardRationalGapMeasurableSelectionPremise
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu) : Prop :=
  RayForwardRationalGapMeasurableSelectionPremise
    D.source (D.canonicalTarget gamma0)

/-- For the canonical source and target ray kernels, rational-gap
measurable selection implies the exact downstream improvement-selection
premise. -/
theorem rayForwardFiberwiseImprovementSelectionPremise_of_canonical
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu)
    (hselection :
      CanonicalRayForwardRationalGapMeasurableSelectionPremise D gamma0) :
    RayForwardFiberwiseImprovementSelectionPremise
      D.sigma D.source (D.canonicalTarget gamma0) := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  exact
    rayForwardFiberwiseImprovementSelectionPremise_of_rationalGapSelection
      D.sigma D.source (D.canonicalTarget gamma0) hselection

/-- A supported witness supplies a feasible forward coupling in almost
every canonical source/target fiber. -/
theorem canonicalRayForwardFiberCouplingSet_nonempty_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu)
    (hgamma0 : IsSupported gamma0 Gamma) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      (fiberCouplingSet D.source (D.canonicalTarget gamma0)
        (rayForwardFiberCarrier n) R).Nonempty := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma0) :=
    D.component_isMarkovKernel gamma0
  have hsource :
      (D.component gamma0).map Prod.fst
        =ᵐ[(D.sigma : Measure (OrientedOpenRay n))] D.source :=
    D.component_map_fst_ae_eq_source gamma0 hgamma0
  have htarget :
      (D.component gamma0).map Prod.snd
        =ᵐ[(D.sigma : Measure (OrientedOpenRay n))]
          D.canonicalTarget gamma0 := by
    exact Eventually.of_forall fun _ => rfl
  have hforward :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂D.component gamma0 R,
          (R, z) ∈ rayForwardFiberCarrier n := by
    simpa [rayForwardFiberCarrier] using
      (component_coordinate_forward_ae_for_selection D gamma0 hgamma0)
  have hmem :=
    component_mem_fiberCouplingSet_ae
      D.sigma D.source (D.canonicalTarget gamma0)
      (D.component gamma0) (rayForwardFiberCarrier n)
      hsource htarget hforward
  exact hmem.mono fun _ h => ⟨_, h⟩

end MaximalRayKernelDisintegration

end RaySpecialization

end ConcaveOTLimit
