import Theorems.Thm_ConcaveOTLimit_liftedSameLabelCouplingCompact
import Theorems.Thm_ConcaveOTLimit_kernelDisintegration
import Theorems.Thm_ConcaveOTLimit_kernelDisintegrationUniqueness
import Theorems.Thm_ConcaveOTLimit_kernelDeterministicGluing
import Theorems.Thm_ConcaveOTLimit_labeledCouplingDisintegration
import Theorems.Thm_ConcaveOTLimit_orientedOpenRayStandardBorel

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped BoundedContinuousFunction ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

section KernelLift

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]

/-- The joint law of a finite base and a Markov kernel, bundled as a finite
measure on the explicitly labeled space. -/
noncomputable def liftedKernelMarginal
    (sigma : FiniteMeasure R) (kappa : Kernel R X)
    [IsMarkovKernel kappa] :
    FiniteMeasure (R × X) :=
  ⟨(sigma : Measure R) ⊗ₘ kappa, inferInstance⟩

/-- Put the common kernel parameter into both sides of a component pair. -/
def liftedComponentMap (p : R × (X × Y)) :
    (R × X) × (R × Y) :=
  ((p.1, p.2.1), (p.1, p.2.2))

theorem measurable_liftedComponentMap :
    Measurable (liftedComponentMap : R × (X × Y) -> (R × X) × (R × Y)) := by
  unfold liftedComponentMap
  fun_prop

/-- Map the joint law of the base and a component coupling kernel to a
coupling of explicitly labeled points. -/
noncomputable def liftedComponentPlan
    (sigma : FiniteMeasure R) (component : Kernel R (X × Y))
    [IsMarkovKernel component] :
    FiniteMeasure ((R × X) × (R × Y)) :=
  ⟨((sigma : Measure R) ⊗ₘ component).map liftedComponentMap,
    inferInstance⟩

@[simp]
theorem liftedComponentPlan_toMeasure
    (sigma : FiniteMeasure R) (component : Kernel R (X × Y))
    [IsMarkovKernel component] :
    (liftedComponentPlan sigma component :
      Measure ((R × X) × (R × Y))) =
      ((sigma : Measure R) ⊗ₘ component).map liftedComponentMap :=
  rfl

/-- The first marginal of the lifted component plan is exactly the lifted
source kernel law. -/
theorem firstMarginal_liftedComponentPlan
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source) :
    firstMarginal (liftedComponentPlan sigma component) =
      liftedKernelMarginal sigma source := by
  apply FiniteMeasure.toMeasure_injective
  change
    Measure.map Prod.fst
        (((sigma : Measure R) ⊗ₘ component).map liftedComponentMap) =
      (sigma : Measure R) ⊗ₘ source
  calc
    Measure.map Prod.fst
        (((sigma : Measure R) ⊗ₘ component).map liftedComponentMap) =
        ((sigma : Measure R) ⊗ₘ component).map
          (Prod.map id Prod.fst) := by
      rw [Measure.map_map measurable_fst measurable_liftedComponentMap]
      rfl
    _ = (sigma : Measure R) ⊗ₘ component.map Prod.fst :=
      (Measure.compProd_map measurable_fst).symm
    _ = (sigma : Measure R) ⊗ₘ source :=
      Measure.compProd_congr hsource

/-- The second marginal of the lifted component plan is exactly the lifted
target kernel law. -/
theorem secondMarginal_liftedComponentPlan
    (sigma : FiniteMeasure R)
    (target : Kernel R Y) (component : Kernel R (X × Y))
    [IsMarkovKernel target] [IsMarkovKernel component]
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target) :
    secondMarginal (liftedComponentPlan sigma component) =
      liftedKernelMarginal sigma target := by
  apply FiniteMeasure.toMeasure_injective
  change
    Measure.map Prod.snd
        (((sigma : Measure R) ⊗ₘ component).map liftedComponentMap) =
      (sigma : Measure R) ⊗ₘ target
  calc
    Measure.map Prod.snd
        (((sigma : Measure R) ⊗ₘ component).map liftedComponentMap) =
        ((sigma : Measure R) ⊗ₘ component).map
          (Prod.map id Prod.snd) := by
      rw [Measure.map_map measurable_snd measurable_liftedComponentMap]
      rfl
    _ = (sigma : Measure R) ⊗ₘ component.map Prod.snd :=
      (Measure.compProd_map measurable_snd).symm
    _ = (sigma : Measure R) ⊗ₘ target :=
      Measure.compProd_congr htarget

/-- The lifted component plan is carried exactly by pairs whose copied
labels agree. -/
theorem liftedComponentPlan_isSupported_sameLabel
    [MeasurableEq R]
    (sigma : FiniteMeasure R) (component : Kernel R (X × Y))
    [IsMarkovKernel component] :
    ∀ᵐ z ∂(liftedComponentPlan sigma component :
      Measure ((R × X) × (R × Y))),
      z ∈ liftedSameLabelRelation R X Y := by
  have hrelation :
      MeasurableSet (liftedSameLabelRelation R X Y) := by
    exact measurableSet_eq_fun
      (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)
  have hequality :
      MeasurableSet
        {z : (R × X) × (R × Y) | z.1.1 = z.2.1} := by
    simpa only [liftedSameLabelRelation] using hrelation
  change
    ∀ᵐ z ∂((sigma : Measure R) ⊗ₘ component).map liftedComponentMap,
      z.1.1 = z.2.1
  rw [ae_map_iff measurable_liftedComponentMap.aemeasurable hequality]
  exact Eventually.of_forall fun _ => rfl

/-- The mapped component law, with the two exact marginal identities
installed, is a finite coupling of the lifted kernel laws. -/
noncomputable def liftedComponentCoupling
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target) :
    FiniteCoupling
      (liftedKernelMarginal sigma source)
      (liftedKernelMarginal sigma target) :=
  ⟨liftedComponentPlan sigma component,
    firstMarginal_liftedComponentPlan sigma source component hsource,
    secondMarginal_liftedComponentPlan sigma target component htarget⟩

@[simp]
theorem liftedComponentCoupling_plan
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target) :
    (liftedComponentCoupling sigma source target component
        hsource htarget).plan =
      liftedComponentPlan sigma component :=
  rfl

/-- The packaged lifted component coupling is a same-label witness. -/
theorem liftedComponentCoupling_isSupported_sameLabel
    [MeasurableEq R]
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target) :
    IsSupported
      (liftedComponentCoupling sigma source target component
        hsource htarget)
      (liftedSameLabelRelation R X Y) := by
  exact liftedComponentPlan_isSupported_sameLabel sigma component

end KernelLift

section Minimizer

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  [BorelSpace R] [BorelSpace X] [BorelSpace Y]
  [PolishSpace R] [PolishSpace X] [PolishSpace Y]

/-- A Markov component kernel with the prescribed source and target
marginal kernels supplies the nonempty same-label constraint needed by the
compactness theorem, hence every lower-semicontinuous objective attains a
minimum there. -/
theorem existsLiftedSameLabelKernelMinimizerOfLowerSemicontinuous
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    (cost :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target) -> Real)
    (hcost :
      LowerSemicontinuousOn cost
        (liftedSameLabelCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
        (liftedSameLabelCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        cost gamma := by
  let witness :=
    liftedComponentCoupling sigma source target component hsource htarget
  exact
    existsLiftedSameLabelCouplingMinimizerOfLowerSemicontinuous
      witness
      (liftedComponentCoupling_isSupported_sameLabel
        sigma source target component hsource htarget)
      cost hcost

/-- Integrate a bounded continuous cost over the underlying lifted plan. -/
def liftedBoundedContinuousCost
    {alpha : FiniteMeasure (R × X)}
    {beta : FiniteMeasure (R × Y)}
    (cost : ((R × X) × (R × Y)) →ᵇ Real)
    (gamma : FiniteCoupling alpha beta) : Real :=
  ∫ z, cost z ∂(gamma.plan : Measure ((R × X) × (R × Y)))

theorem continuous_liftedBoundedContinuousCost
    {alpha : FiniteMeasure (R × X)}
    {beta : FiniteMeasure (R × Y)}
    (cost : ((R × X) × (R × Y)) →ᵇ Real) :
    Continuous
      (liftedBoundedContinuousCost
        (alpha := alpha) (beta := beta) cost) := by
  have hplan :
      Continuous
        (fun gamma : FiniteCoupling alpha beta => gamma.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val :
        Continuous
          (fun gamma : FiniteCoupling alpha beta =>
            (gamma.1 : FiniteMeasure ((R × X) × (R × Y)))))
  exact
    (FiniteMeasure.continuous_integral_boundedContinuousFunction cost).comp
      hplan

/-- Bounded continuous point costs give continuous, and therefore
lower-semicontinuous, objectives on the compact same-label coupling set. -/
theorem existsLiftedSameLabelKernelMinimizerOfBoundedContinuous
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    (cost : ((R × X) × (R × Y)) →ᵇ Real) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
        (liftedSameLabelCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        (liftedBoundedContinuousCost cost) gamma := by
  apply existsLiftedSameLabelKernelMinimizerOfLowerSemicontinuous
    sigma source target component hsource htarget
  exact ContinuousOn.lowerSemicontinuousOn
    (Continuous.continuousOn
      (continuous_liftedBoundedContinuousCost cost))

end Minimizer

section OrientedOpenRayForward

/-- Lifted endpoint pairs with one common oriented-ray label and forward
order in that ray's coordinate. -/
def liftedRayForwardRelation (n : Nat) :
    Set
      ((OrientedOpenRay n × Euclidean n) ×
        (OrientedOpenRay n × Euclidean n)) :=
  {z |
    z.1.1 = z.2.1 ∧
      rayCoordinate z.1.1 z.1.2 ≤ rayCoordinate z.1.1 z.2.2}

/-- Equal labels and forward ray-coordinate order define a closed lifted
carrier. -/
theorem isClosed_liftedRayForwardRelation (n : Nat) :
    IsClosed (liftedRayForwardRelation n) := by
  have hlabels :
      IsClosed
        (liftedSameLabelRelation
          (OrientedOpenRay n) (Euclidean n) (Euclidean n)) :=
    isClosed_liftedSameLabelRelation
  have hcoordinates :
      IsClosed
        {z :
            (OrientedOpenRay n × Euclidean n) ×
              (OrientedOpenRay n × Euclidean n) |
          rayCoordinate z.1.1 z.1.2 ≤
            rayCoordinate z.1.1 z.2.2} :=
    isClosed_le
      (continuous_rayCoordinate_uncurry.comp continuous_fst)
      (continuous_rayCoordinate_uncurry.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_snd)))
  simpa only [liftedRayForwardRelation, liftedSameLabelRelation,
    setOf_and] using hlabels.inter hcoordinates

theorem liftedRayForwardRelation_subset_sameLabel (n : Nat) :
    liftedRayForwardRelation n ⊆
      liftedSameLabelRelation
        (OrientedOpenRay n) (Euclidean n) (Euclidean n) := by
  intro z hz
  exact hz.1

/-- Fixed lifted marginals, equal ray labels, and forward ray-coordinate
order form the feasible set for the global raywise problem. -/
def liftedRayForwardCouplingSet
    {n : Nat}
    (alpha beta : FiniteMeasure (OrientedOpenRay n × Euclidean n)) :
    Set (FiniteCoupling alpha beta) :=
  {gamma | IsSupported gamma (liftedRayForwardRelation n)}

theorem isClosed_liftedRayForwardCouplingSet
    {n : Nat}
    (alpha beta : FiniteMeasure (OrientedOpenRay n × Euclidean n)) :
    IsClosed (liftedRayForwardCouplingSet alpha beta) := by
  exact isClosed_finiteCouplingSupportedOnClosed
    (isClosed_liftedRayForwardRelation n)

theorem isCompact_liftedRayForwardCouplingSet
    {n : Nat}
    (alpha beta : FiniteMeasure (OrientedOpenRay n × Euclidean n)) :
    IsCompact (liftedRayForwardCouplingSet alpha beta) := by
  exact isCompact_finiteCouplingSupportedOnClosed alpha beta
    (isClosed_liftedRayForwardRelation n)

/-- A component kernel that is forward in its base ray coordinate maps
exactly into the closed lifted forward carrier. -/
theorem liftedComponentPlan_isSupported_rayForward
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (component :
      Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n))
    [IsMarkovKernel component]
    (hforward :
      ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂component R,
          rayCoordinate R z.1 ≤ rayCoordinate R z.2) :
    ∀ᵐ z ∂(liftedComponentPlan sigma component :
        Measure
          ((OrientedOpenRay n × Euclidean n) ×
            (OrientedOpenRay n × Euclidean n))),
      z ∈ liftedRayForwardRelation n := by
  have hcarrier :
      MeasurableSet (liftedRayForwardRelation n) :=
    (isClosed_liftedRayForwardRelation n).measurableSet
  have hproperty :
      MeasurableSet
        {z :
            (OrientedOpenRay n × Euclidean n) ×
              (OrientedOpenRay n × Euclidean n) |
          z.1.1 = z.2.1 ∧
            rayCoordinate z.1.1 z.1.2 ≤
              rayCoordinate z.1.1 z.2.2} := by
    simpa only [liftedRayForwardRelation] using hcarrier
  change
    ∀ᵐ z ∂
        ((sigma : Measure (OrientedOpenRay n)) ⊗ₘ component).map
          liftedComponentMap,
      z.1.1 = z.2.1 ∧
        rayCoordinate z.1.1 z.1.2 ≤ rayCoordinate z.1.1 z.2.2
  rw [ae_map_iff measurable_liftedComponentMap.aemeasurable hproperty]
  apply Measure.ae_compProd_of_ae_ae
  · exact hproperty.preimage measurable_liftedComponentMap
  · filter_upwards [hforward] with R hR
    filter_upwards [hR] with z hz
    exact ⟨rfl, hz⟩

/-- The component coupling is a feasible witness for the closed lifted
forward coupling set. -/
theorem liftedComponentCoupling_isSupported_rayForward
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target : Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] source)
    (htarget :
      component.map Prod.snd
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] target)
    (hforward :
      ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂component R,
          rayCoordinate R z.1 ≤ rayCoordinate R z.2) :
    IsSupported
      (liftedComponentCoupling sigma source target component
        hsource htarget)
      (liftedRayForwardRelation n) := by
  exact liftedComponentPlan_isSupported_rayForward
    sigma component hforward

/-- Compactness of the closed lifted forward carrier turns a forward
component kernel into existence of a global minimizer for every
lower-semicontinuous objective. -/
theorem existsLiftedRayForwardKernelMinimizerOfLowerSemicontinuous
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target : Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] source)
    (htarget :
      component.map Prod.snd
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] target)
    (hforward :
      ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂component R,
          rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (cost :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target) -> Real)
    (hcost :
      LowerSemicontinuousOn cost
        (liftedRayForwardCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
        (liftedRayForwardCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        cost gamma := by
  let witness :=
    liftedComponentCoupling sigma source target component hsource htarget
  have hwitness :
      witness ∈
        liftedRayForwardCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target) :=
    liftedComponentCoupling_isSupported_rayForward
      sigma source target component hsource htarget hforward
  obtain ⟨gamma, hgamma, hgammaMin⟩ :=
    hcost.exists_isMinOn
      ⟨witness, hwitness⟩
      (isCompact_liftedRayForwardCouplingSet
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
  exact ⟨gamma, hgamma, hgammaMin⟩

/-- Bounded continuous point costs attain a global minimum over all
same-ray forward lifted couplings. -/
theorem existsLiftedRayForwardKernelMinimizerOfBoundedContinuous
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target : Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] source)
    (htarget :
      component.map Prod.snd
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] target)
    (hforward :
      ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂component R,
          rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (cost :
      ((OrientedOpenRay n × Euclidean n) ×
        (OrientedOpenRay n × Euclidean n)) →ᵇ Real) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
        (liftedRayForwardCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        (liftedBoundedContinuousCost cost) gamma := by
  apply existsLiftedRayForwardKernelMinimizerOfLowerSemicontinuous
    sigma source target component hsource htarget hforward
  exact ContinuousOn.lowerSemicontinuousOn
    (Continuous.continuousOn
      (continuous_liftedBoundedContinuousCost cost))

end OrientedOpenRayForward

section StrictExponentialProfile

/-- The bounded strict profile used for the clean existence specialization. -/
def strictExponentialProfile (d : Real) : Real :=
  1 - Real.exp (-d)

theorem continuous_strictExponentialProfile :
    Continuous strictExponentialProfile := by
  unfold strictExponentialProfile
  fun_prop

variable (R E : Type*)
  [TopologicalSpace R] [PseudoMetricSpace E]

/-- The lifted bounded continuous point cost
`chi(dist x y) = 1 - exp (-dist x y)`, ignoring the copied labels. -/
noncomputable def liftedStrictExponentialCost :
    ((R × E) × (R × E)) →ᵇ Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z : (R × E) × (R × E) =>
      strictExponentialProfile (dist z.1.2 z.2.2))
    (by
      apply continuous_strictExponentialProfile.comp
      fun_prop)
    1
    (fun z : (R × E) × (R × E) => by
      have hexp :
          Real.exp (-dist z.1.2 z.2.2) ≤ 1 := by
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr dist_nonneg)
      change |1 - Real.exp (-dist z.1.2 z.2.2)| ≤ 1
      rw [abs_of_nonneg (sub_nonneg.mpr hexp)]
      exact sub_le_self 1 (Real.exp_nonneg _))

@[simp]
theorem liftedStrictExponentialCost_apply
    (z : (R × E) × (R × E)) :
    liftedStrictExponentialCost R E z =
      1 - Real.exp (-dist z.1.2 z.2.2) :=
  rfl

variable {R E : Type*}
  [MeasurableSpace R] [MeasurableSpace E]
  [TopologicalSpace R] [MetricSpace E]
  [BorelSpace R] [BorelSpace E]
  [PolishSpace R] [PolishSpace E]

/-- Existence for the strict bounded profile
`chi(d) = 1 - exp (-d)` on each same-label fiber. This is only a global
lifted minimizer statement; it asserts no fiberwise minimality. -/
theorem existsLiftedSameLabelKernelMinimizer_strictExponentialProfile
    (sigma : FiniteMeasure R)
    (source target : Kernel R E)
    (component : Kernel R (E × E))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
        (liftedSameLabelCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        (fun eta =>
          ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
            ∂(eta.plan : Measure ((R × E) × (R × E))))
        gamma := by
  simpa [liftedBoundedContinuousCost, liftedStrictExponentialCost,
    strictExponentialProfile] using
    existsLiftedSameLabelKernelMinimizerOfBoundedContinuous
      sigma source target component hsource htarget
      (liftedStrictExponentialCost R E)

end StrictExponentialProfile

section OrientedOpenRayStrictExponentialProfile

/-- The global strict-profile minimizer over lifted couplings that have
equal oriented-ray labels and are forward in the common ray coordinate. -/
theorem existsLiftedRayForwardKernelMinimizer_strictExponentialProfile
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target : Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] source)
    (htarget :
      component.map Prod.snd
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] target)
    (hforward :
      ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂component R,
          rayCoordinate R z.1 ≤ rayCoordinate R z.2) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
        (liftedRayForwardCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        (fun eta =>
          ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
            ∂(eta.plan :
              Measure
                ((OrientedOpenRay n × Euclidean n) ×
                  (OrientedOpenRay n × Euclidean n))))
        gamma := by
  simpa [liftedBoundedContinuousCost, liftedStrictExponentialCost,
    strictExponentialProfile] using
    existsLiftedRayForwardKernelMinimizerOfBoundedContinuous
      sigma source target component hsource htarget hforward
      (liftedStrictExponentialCost (OrientedOpenRay n) (Euclidean n))

end OrientedOpenRayStrictExponentialProfile

end ConcaveOTLimit
