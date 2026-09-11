import Theorems.Thm_ConcaveOTLimit_kernelDeterministicGluing
import Theorems.Thm_ConcaveOTLimit_fiberwiseImprovementSelection
import Theorems.Thm_ConcaveOTLimit_fiberwiseKernelMinimality
import Theorems.Thm_ConcaveOTLimit_liftedSameLabelKernelMinimizer
import Theorems.Thm_ConcaveOTLimit_measurableEndpointAllocation
import Theorems.Thm_ConcaveOTLimit_rayConditionalAtomlessness

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Forward geometry of the maximal-ray components -/

theorem pairRay_coordinate_forward_of_mem
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
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

theorem pairRay_coordinate_forward_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)),
      rayCoordinate (D.pairRay z) z.1 ≤
        rayCoordinate (D.pairRay z) z.2 := by
  filter_upwards [hSupported] with z hz
  exact pairRay_coordinate_forward_of_mem D hz

theorem maximalRayComponent_coordinate_forward_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
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
    exact pairRay_coordinate_forward_ae D gamma hSupported
  filter_upwards
      [hIndexed, D.component_ae_fiber_eq gamma hSupported] with
      R hForward hLabel
  filter_upwards [hForward, hLabel] with z hz hR
  simpa only [hR] using hz

/-! ## Projecting a lifted same-label coupling back to component kernels -/

section Unlift

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace R] [StandardBorelSpace X] [StandardBorelSpace Y]
  [Nonempty R] [Nonempty X] [Nonempty Y]

def liftedFirstLabel (z : (R × X) × (R × Y)) : R :=
  z.1.1

def dropLiftedLabels (z : (R × X) × (R × Y)) : X × Y :=
  (z.1.2, z.2.2)

def liftedSourceValue (z : (R × X) × (R × Y)) : X :=
  z.1.2

def liftedTargetValue (z : (R × X) × (R × Y)) : Y :=
  z.2.2

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem measurable_liftedFirstLabel :
    Measurable (liftedFirstLabel : (R × X) × (R × Y) -> R) := by
  unfold liftedFirstLabel
  fun_prop

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem measurable_dropLiftedLabels :
    Measurable (dropLiftedLabels : (R × X) × (R × Y) -> X × Y) := by
  unfold dropLiftedLabels
  fun_prop

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem measurable_liftedSourceValue :
    Measurable (liftedSourceValue : (R × X) × (R × Y) -> X) := by
  unfold liftedSourceValue
  fun_prop

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem measurable_liftedTargetValue :
    Measurable (liftedTargetValue : (R × X) × (R × Y) -> Y) := by
  unfold liftedTargetValue
  fun_prop

noncomputable def liftedCouplingLabelKernel
    {alpha : FiniteMeasure (R × X)} {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta) :
    Kernel R ((R × X) × (R × Y)) :=
  ap91Disintegration liftedFirstLabel
    (gamma.plan : Measure ((R × X) × (R × Y)))

noncomputable def unliftedSameLabelKernel
    {alpha : FiniteMeasure (R × X)} {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta) :
    Kernel R (X × Y) :=
  (liftedCouplingLabelKernel gamma).map dropLiftedLabels

theorem liftedCouplingLabelKernel_isMarkovKernel
    {alpha : FiniteMeasure (R × X)} {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta) :
    IsMarkovKernel (liftedCouplingLabelKernel gamma) := by
  exact ap91Disintegration_isMarkovKernel liftedFirstLabel
    (gamma.plan : Measure ((R × X) × (R × Y)))

theorem unliftedSameLabelKernel_isMarkovKernel
    {alpha : FiniteMeasure (R × X)} {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta) :
    IsMarkovKernel (unliftedSameLabelKernel gamma) := by
  letI : IsMarkovKernel (liftedCouplingLabelKernel gamma) :=
    liftedCouplingLabelKernel_isMarkovKernel gamma
  exact Kernel.IsMarkovKernel.map
    (liftedCouplingLabelKernel gamma) measurable_dropLiftedLabels

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem liftedCoupling_firstLabelBase
    (sigma : FiniteMeasure R) (source : Kernel R X)
    [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    Measure.map liftedFirstLabel
        (gamma.plan : Measure ((R × X) × (R × Y))) =
      (sigma : Measure R) := by
  have hFirst :
      Measure.map (Prod.fst : (R × X) × (R × Y) -> R × X)
          (gamma.plan : Measure ((R × X) × (R × Y))) =
        (sigma : Measure R) ⊗ₘ source := by
    simpa [firstMarginal, liftedKernelMarginal,
      FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure (R × X) => (eta : Measure (R × X)))
        gamma.property.1
  calc
    Measure.map liftedFirstLabel
        (gamma.plan : Measure ((R × X) × (R × Y))) =
        Measure.map Prod.fst
          (Measure.map Prod.fst
            (gamma.plan : Measure ((R × X) × (R × Y)))) := by
      rw [Measure.map_map measurable_fst measurable_fst]
      rfl
    _ = Measure.map Prod.fst ((sigma : Measure R) ⊗ₘ source) := by
      rw [hFirst]
    _ = (sigma : Measure R) := by
      exact Measure.fst_compProd (sigma : Measure R) source

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem liftedCoupling_firstMarginal_measure
    (sigma : FiniteMeasure R) (source : Kernel R X)
    [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    Measure.map (Prod.fst : (R × X) × (R × Y) -> R × X)
        (gamma.plan : Measure ((R × X) × (R × Y))) =
      (sigma : Measure R) ⊗ₘ source := by
  simpa [firstMarginal, liftedKernelMarginal,
    FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (R × X) => (eta : Measure (R × X)))
      gamma.property.1

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
theorem liftedCoupling_secondMarginal_measure
    {alpha : FiniteMeasure (R × X)}
    (sigma : FiniteMeasure R) (target : Kernel R Y)
    [IsMarkovKernel target]
    (gamma :
      FiniteCoupling alpha (liftedKernelMarginal sigma target)) :
    Measure.map (Prod.snd : (R × X) × (R × Y) -> R × Y)
        (gamma.plan : Measure ((R × X) × (R × Y))) =
      (sigma : Measure R) ⊗ₘ target := by
  simpa [secondMarginal, liftedKernelMarginal,
    FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (R × Y) => (eta : Measure (R × Y)))
      gamma.property.2

theorem liftedCouplingLabelKernel_reconstruction
    (sigma : FiniteMeasure R) (source : Kernel R X)
    [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    liftedCouplingLabelKernel gamma ∘ₘ (sigma : Measure R) =
      (gamma.plan : Measure ((R × X) × (R × Y))) := by
  rw [← liftedCoupling_firstLabelBase sigma source gamma]
  exact ap91_reconstruction liftedFirstLabel
    (gamma.plan : Measure ((R × X) × (R × Y)))
    measurable_liftedFirstLabel

theorem liftedCouplingLabelKernel_joint_reconstruction
    (sigma : FiniteMeasure R) (source : Kernel R X)
    [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    (sigma : Measure R) ⊗ₘ liftedCouplingLabelKernel gamma =
      Measure.map (fun z => (liftedFirstLabel z, z))
        (gamma.plan : Measure ((R × X) × (R × Y))) := by
  rw [← liftedCoupling_firstLabelBase sigma source gamma]
  exact ap91_joint_reconstruction liftedFirstLabel
    (gamma.plan : Measure ((R × X) × (R × Y)))

theorem unliftedSameLabelKernel_reconstruction
    (sigma : FiniteMeasure R) (source : Kernel R X)
    [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    unliftedSameLabelKernel gamma ∘ₘ (sigma : Measure R) =
      Measure.map dropLiftedLabels
        (gamma.plan : Measure ((R × X) × (R × Y))) := by
  change
    (liftedCouplingLabelKernel gamma).map dropLiftedLabels
        ∘ₘ (sigma : Measure R) =
      Measure.map dropLiftedLabels
        (gamma.plan : Measure ((R × X) × (R × Y)))
  rw [← Measure.map_comp (sigma : Measure R)
      (liftedCouplingLabelKernel gamma) measurable_dropLiftedLabels,
    liftedCouplingLabelKernel_reconstruction sigma source gamma]

theorem unliftedSameLabelKernel_map_fst_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target)) :
    (unliftedSameLabelKernel gamma).map Prod.fst
      =ᵐ[(sigma : Measure R)] source := by
  letI : IsMarkovKernel (liftedCouplingLabelKernel gamma) :=
    liftedCouplingLabelKernel_isMarkovKernel gamma
  letI : IsMarkovKernel (unliftedSameLabelKernel gamma) :=
    unliftedSameLabelKernel_isMarkovKernel gamma
  have hDropProd :
      Measurable
        (Prod.map id dropLiftedLabels :
          R × ((R × X) × (R × Y)) -> R × (X × Y)) :=
    measurable_id.prodMap measurable_dropLiftedLabels
  have hFstProd :
      Measurable
        (Prod.map id Prod.fst : R × (X × Y) -> R × X) :=
    measurable_id.prodMap measurable_fst
  have hGraph :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (liftedFirstLabel z, z)) :=
    measurable_liftedFirstLabel.prodMk measurable_id
  apply Kernel.ae_eq_of_compProd_eq
  calc
    (sigma : Measure R) ⊗ₘ
          (unliftedSameLabelKernel gamma).map Prod.fst =
        Measure.map (Prod.map id Prod.fst)
          ((sigma : Measure R) ⊗ₘ
            unliftedSameLabelKernel gamma) :=
      Measure.compProd_map measurable_fst
    _ = Measure.map (Prod.map id Prod.fst)
          (Measure.map (Prod.map id dropLiftedLabels)
            ((sigma : Measure R) ⊗ₘ
              liftedCouplingLabelKernel gamma)) := by
      rw [unliftedSameLabelKernel,
        Measure.compProd_map measurable_dropLiftedLabels]
    _ = Measure.map
          ((Prod.map id Prod.fst) ∘
            (Prod.map id dropLiftedLabels))
          ((sigma : Measure R) ⊗ₘ
            liftedCouplingLabelKernel gamma) := by
      rw [Measure.map_map hFstProd hDropProd]
    _ = Measure.map
          ((Prod.map id Prod.fst) ∘
            (Prod.map id dropLiftedLabels))
          (Measure.map (fun z => (liftedFirstLabel z, z))
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) := by
      rw [liftedCouplingLabelKernel_joint_reconstruction
        sigma source gamma]
    _ = Measure.map
          (((Prod.map id Prod.fst) ∘
              (Prod.map id dropLiftedLabels)) ∘
            fun z => (liftedFirstLabel z, z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      rw [Measure.map_map (hFstProd.comp hDropProd) hGraph]
    _ = Measure.map Prod.fst
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      congr 1
    _ = (sigma : Measure R) ⊗ₘ source :=
      liftedCoupling_firstMarginal_measure sigma source gamma

theorem unliftedSameLabelKernel_map_snd_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
    (hSameLabel :
      IsSupported gamma (liftedSameLabelRelation R X Y)) :
    (unliftedSameLabelKernel gamma).map Prod.snd
      =ᵐ[(sigma : Measure R)] target := by
  letI : IsMarkovKernel (liftedCouplingLabelKernel gamma) :=
    liftedCouplingLabelKernel_isMarkovKernel gamma
  letI : IsMarkovKernel (unliftedSameLabelKernel gamma) :=
    unliftedSameLabelKernel_isMarkovKernel gamma
  have hDropProd :
      Measurable
        (Prod.map id dropLiftedLabels :
          R × ((R × X) × (R × Y)) -> R × (X × Y)) :=
    measurable_id.prodMap measurable_dropLiftedLabels
  have hSndProd :
      Measurable
        (Prod.map id Prod.snd : R × (X × Y) -> R × Y) :=
    measurable_id.prodMap measurable_snd
  have hGraph :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (liftedFirstLabel z, z)) :=
    measurable_liftedFirstLabel.prodMk measurable_id
  apply Kernel.ae_eq_of_compProd_eq
  calc
    (sigma : Measure R) ⊗ₘ
          (unliftedSameLabelKernel gamma).map Prod.snd =
        Measure.map (Prod.map id Prod.snd)
          ((sigma : Measure R) ⊗ₘ
            unliftedSameLabelKernel gamma) :=
      Measure.compProd_map measurable_snd
    _ = Measure.map (Prod.map id Prod.snd)
          (Measure.map (Prod.map id dropLiftedLabels)
            ((sigma : Measure R) ⊗ₘ
              liftedCouplingLabelKernel gamma)) := by
      rw [unliftedSameLabelKernel,
        Measure.compProd_map measurable_dropLiftedLabels]
    _ = Measure.map
          ((Prod.map id Prod.snd) ∘
            (Prod.map id dropLiftedLabels))
          ((sigma : Measure R) ⊗ₘ
            liftedCouplingLabelKernel gamma) := by
      rw [Measure.map_map hSndProd hDropProd]
    _ = Measure.map
          ((Prod.map id Prod.snd) ∘
            (Prod.map id dropLiftedLabels))
          (Measure.map (fun z => (liftedFirstLabel z, z))
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) := by
      rw [liftedCouplingLabelKernel_joint_reconstruction
        sigma source gamma]
    _ = Measure.map
          (((Prod.map id Prod.snd) ∘
              (Prod.map id dropLiftedLabels)) ∘
            fun z => (liftedFirstLabel z, z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      rw [Measure.map_map (hSndProd.comp hDropProd) hGraph]
    _ = Measure.map Prod.snd
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      apply Measure.map_congr
      filter_upwards [hSameLabel] with z hz
      exact Prod.ext hz rfl
    _ = (sigma : Measure R) ⊗ₘ target :=
      liftedCoupling_secondMarginal_measure sigma target gamma

noncomputable def unliftedLiftedCoupling
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hsource :
      source ∘ₘ (sigma : Measure R) = (mu : Measure X))
    (htarget :
      target ∘ₘ (sigma : Measure R) = (nu : Measure Y))
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target)) :
    FiniteCoupling mu nu := by
  let plan : FiniteMeasure (X × Y) :=
    gamma.plan.map dropLiftedLabels
  refine ⟨plan, ?_, ?_⟩
  · apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.fst
          (Measure.map dropLiftedLabels
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) =
        (mu : Measure X)
    rw [Measure.map_map measurable_fst measurable_dropLiftedLabels]
    calc
      Measure.map (Prod.fst ∘ dropLiftedLabels)
          (gamma.plan :
            Measure ((R × X) × (R × Y))) =
          Measure.map Prod.snd
            (Measure.map Prod.fst
              (gamma.plan :
                Measure ((R × X) × (R × Y)))) := by
        rw [Measure.map_map measurable_snd measurable_fst]
        rfl
      _ = Measure.map Prod.snd
          ((sigma : Measure R) ⊗ₘ source) := by
        rw [liftedCoupling_firstMarginal_measure
          sigma source gamma]
      _ = source ∘ₘ (sigma : Measure R) :=
        Measure.snd_compProd (sigma : Measure R) source
      _ = (mu : Measure X) := hsource
  · apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.snd
          (Measure.map dropLiftedLabels
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) =
        (nu : Measure Y)
    rw [Measure.map_map measurable_snd measurable_dropLiftedLabels]
    calc
      Measure.map (Prod.snd ∘ dropLiftedLabels)
          (gamma.plan :
            Measure ((R × X) × (R × Y))) =
          Measure.map Prod.snd
            (Measure.map Prod.snd
              (gamma.plan :
                Measure ((R × X) × (R × Y)))) := by
        rw [Measure.map_map measurable_snd measurable_snd]
        rfl
      _ = Measure.map Prod.snd
          ((sigma : Measure R) ⊗ₘ target) := by
        rw [liftedCoupling_secondMarginal_measure
          sigma target gamma]
      _ = target ∘ₘ (sigma : Measure R) :=
        Measure.snd_compProd (sigma : Measure R) target
      _ = (nu : Measure Y) := htarget

omit [StandardBorelSpace R] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty R] [Nonempty X] [Nonempty Y] in
@[simp]
theorem unliftedLiftedCoupling_plan
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hsource :
      source ∘ₘ (sigma : Measure R) = (mu : Measure X))
    (htarget :
      target ∘ₘ (sigma : Measure R) = (nu : Measure Y))
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target)) :
    (unliftedLiftedCoupling sigma source target
        hsource htarget gamma).plan =
      gamma.plan.map dropLiftedLabels :=
  rfl

theorem unliftedSameLabelKernel_reconstructs_coupling
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hsource :
      source ∘ₘ (sigma : Measure R) = (mu : Measure X))
    (htarget :
      target ∘ₘ (sigma : Measure R) = (nu : Measure Y))
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target)) :
    unliftedSameLabelKernel gamma ∘ₘ (sigma : Measure R) =
      ((unliftedLiftedCoupling sigma source target
          hsource htarget gamma).plan : Measure (X × Y)) := by
  exact unliftedSameLabelKernel_reconstruction sigma source gamma

theorem unliftedSameLabelKernel_ae_of_liftedLabelProperty
    (sigma : FiniteMeasure R) (source : Kernel R X)
    [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta)
    (P : R -> X × Y -> Prop)
    (hP : ∀ r, MeasurableSet {z | P r z})
    (hLifted :
      ∀ᵐ z ∂(gamma.plan :
          Measure ((R × X) × (R × Y))),
        P (liftedFirstLabel z) (dropLiftedLabels z)) :
    ∀ᵐ r ∂(sigma : Measure R),
      ∀ᵐ z ∂unliftedSameLabelKernel gamma r, P r z := by
  letI : IsMarkovKernel (liftedCouplingLabelKernel gamma) :=
    liftedCouplingLabelKernel_isMarkovKernel gamma
  have hLiftedFiber :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂liftedCouplingLabelKernel gamma r,
          P (liftedFirstLabel z) (dropLiftedLabels z) := by
    apply Measure.ae_ae_of_ae_comp
    rw [liftedCouplingLabelKernel_reconstruction sigma source gamma]
    exact hLifted
  have hLabelFiber :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂liftedCouplingLabelKernel gamma r,
          liftedFirstLabel z = r := by
    have h :=
      ap91_ae_fiber_eq liftedFirstLabel
        (gamma.plan : Measure ((R × X) × (R × Y)))
        measurable_liftedFirstLabel
    rw [liftedCoupling_firstLabelBase sigma source gamma] at h
    exact h
  filter_upwards [hLiftedFiber, hLabelFiber] with r hr hLabel
  rw [unliftedSameLabelKernel,
    Kernel.map_apply _ measurable_dropLiftedLabels]
  apply
    (ae_map_iff measurable_dropLiftedLabels.aemeasurable
      (hP r)).2
  filter_upwards [hr, hLabel] with z hz hzLabel
  simpa only [hzLabel] using hz

end Unlift

theorem unliftedSameLabelKernel_rayForward_ae
    {n : Nat}
    [Nonempty (OrientedOpenRay n)]
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
    (hForward :
      IsSupported gamma (liftedRayForwardRelation n)) :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂unliftedSameLabelKernel gamma R,
        rayCoordinate R z.1 ≤ rayCoordinate R z.2 := by
  apply unliftedSameLabelKernel_ae_of_liftedLabelProperty
    sigma source gamma
    (fun R z => rayCoordinate R z.1 ≤ rayCoordinate R z.2)
  · intro R
    exact measurableSet_le
      ((measurable_rayCoordinate R).comp measurable_fst)
      ((measurable_rayCoordinate R).comp measurable_snd)
  · filter_upwards [hForward] with z hz
    exact hz.2

/-! ## Elementary finite-coupling adapters -/

section FiniteCouplingAdapters

variable {X Y X' Y' : Type*}
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace X'] [MeasurableSpace Y']

noncomputable def mapFiniteCoupling
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (f : X -> X') (g : Y -> Y')
    (hf : Measurable f) (hg : Measurable g) :
    FiniteCoupling (mu.map f) (nu.map g) := by
  refine ⟨gamma.plan.map (Prod.map f g), ?_, ?_⟩
  · apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.fst
          (Measure.map (Prod.map f g)
            (gamma.plan : Measure (X × Y))) =
        Measure.map f (mu : Measure X)
    rw [Measure.map_map measurable_fst (hf.prodMap hg)]
    change
      Measure.map (f ∘ Prod.fst)
          (gamma.plan : Measure (X × Y)) =
        Measure.map f (mu : Measure X)
    rw [← Measure.map_map hf measurable_fst]
    have hfirst :
        Measure.map Prod.fst
            (gamma.plan : Measure (X × Y)) =
          (mu : Measure X) := by
      simpa [firstMarginal, FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure X => (eta : Measure X))
        gamma.property.1
    rw [hfirst]
  · apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.snd
          (Measure.map (Prod.map f g)
            (gamma.plan : Measure (X × Y))) =
        Measure.map g (nu : Measure Y)
    rw [Measure.map_map measurable_snd (hf.prodMap hg)]
    change
      Measure.map (g ∘ Prod.snd)
          (gamma.plan : Measure (X × Y)) =
        Measure.map g (nu : Measure Y)
    rw [← Measure.map_map hg measurable_snd]
    have hsecond :
        Measure.map Prod.snd
            (gamma.plan : Measure (X × Y)) =
          (nu : Measure Y) := by
      simpa [secondMarginal, FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure Y => (eta : Measure Y))
        gamma.property.2
    rw [hsecond]

@[simp]
theorem mapFiniteCoupling_plan
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (f : X -> X') (g : Y -> Y')
    (hf : Measurable f) (hg : Measurable g) :
    (mapFiniteCoupling gamma f g hf hg).plan =
      gamma.plan.map (Prod.map f g) :=
  rfl

theorem stochasticallyDominates_of_forwardFiniteCoupling
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gamma) :
    StochasticallyDominates nu mu := by
  intro r
  change
    (nu : Measure Real) (Iic r) ≤
      (mu : Measure Real) (Iic r)
  have hfirst :
      Measure.map Prod.fst
          (gamma.plan : Measure (Real × Real)) =
        (mu : Measure Real) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Real => (eta : Measure Real))
      gamma.property.1
  have hsecond :
      Measure.map Prod.snd
          (gamma.plan : Measure (Real × Real)) =
        (nu : Measure Real) := by
    simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Real => (eta : Measure Real))
      gamma.property.2
  rw [← hsecond, ← hfirst,
    Measure.map_apply measurable_snd measurableSet_Iic,
    Measure.map_apply measurable_fst measurableSet_Iic]
  apply measure_mono_ae
  filter_upwards [hForward] with z hz
  exact fun hzr => hz.trans hzr

theorem component_agreesWithMap_of_reconstruction
    {R E : Type*}
    [MeasurableSpace R] [MeasurableSpace E]
    [MeasurableEq E]
    (sigma : FiniteMeasure R)
    (component : Kernel R (E × E)) [IsMarkovKernel component]
    {mu nu : FiniteMeasure E}
    (gamma : FiniteCoupling mu nu)
    (T : E -> E) (hGraph : IsGraphPlan gamma T)
    (hreconstruct :
      component ∘ₘ (sigma : Measure R) =
        (gamma.plan : Measure (E × E))) :
    ∀ᵐ r ∂(sigma : Measure R),
      ∀ᵐ z ∂component r, z.2 = T z.1 := by
  obtain ⟨hT, hPlan⟩ := hGraph
  have hGlobal :
      ∀ᵐ z ∂(gamma.plan : Measure (E × E)),
        z.2 = T z.1 := by
    rw [hPlan]
    change
      ∀ᵐ z ∂Measure.map (fun x => (x, T x)) (mu : Measure E),
        z.2 = T z.1
    apply
      (ae_map_iff (measurable_id.prodMk hT).aemeasurable
        (measurableSet_eq_fun measurable_snd
          (hT.comp measurable_fst))).2
    exact Eventually.of_forall fun _ => rfl
  apply Measure.ae_ae_of_ae_comp
  rw [hreconstruct]
  exact hGlobal

end FiniteCouplingAdapters

/-! ## Maximal-ray specialization of the lifted construction -/

section MaximalRayLift

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

noncomputable def maximalRayTargetKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  D.canonicalTarget gamma

theorem maximalRayTargetKernel_isMarkovKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    IsMarkovKernel (maximalRayTargetKernel D gamma) :=
  D.canonicalTarget_isMarkovKernel gamma

theorem maximalRayTargetKernel_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    maximalRayTargetKernel D gamma
        ∘ₘ (D.sigma : Measure (OrientedOpenRay n)) =
      (nu : Measure (Euclidean n)) :=
  D.canonicalTarget_reconstruction gamma hSupported

theorem maximalRayTargetKernel_ae_eq_of_supported_witnesses
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma eta : FiniteCoupling mu nu)
    (hgamma : IsSupported gamma Gamma)
    (heta : IsSupported eta Gamma) :
    maximalRayTargetKernel D gamma
      =ᵐ[(D.sigma : Measure (OrientedOpenRay n))]
        maximalRayTargetKernel D eta :=
  D.canonicalTarget_ae_eq gamma eta hgamma heta

theorem supportedComponent_target_ae_eq_maximalRayTargetKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 gamma : FiniteCoupling mu nu)
    (hgamma0 : IsSupported gamma0 Gamma)
    (hgamma : IsSupported gamma Gamma) :
    (D.component gamma).map Prod.snd
      =ᵐ[(D.sigma : Measure (OrientedOpenRay n))]
        maximalRayTargetKernel D gamma0 :=
  D.target_ae_eq_canonicalTarget gamma0 gamma hgamma0 hgamma

noncomputable def maximalRayLiftedSource
    (D : MaximalRayKernelDisintegration n mu nu Gamma) :
    FiniteMeasure (OrientedOpenRay n × Euclidean n) := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  exact liftedKernelMarginal D.sigma D.source

noncomputable def maximalRayLiftedTarget
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu) :
    FiniteMeasure (OrientedOpenRay n × Euclidean n) := by
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  exact liftedKernelMarginal D.sigma (maximalRayTargetKernel D gamma)

theorem existsCanonicalRayLiftedMinimizer
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∃ gammaLift :
        FiniteCoupling
          (maximalRayLiftedSource D)
          (maximalRayLiftedTarget D gamma),
      IsMinimizerOn
        (liftedRayForwardCouplingSet
          (maximalRayLiftedSource D)
          (maximalRayLiftedTarget D gamma))
        (fun eta =>
          ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
            ∂(eta.plan :
              Measure
                ((OrientedOpenRay n × Euclidean n) ×
                  (OrientedOpenRay n × Euclidean n))))
        gammaLift := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    ∃ gammaLift :
        FiniteCoupling
          (liftedKernelMarginal D.sigma D.source)
          (liftedKernelMarginal D.sigma
            (maximalRayTargetKernel D gamma)),
      IsMinimizerOn
        (liftedRayForwardCouplingSet
          (liftedKernelMarginal D.sigma D.source)
          (liftedKernelMarginal D.sigma
            (maximalRayTargetKernel D gamma)))
        (fun eta =>
          ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
            ∂(eta.plan :
              Measure
                ((OrientedOpenRay n × Euclidean n) ×
                  (OrientedOpenRay n × Euclidean n))))
        gammaLift
  exact
    existsLiftedRayForwardKernelMinimizer_strictExponentialProfile
      D.sigma D.source (maximalRayTargetKernel D gamma)
      (D.component gamma)
      (D.component_map_fst_ae_eq_source gamma hSupported)
      (Eventually.of_forall fun _ => rfl)
      (maximalRayComponent_coordinate_forward_ae D gamma hSupported)

theorem existsCanonicalRayLiftedMinimizer_with_fiberwiseMinimality
    [Nonempty (OrientedOpenRay n)]
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hselection :
      RayForwardFiberwiseImprovementSelectionPremise
        D.sigma D.source (maximalRayTargetKernel D gamma)) :
    ∃ gammaLift :
        FiniteCoupling
          (maximalRayLiftedSource D)
          (maximalRayLiftedTarget D gamma),
      IsMinimizerOn
          (liftedRayForwardCouplingSet
            (maximalRayLiftedSource D)
            (maximalRayLiftedTarget D gamma))
          (fun eta =>
            ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
              ∂(eta.plan :
                Measure
                  ((OrientedOpenRay n × Euclidean n) ×
                    (OrientedOpenRay n × Euclidean n))))
          gammaLift ∧
        ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
          IsMinimizerOn
            (fiberCouplingSet D.source
              (maximalRayTargetKernel D gamma)
              (rayForwardFiberCarrier n) R)
            (fiberMeasureCost rayStrictExponentialFiberCost R)
            (componentKernelOfLiftedCoupling gammaLift R) := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    ∃ gammaLift :
        FiniteCoupling
          (liftedKernelMarginal D.sigma D.source)
          (liftedKernelMarginal D.sigma
            (maximalRayTargetKernel D gamma)),
      IsMinimizerOn
          (liftedRayForwardCouplingSet
            (liftedKernelMarginal D.sigma D.source)
            (liftedKernelMarginal D.sigma
              (maximalRayTargetKernel D gamma)))
          (fun eta =>
            ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
              ∂(eta.plan :
                Measure
                  ((OrientedOpenRay n × Euclidean n) ×
                    (OrientedOpenRay n × Euclidean n))))
          gammaLift ∧
        ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
          IsMinimizerOn
            (fiberCouplingSet D.source
              (maximalRayTargetKernel D gamma)
              (rayForwardFiberCarrier n) R)
            (fiberMeasureCost rayStrictExponentialFiberCost R)
            (componentKernelOfLiftedCoupling gammaLift R)
  exact
    existsLiftedRayForwardMinimizer_with_ae_fiberwiseMinimality
      D.sigma D.source (maximalRayTargetKernel D gamma)
      (D.component gamma)
      (D.component_map_fst_ae_eq_source gamma hSupported)
      (Eventually.of_forall fun _ => rfl)
      (maximalRayComponent_coordinate_forward_ae D gamma hSupported)
      hselection

noncomputable def assembledRaywiseCoupling
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    FiniteCoupling mu nu := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    FiniteCoupling
      (liftedKernelMarginal D.sigma D.source)
      (liftedKernelMarginal D.sigma
        (maximalRayTargetKernel D gamma)) at gammaLift
  exact
    unliftedLiftedCoupling D.sigma D.source
      (maximalRayTargetKernel D gamma)
      D.source_reconstruction
      (maximalRayTargetKernel_reconstruction D gamma hSupported)
      gammaLift

@[simp]
theorem assembledRaywiseCoupling_plan
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    (assembledRaywiseCoupling D gamma hSupported gammaLift).plan =
      gammaLift.plan.map dropLiftedLabels :=
  rfl

noncomputable def assembledRaywiseKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    FiniteCoupling
      (liftedKernelMarginal D.sigma D.source)
      (liftedKernelMarginal D.sigma
        (maximalRayTargetKernel D gamma)) at gammaLift
  exact unliftedSameLabelKernel gammaLift

@[simp]
theorem assembledRaywiseKernel_eq_componentKernelOfLiftedCoupling
    [Nonempty (OrientedOpenRay n)]
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    assembledRaywiseKernel D gamma gammaLift =
      componentKernelOfLiftedCoupling gammaLift :=
  rfl

theorem assembledRaywiseKernel_isMarkovKernel
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    FiniteCoupling
      (liftedKernelMarginal D.sigma D.source)
      (liftedKernelMarginal D.sigma
        (maximalRayTargetKernel D gamma)) at gammaLift
  exact unliftedSameLabelKernel_isMarkovKernel gammaLift

theorem assembledRaywiseKernel_map_fst_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    (assembledRaywiseKernel D gamma gammaLift).map Prod.fst
      =ᵐ[(D.sigma : Measure (OrientedOpenRay n))] D.source := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    FiniteCoupling
      (liftedKernelMarginal D.sigma D.source)
      (liftedKernelMarginal D.sigma
        (maximalRayTargetKernel D gamma)) at gammaLift
  change
    (unliftedSameLabelKernel gammaLift).map Prod.fst
      =ᵐ[(D.sigma : Measure (OrientedOpenRay n))] D.source
  exact
    unliftedSameLabelKernel_map_fst_ae
      D.sigma D.source (maximalRayTargetKernel D gamma) gammaLift

theorem assembledRaywiseKernel_map_snd_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n)) :
    (assembledRaywiseKernel D gamma gammaLift).map Prod.snd
      =ᵐ[(D.sigma : Measure (OrientedOpenRay n))]
        maximalRayTargetKernel D gamma := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    FiniteCoupling
      (liftedKernelMarginal D.sigma D.source)
      (liftedKernelMarginal D.sigma
        (maximalRayTargetKernel D gamma)) at gammaLift
  change
    IsSupported gammaLift (liftedRayForwardRelation n)
      at hLiftedForward
  change
    (unliftedSameLabelKernel gammaLift).map Prod.snd
      =ᵐ[(D.sigma : Measure (OrientedOpenRay n))]
        maximalRayTargetKernel D gamma
  apply unliftedSameLabelKernel_map_snd_ae
    D.sigma D.source (maximalRayTargetKernel D gamma) gammaLift
  exact hLiftedForward.mono
    (liftedRayForwardRelation_subset_sameLabel n)

theorem assembledRaywiseKernel_reconstruction
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) :
    assembledRaywiseKernel D gamma gammaLift
        ∘ₘ (D.sigma : Measure (OrientedOpenRay n)) =
      ((assembledRaywiseCoupling D gamma hSupported gammaLift).plan :
        Measure (Euclidean n × Euclidean n)) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  change
    FiniteCoupling
      (liftedKernelMarginal D.sigma D.source)
      (liftedKernelMarginal D.sigma
        (maximalRayTargetKernel D gamma)) at gammaLift
  change
    unliftedSameLabelKernel gammaLift
        ∘ₘ (D.sigma : Measure (OrientedOpenRay n)) =
      ((assembledRaywiseCoupling D gamma hSupported gammaLift).plan :
        Measure (Euclidean n × Euclidean n))
  exact
    unliftedSameLabelKernel_reconstructs_coupling
      D.sigma D.source (maximalRayTargetKernel D gamma)
      D.source_reconstruction
      (maximalRayTargetKernel_reconstruction D gamma hSupported)
      gammaLift

noncomputable def maximalRaySourceFiber
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (R : OrientedOpenRay n) :
    FiniteMeasure (Euclidean n) := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  exact ⟨D.source R, inferInstance⟩

noncomputable def maximalRayTargetFiber
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (R : OrientedOpenRay n) :
    FiniteMeasure (Euclidean n) := by
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  exact ⟨maximalRayTargetKernel D gamma R, inferInstance⟩

noncomputable def assembledRaywiseComponentFiber
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n) :
    FiniteMeasure (Euclidean n × Euclidean n) := by
  letI : IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  exact ⟨assembledRaywiseKernel D gamma gammaLift R, inferInstance⟩

@[simp]
theorem maximalRaySourceFiber_toMeasure
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (R : OrientedOpenRay n) :
    (maximalRaySourceFiber D R : Measure (Euclidean n)) =
      D.source R :=
  rfl

@[simp]
theorem maximalRayTargetFiber_toMeasure
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (R : OrientedOpenRay n) :
    (maximalRayTargetFiber D gamma R : Measure (Euclidean n)) =
      maximalRayTargetKernel D gamma R :=
  rfl

@[simp]
theorem assembledRaywiseComponentFiber_toMeasure
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n) :
    (assembledRaywiseComponentFiber D gamma gammaLift R :
        Measure (Euclidean n × Euclidean n)) =
      assembledRaywiseKernel D gamma gammaLift R :=
  rfl

theorem assembledRaywiseComponent_isCoupling_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n)) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R) := by
  filter_upwards
      [assembledRaywiseKernel_map_fst_ae D gamma gammaLift,
        assembledRaywiseKernel_map_snd_ae
          D gamma gammaLift hLiftedForward] with R hfst hsnd
  constructor
  · apply FiniteMeasure.toMeasure_injective
    simpa [firstMarginal, Kernel.map_apply _ measurable_fst] using hfst
  · apply FiniteMeasure.toMeasure_injective
    simpa [secondMarginal, Kernel.map_apply _ measurable_snd] using hsnd

theorem maximalRayTarget_on_ray_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ y ∂(maximalRayTargetFiber D gamma R :
          Measure (Euclidean n)),
        y ∈ closure R.carrier := by
  filter_upwards
      [D.component_endpoints_mem_closure_ae
        gamma hSupported] with R hR
  change
    ∀ᵐ y ∂(D.component gamma).map Prod.snd R,
      y ∈ closure R.carrier
  rw [Kernel.map_apply _ measurable_snd]
  apply
    (ae_map_iff measurable_snd.aemeasurable
      isClosed_closure.measurableSet).2
  exact hR.mono fun _ hz => hz.2

theorem assembledRaywiseComponent_on_ray_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n)) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(assembledRaywiseComponentFiber
          D gamma gammaLift R :
        Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier := by
  filter_upwards
      [assembledRaywiseComponent_isCoupling_ae
        D gamma gammaLift hLiftedForward,
        D.source_on_ray_ae,
        maximalRayTarget_on_ray_ae D gamma hSupported] with
      R hCoupling hSource hTarget
  let eta :
      FiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R) :=
    ⟨assembledRaywiseComponentFiber D gamma gammaLift R, hCoupling⟩
  have hSourceClosure :
      ∀ᵐ x ∂(maximalRaySourceFiber D R :
          Measure (Euclidean n)),
        x ∈ closure R.carrier :=
    hSource.mono fun _ hx => subset_closure hx
  obtain ⟨hfst, hsnd⟩ :=
    finiteCouplingMarginalAeTransfer eta hSourceClosure hTarget
  exact hfst.and hsnd

theorem rayPoint_rayCoordinate_eq_of_mem_closure
    (R : OrientedOpenRay n) {x : Euclidean n}
    (hx : x ∈ closure R.carrier) :
    R.point (rayCoordinate R x) = x := by
  let fixedPoints : Set (Euclidean n) :=
    {y | R.point (rayCoordinate R y) = y}
  have hClosed : IsClosed fixedPoints := by
    exact isClosed_eq
      ((OrientedOpenRay.continuous_point R).comp
        (continuous_rayCoordinate R))
      continuous_id
  have hCarrier : R.carrier ⊆ fixedPoints := by
    intro y hy
    obtain ⟨t, _htLower, _htUpper, rfl⟩ := hy
    change R.point (rayCoordinate R (R.point t)) = R.point t
    rw [rayCoordinate_point_apply]
  exact (closure_minimal hCarrier hClosed) hx

theorem maximalRayCoordinateMarginals_mutuallySingular_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hSingular : FiniteMutuallySingular mu nu) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      FiniteMutuallySingular
        ((maximalRaySourceFiber D R).map (rayCoordinate R))
        ((maximalRayTargetFiber D gamma R).map (rayCoordinate R)) := by
  obtain ⟨A, hA, hmu, hnu⟩ := hSingular
  have hSourceGlobal :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)), x ∈ A := by
    apply ae_iff.mpr
    exact hmu
  have hTargetGlobal :
      ∀ᵐ y ∂(nu : Measure (Euclidean n)), y ∉ A := by
    apply ae_iff.mpr
    simpa only [not_not, setOf_mem_eq] using hnu
  have hSourceFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ x ∂D.source R, x ∈ A := by
    apply Measure.ae_ae_of_ae_comp
    rw [D.source_reconstruction]
    exact hSourceGlobal
  have hTargetFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ y ∂maximalRayTargetKernel D gamma R, y ∉ A := by
    apply Measure.ae_ae_of_ae_comp
    rw [maximalRayTargetKernel_reconstruction D gamma hSupported]
    exact hTargetGlobal
  filter_upwards
      [hSourceFiber, hTargetFiber, D.source_on_ray_ae,
        maximalRayTarget_on_ray_ae D gamma hSupported] with
      R hSourceA hTargetA hSourceRay hTargetRay
  let B : Set Real := R.point ⁻¹' A
  have hB : MeasurableSet B :=
    hA.preimage (OrientedOpenRay.continuous_point R).measurable
  refine ⟨B, hB, ?_, ?_⟩
  · have hMapped :
        ∀ᵐ t ∂(((maximalRaySourceFiber D R).map
            (rayCoordinate R) : FiniteMeasure Real) : Measure Real),
          t ∈ B := by
      change
        ∀ᵐ t ∂Measure.map (rayCoordinate R) (D.source R),
          t ∈ B
      apply
        (ae_map_iff (measurable_rayCoordinate R).aemeasurable hB).2
      filter_upwards [hSourceA, hSourceRay] with x hxA hxRay
      rw [rayPoint_rayCoordinate_eq_of_mem_closure R
        (subset_closure hxRay)]
      exact hxA
    exact ae_iff.mp hMapped
  · have hMapped :
        ∀ᵐ t ∂(((maximalRayTargetFiber D gamma R).map
            (rayCoordinate R) : FiniteMeasure Real) : Measure Real),
          t ∉ B := by
      change
        ∀ᵐ t ∂Measure.map (rayCoordinate R)
            (maximalRayTargetKernel D gamma R),
          t ∉ B
      apply
        (ae_map_iff (measurable_rayCoordinate R).aemeasurable
          hB.compl).2
      filter_upwards [hTargetA, hTargetRay] with y hyA hyRay
      change R.point (rayCoordinate R y) ∉ A
      rw [rayPoint_rayCoordinate_eq_of_mem_closure R hyRay]
      exact hyA
    simpa only [not_not, setOf_mem_eq] using (ae_iff.mp hMapped)

theorem assembledRaywiseCoordinateTargetDominates
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hComponentCoupling :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsFiniteCoupling
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R)
          (assembledRaywiseComponentFiber D gamma gammaLift R))
    (hForward :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂(assembledRaywiseComponentFiber
            D gamma gammaLift R :
          Measure (Euclidean n × Euclidean n)),
          rayCoordinate R z.1 ≤ rayCoordinate R z.2) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      StochasticallyDominates
        ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
        ((maximalRaySourceFiber D R).map (rayCoordinate R)) := by
  filter_upwards [hComponentCoupling, hForward] with R hCoupling hR
  let eta :
      FiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R) :=
    ⟨assembledRaywiseComponentFiber D gamma gammaLift R, hCoupling⟩
  let etaCoordinate :
      FiniteCoupling
        ((maximalRaySourceFiber D R).map (rayCoordinate R))
        ((maximalRayTargetFiber D gamma R).map (rayCoordinate R)) :=
    mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
      (measurable_rayCoordinate R) (measurable_rayCoordinate R)
  have hCoordinateForward : IsForwardPlan etaCoordinate := by
    change
      ∀ᵐ z ∂Measure.map
          (Prod.map (rayCoordinate R) (rayCoordinate R))
          (assembledRaywiseComponentFiber D gamma gammaLift R :
            Measure (Euclidean n × Euclidean n)),
        z.1 ≤ z.2
    apply
      (ae_map_iff
        ((measurable_rayCoordinate R).prodMap
          (measurable_rayCoordinate R)).aemeasurable
        (measurableSet_le measurable_fst measurable_snd)).2
    exact hR
  exact stochasticallyDominates_of_forwardFiniteCoupling
    etaCoordinate hCoordinateForward

theorem maximalRaySource_coordinateAtomless
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsAtomlessFinite
        ((maximalRaySourceFiber D R).map (rayCoordinate R)) := by
  have hAtomless :=
    rayConditionalAtomlessness_of_countablyLipschitzCoarea
      D.transportSet_measurable D.diagonalFree hRegularity
      D.rayAssignment D.rayAssignment_measurable
      D.rayAssignment_isMaximal D.defaultRay gamma hSupported
      hmuAC hCoarea
  simpa [MaximalRayKernelDisintegration.sigma,
    MaximalRayKernelDisintegration.pointRay,
    MaximalRayKernelDisintegration.source,
    maximalRaySourceFiber,
    canonicalRaySourceConditional,
    canonicalRaySourceKernel] using hAtomless

theorem assembledRaywiseComponent_coordinate_forward_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n)) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(assembledRaywiseComponentFiber
          D gamma gammaLift R :
        Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 ≤ rayCoordinate R z.2 := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  have hCarrier :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂componentKernelOfLiftedCoupling gammaLift R,
          (R, z) ∈ rayForwardFiberCarrier n := by
    apply componentKernelOfLiftedCoupling_carrier_ae
      D.sigma D.source gammaLift
      (measurableSet_rayForwardFiberCarrier n)
    simpa only [liftedFiberCarrier_rayForwardFiberCarrier] using
      hLiftedForward
  simpa only [assembledRaywiseComponentFiber_toMeasure,
    assembledRaywiseKernel_eq_componentKernelOfLiftedCoupling,
    rayForwardFiberCarrier, mem_setOf_eq] using hCarrier

theorem existsRaywiseExcursionDisintegration_of_assembled
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (transportMap : Euclidean n -> Euclidean n)
    (hGraph :
      IsGraphPlan
        (assembledRaywiseCoupling D gamma hSupported gammaLift)
        transportMap)
    (hAtomless :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsAtomlessFinite
          ((maximalRaySourceFiber D R).map (rayCoordinate R)))
    (hSingular :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        FiniteMutuallySingular
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R)))
    (hExcursion :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          ((assembledRaywiseComponentFiber D gamma gammaLift R).map
            fun z =>
              (rayCoordinate R z.1, rayCoordinate R z.2))) :
    Nonempty
      (RaywiseExcursionDisintegration
        Gamma mu nu
        (assembledRaywiseCoupling D gamma hSupported gammaLift).plan
        transportMap) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  letI : IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  have hComponentCoupling :=
    assembledRaywiseComponent_isCoupling_ae
      D gamma gammaLift hLiftedForward
  have hComponentForward :=
    assembledRaywiseComponent_coordinate_forward_ae
      D gamma gammaLift hLiftedForward
  have hTargetDominates :=
    assembledRaywiseCoordinateTargetDominates
      D gamma gammaLift hComponentCoupling hComponentForward
  refine ⟨{
    sigma := D.sigma
    source := maximalRaySourceFiber D
    target := maximalRayTargetFiber D gamma
    component := assembledRaywiseComponentFiber D gamma gammaLift
    sourceEvaluationMeasurable := ?_
    targetEvaluationMeasurable := ?_
    componentEvaluationMeasurable := ?_
    sourceReconstruction := ?_
    targetReconstruction := ?_
    planReconstruction := ?_
    rayIsMaximal := D.ray_isMaximal_ae
    componentIsCoupling := hComponentCoupling
    componentOnRay :=
      assembledRaywiseComponent_on_ray_ae
        D gamma hSupported gammaLift hLiftedForward
    componentAgreesWithMap :=
      component_agreesWithMap_of_reconstruction
        D.sigma (assembledRaywiseKernel D gamma gammaLift)
        (assembledRaywiseCoupling D gamma hSupported gammaLift)
        transportMap hGraph
        (assembledRaywiseKernel_reconstruction
          D gamma hSupported gammaLift)
    coordinateSourceAtomless := hAtomless
    coordinateMarginalsMutuallySingular := hSingular
    coordinateTargetDominates := hTargetDominates
    coordinateComponentForward := hComponentForward
    componentIsExcursion := hExcursion
  }⟩
  · intro s hs
    exact Kernel.measurable_coe D.source hs
  · intro s hs
    exact Kernel.measurable_coe (maximalRayTargetKernel D gamma) hs
  · intro s hs
    exact
      Kernel.measurable_coe
        (assembledRaywiseKernel D gamma gammaLift) hs
  · intro s hs
    have h := congrArg (fun rho : Measure (Euclidean n) => rho s)
      D.source_reconstruction
    change
      (D.source ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) s =
        (mu : Measure (Euclidean n)) s at h
    rw [Measure.bind_apply hs (Kernel.aemeasurable D.source)] at h
    simpa only [maximalRaySourceFiber_toMeasure] using h.symm
  · intro s hs
    have h := congrArg (fun rho : Measure (Euclidean n) => rho s)
      (maximalRayTargetKernel_reconstruction
        D gamma hSupported)
    change
      (maximalRayTargetKernel D gamma ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) s =
        (nu : Measure (Euclidean n)) s at h
    rw [Measure.bind_apply hs
      (Kernel.aemeasurable (maximalRayTargetKernel D gamma))] at h
    simpa only [maximalRayTargetFiber_toMeasure] using h.symm
  · intro s hs
    have h := congrArg
      (fun rho : Measure (Euclidean n × Euclidean n) => rho s)
      (assembledRaywiseKernel_reconstruction
        D gamma hSupported gammaLift)
    change
      (assembledRaywiseKernel D gamma gammaLift ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) s =
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)) s at h
    rw [Measure.bind_apply hs
      (Kernel.aemeasurable
        (assembledRaywiseKernel D gamma gammaLift))] at h
    simpa only [assembledRaywiseComponentFiber_toMeasure] using h.symm

theorem assembledRaywiseCoupling_supported_sameMaximalRayClosure
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hSameRayMeasurable :
      MeasurableSet
        {z : Euclidean n × Euclidean n |
          SameMaximalRayClosure Gamma z.1 z.2}) :
    IsSupported
      (assembledRaywiseCoupling D gamma hSupported gammaLift)
      {z | SameMaximalRayClosure Gamma z.1 z.2} := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  letI : IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  have hFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂assembledRaywiseKernel D gamma gammaLift R,
          SameMaximalRayClosure Gamma z.1 z.2 := by
    filter_upwards
        [D.ray_isMaximal_ae,
          assembledRaywiseComponent_on_ray_ae
            D gamma hSupported gammaLift hLiftedForward] with
        R hMaximal hOnRay
    filter_upwards [hOnRay] with z hz
    exact ⟨R, hMaximal, hz⟩
  change
    ∀ᵐ z ∂((assembledRaywiseCoupling
        D gamma hSupported gammaLift).plan :
      Measure (Euclidean n × Euclidean n)),
      SameMaximalRayClosure Gamma z.1 z.2
  rw [← assembledRaywiseKernel_reconstruction
    D gamma hSupported gammaLift]
  exact Measure.ae_comp_of_ae_ae hSameRayMeasurable hFiber

end MaximalRayLift

/-! ## Exact residual boundary and paper-statement assembly -/

section AssemblyBoundary

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

def IsCanonicalRayLiftedMinimizer
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) : Prop :=
  IsMinimizerOn
    (liftedRayForwardCouplingSet
      (maximalRayLiftedSource D)
      (maximalRayLiftedTarget D gamma))
    (fun eta =>
      ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
        ∂(eta.plan :
          Measure
            ((OrientedOpenRay n × Euclidean n) ×
              (OrientedOpenRay n × Euclidean n))))
    gammaLift

def CanonicalRayFiberMinimality
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) : Prop :=
  ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
    IsMinimizerOn
      (fiberCouplingSet D.source
        (maximalRayTargetKernel D gamma)
        (rayForwardFiberCarrier n) R)
      (fiberMeasureCost rayStrictExponentialFiberCost R)
      (assembledRaywiseKernel D gamma gammaLift R)

/-- Inputs still missing after maximal-ray disintegration, canonical endpoint
allocation, lifted minimizer localization, atomlessness, and ray geometry have
all been applied to one selected lifted minimizer. -/
structure CanonicalRaywiseReplacementResidualInputs
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma)) : Prop where
  sameRayClosureMeasurable :
    MeasurableSet
      {z : Euclidean n × Euclidean n |
        SameMaximalRayClosure Gamma z.1 z.2}
  fiberMinimalityIdentifiesExcursion :
    CanonicalRayFiberMinimality D gamma gammaLift ->
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          ((assembledRaywiseComponentFiber D gamma gammaLift R).map
            fun z =>
              (rayCoordinate R z.1, rayCoordinate R z.2))
  conditionalDeterminism :
    IsDeterministic
      (condDistrib Prod.snd Prod.fst
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)))
  cyclicDistanceOptimal :
    IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
      IsDistanceOptimal
        (assembledRaywiseCoupling D gamma hSupported gammaLift)
  profileComparison :
    ∀ eta : FiniteCoupling mu nu,
      IsSupported eta Gamma ->
        ∀ profile : Real -> Real,
          AdmissibleConcaveProfile profile ->
            profileCost profile
                (assembledRaywiseCoupling
                  D gamma hSupported gammaLift) <=
              profileCost profile eta
  strictProfileRigidity :
    ∀ eta : FiniteCoupling mu nu,
      IsSupported eta Gamma ->
        ∀ profile : Real -> Real,
          AdmissibleStrictlyConcaveProfile profile ->
            profileCost profile
                (assembledRaywiseCoupling
                  D gamma hSupported gammaLift) =
                profileCost profile eta ->
              eta =
                assembledRaywiseCoupling
                  D gamma hSupported gammaLift

/-- Uniform premise needed to close the paper theorem from its stated inputs.
The first two fields are the exact local analytic gaps; `residual` supplies
the six post-selection inputs recorded above. -/
structure CanonicalRaywiseReplacementAssemblyPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma) : Prop where
  coarea :
    ∀ D : MaximalRayKernelDisintegration n mu nu Gamma,
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay
  fiberSelection :
    ∀ (gamma : FiniteCoupling mu nu),
      IsSupported gamma Gamma ->
        ∀ D : MaximalRayKernelDisintegration n mu nu Gamma,
          MaximalRayKernelDisintegration.CanonicalRayForwardRationalGapMeasurableSelectionPremise
            D gamma
  residual :
    ∀ (gamma : FiniteCoupling mu nu)
      (hSupported : IsSupported gamma Gamma)
      (D : MaximalRayKernelDisintegration n mu nu Gamma)
      (gammaLift :
        FiniteCoupling
          (maximalRayLiftedSource D)
          (maximalRayLiftedTarget D gamma)),
      IsCanonicalRayLiftedMinimizer D gamma gammaLift ->
        CanonicalRaywiseReplacementResidualInputs
          D gamma hSupported gammaLift

theorem canonicalRaywiseReplacement_of_assemblyPremise
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
      ∃ gamma : FiniteCoupling mu nu, IsSupported gamma Gamma)
    (hAssembly :
      CanonicalRaywiseReplacementAssemblyPremise
        n mu nu Gamma hRegularity) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
        (IsDistanceCyclicallyMonotone.{0, 0} Gamma ->
          IsDistanceOptimal gammaSharp) /\
        IsSupported gammaSharp
          {z | SameMaximalRayClosure Gamma z.1 z.2} /\
        Nonempty
          (RaywiseExcursionDisintegration
            Gamma mu nu gammaSharp.plan tSharp) /\
        ∀ gamma : FiniteCoupling mu nu,
          IsSupported gamma Gamma ->
            ∀ profile : Real -> Real,
              AdmissibleConcaveProfile profile ->
                profileCost profile gammaSharp <=
                  profileCost profile gamma /\
                (AdmissibleStrictlyConcaveProfile profile ->
                  (profileCost profile gammaSharp =
                    profileCost profile gamma <-> gamma = gammaSharp)) := by
  obtain ⟨gamma, hSupported⟩ := hInput
  let D : MaximalRayKernelDisintegration n mu nu Gamma :=
    Classical.choice
      (existsMaximalRayKernelDisintegration
        n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
        ⟨gamma, hSupported⟩)
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  obtain ⟨gammaLift, hGlobal, hFiberRaw⟩ :=
    existsCanonicalRayLiftedMinimizer_with_fiberwiseMinimality
      D gamma hSupported
      (D.rayForwardFiberwiseImprovementSelectionPremise_of_canonical
        gamma (hAssembly.fiberSelection gamma hSupported D))
  have hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n) :=
    hGlobal.1
  have hFiber :
      CanonicalRayFiberMinimality D gamma gammaLift := by
    unfold CanonicalRayFiberMinimality
    simpa only
        [assembledRaywiseKernel_eq_componentKernelOfLiftedCoupling] using
      hFiberRaw
  have hGlobal' :
      IsCanonicalRayLiftedMinimizer D gamma gammaLift :=
    hGlobal
  let residual :
      CanonicalRaywiseReplacementResidualInputs
        D gamma hSupported gammaLift :=
    hAssembly.residual gamma hSupported D gammaLift hGlobal'
  have hExcursion :=
    residual.fiberMinimalityIdentifiesExcursion hFiber
  have hAtomless :=
    maximalRaySource_coordinateAtomless
      D hRegularity gamma hSupported
      hMarginals.sourceAbsolutelyContinuous
      (hAssembly.coarea D)
  have hSingular :=
    maximalRayCoordinateMarginals_mutuallySingular_ae
      D gamma hSupported hMarginals.mutuallySingular
  let gammaSharp : FiniteCoupling mu nu :=
    assembledRaywiseCoupling D gamma hSupported gammaLift
  obtain ⟨tSharp, hGraph⟩ :=
    existsGraphPlan_of_isDeterministic_condDistrib
      gammaSharp residual.conditionalDeterminism
  have hSameRay :
      IsSupported gammaSharp
        {z | SameMaximalRayClosure Gamma z.1 z.2} :=
    assembledRaywiseCoupling_supported_sameMaximalRayClosure
      D gamma hSupported gammaLift hLiftedForward
      residual.sameRayClosureMeasurable
  have hDisintegration :
      Nonempty
        (RaywiseExcursionDisintegration
          Gamma mu nu gammaSharp.plan tSharp) := by
    exact
      existsRaywiseExcursionDisintegration_of_assembled
        D gamma hSupported gammaLift hLiftedForward
        tSharp hGraph hAtomless hSingular hExcursion
  refine
    ⟨gammaSharp, tSharp, hGraph,
      residual.cyclicDistanceOptimal, hSameRay,
      hDisintegration, ?_⟩
  intro eta hEta profile hProfile
  refine
    ⟨residual.profileComparison eta hEta profile hProfile, ?_⟩
  intro hStrict
  constructor
  · intro hCost
    exact residual.strictProfileRigidity
      eta hEta profile hStrict hCost
  · intro hEq
    rw [hEq]

end AssemblyBoundary

end ConcaveOTLimit
