import Theorems.Thm_ConcaveOTLimit_raywiseCoordinateInheritance
import Theorems.Thm_ConcaveOTLimit_distanceCostEqMomentDifferenceIffForward
import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open Filter MeasureTheory ProbabilityTheory Set

open scoped MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

noncomputable def maximalRayInputComponentFiber
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (R : OrientedOpenRay n) :
    FiniteMeasure (Euclidean n × Euclidean n) := by
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  exact ⟨D.component gamma R, inferInstance⟩

@[simp]
theorem maximalRayInputComponentFiber_toMeasure
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (R : OrientedOpenRay n) :
    (maximalRayInputComponentFiber D gamma R :
        Measure (Euclidean n × Euclidean n)) =
      D.component gamma R :=
  rfl

theorem maximalRayInputComponent_isCoupling_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (maximalRayInputComponentFiber D gamma R) := by
  filter_upwards
      [D.component_map_fst_ae_eq_source gamma hSupported,
        supportedComponent_target_ae_eq_maximalRayTargetKernel
          D gamma gamma hSupported hSupported] with R hfst hsnd
  constructor
  · apply FiniteMeasure.toMeasure_injective
    simpa [firstMarginal, Kernel.map_apply _ measurable_fst] using hfst
  · apply FiniteMeasure.toMeasure_injective
    simpa [secondMarginal, Kernel.map_apply _ measurable_snd] using hsnd

private theorem norm_rayPoint_sub_eq
    (R : OrientedOpenRay n) (s t : Real) :
    ‖R.point s - R.point t‖ = ‖s - t‖ := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  simp only [OrientedOpenRay.point, add_sub_add_left_eq_sub, ← sub_smul,
    norm_smul, hnorm, mul_one, Real.norm_eq_abs]

private theorem norm_sub_eq_norm_rayCoordinate_sub
    (R : OrientedOpenRay n) {x y : Euclidean n}
    (hx : x ∈ closure R.carrier)
    (hy : y ∈ closure R.carrier) :
    ‖x - y‖ = ‖rayCoordinate R x - rayCoordinate R y‖ := by
  calc
    ‖x - y‖ =
        ‖R.point (rayCoordinate R x) -
          R.point (rayCoordinate R y)‖ := by
      rw [rayPoint_rayCoordinate_eq_of_mem_closure R hx,
        rayPoint_rayCoordinate_eq_of_mem_closure R hy]
    _ = ‖rayCoordinate R x - rayCoordinate R y‖ :=
      norm_rayPoint_sub_eq R _ _

theorem distanceCost_mapFiniteCoupling_rayCoordinate_eq
    (R : OrientedOpenRay n)
    {source target : FiniteMeasure (Euclidean n)}
    (eta : FiniteCoupling source target)
    (hOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier) :
    distanceCost
        (mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R) (measurable_rayCoordinate R)) =
      distanceCost eta := by
  unfold distanceCost profileCost
  simp only [id_eq, mapFiniteCoupling_plan, FiniteMeasure.toMeasure_map]
  have hNormMeasurable :
      AEStronglyMeasurable
        (fun z : Real × Real => ‖z.1 - z.2‖)
        (Measure.map
          (Prod.map (rayCoordinate R) (rayCoordinate R))
          (eta.plan : Measure (Euclidean n × Euclidean n))) :=
    (continuous_norm.comp
      (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  rw [integral_map
    (μ := (eta.plan : Measure (Euclidean n × Euclidean n)))
    ((measurable_rayCoordinate R).prodMap
      (measurable_rayCoordinate R)).aemeasurable
    hNormMeasurable]
  apply integral_congr_ae
  filter_upwards [hOnRay] with z hz
  change
    ‖rayCoordinate R z.1 - rayCoordinate R z.2‖ =
      ‖z.1 - z.2‖
  exact (norm_sub_eq_norm_rayCoordinate_sub R hz.1 hz.2).symm

theorem mapFiniteCoupling_rayCoordinate_isForward
    (R : OrientedOpenRay n)
    {source target : FiniteMeasure (Euclidean n)}
    (eta : FiniteCoupling source target)
    (hForward :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 ≤ rayCoordinate R z.2) :
    IsForwardPlan
      (mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
        (measurable_rayCoordinate R) (measurable_rayCoordinate R)) := by
  change
    ∀ᵐ z ∂Measure.map
        (Prod.map (rayCoordinate R) (rayCoordinate R))
        (eta.plan : Measure (Euclidean n × Euclidean n)),
      z.1 ≤ z.2
  exact
    (ae_map_iff
      ((measurable_rayCoordinate R).prodMap
        (measurable_rayCoordinate R)).aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).2 hForward

private theorem fiber_distanceCost_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n)
    (hInputCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (maximalRayInputComponentFiber D gamma R))
    (hAssembledCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R))
    (hInputOnRay :
      ∀ᵐ z ∂(maximalRayInputComponentFiber D gamma R :
          Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hAssembledOnRay :
      ∀ᵐ z ∂(assembledRaywiseComponentFiber D gamma gammaLift R :
          Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hInputForward :
      ∀ᵐ z ∂(maximalRayInputComponentFiber D gamma R :
          Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (hAssembledForward :
      ∀ᵐ z ∂(assembledRaywiseComponentFiber D gamma gammaLift R :
          Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (hSourceFirst :
      Integrable (fun t : Real => |t|)
        (maximalRayCoordinateSource D R : Measure Real))
    (hTargetFirst :
      Integrable (fun t : Real => |t|)
        (maximalRayCoordinateTarget D gamma R : Measure Real)) :
    distanceCost
        (⟨maximalRayInputComponentFiber D gamma R,
          hInputCoupling⟩ :
          FiniteCoupling
            (maximalRaySourceFiber D R)
            (maximalRayTargetFiber D gamma R)) =
      distanceCost
        (⟨assembledRaywiseComponentFiber D gamma gammaLift R,
          hAssembledCoupling⟩ :
          FiniteCoupling
            (maximalRaySourceFiber D R)
            (maximalRayTargetFiber D gamma R)) := by
  let etaInput :
      FiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R) :=
    ⟨maximalRayInputComponentFiber D gamma R, hInputCoupling⟩
  let etaAssembled :
      FiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R) :=
    ⟨assembledRaywiseComponentFiber D gamma gammaLift R,
      hAssembledCoupling⟩
  let coordinateInput :=
    mapFiniteCoupling etaInput (rayCoordinate R) (rayCoordinate R)
      (measurable_rayCoordinate R) (measurable_rayCoordinate R)
  let coordinateAssembled :=
    mapFiniteCoupling etaAssembled (rayCoordinate R) (rayCoordinate R)
      (measurable_rayCoordinate R) (measurable_rayCoordinate R)
  have hSource :
      Integrable (fun t : Real => t)
        (maximalRayCoordinateSource D R : Measure Real) := by
    apply
      (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hSourceFirst
  have hTarget :
      Integrable (fun t : Real => t)
        (maximalRayCoordinateTarget D gamma R : Measure Real) := by
    apply
      (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hTargetFirst
  have hInputCoordinateForward : IsForwardPlan coordinateInput :=
    mapFiniteCoupling_rayCoordinate_isForward R etaInput hInputForward
  have hAssembledCoordinateForward : IsForwardPlan coordinateAssembled :=
    mapFiniteCoupling_rayCoordinate_isForward R etaAssembled
      hAssembledForward
  change distanceCost etaInput = distanceCost etaAssembled
  calc
    distanceCost etaInput = distanceCost coordinateInput :=
      (distanceCost_mapFiniteCoupling_rayCoordinate_eq
        R etaInput hInputOnRay).symm
    _ =
        (integral
          (maximalRayCoordinateTarget D gamma R : Measure Real)
          fun t => t) -
        integral
          (maximalRayCoordinateSource D R : Measure Real)
          fun t => t :=
      (distanceCostEqMomentDifferenceIffForward
        coordinateInput hSource hTarget).2 hInputCoordinateForward
    _ = distanceCost coordinateAssembled :=
      ((distanceCostEqMomentDifferenceIffForward
        coordinateAssembled hSource hTarget).2
          hAssembledCoordinateForward).symm
    _ = distanceCost etaAssembled :=
      distanceCost_mapFiniteCoupling_rayCoordinate_eq
        R etaAssembled hAssembledOnRay

private theorem integral_comp_eq_integral_fiber
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (sigma : Measure R)
    (kappa : Kernel R X)
    (rho : Measure X)
    (hreconstruct : kappa ∘ₘ sigma = rho)
    (f : X -> Real)
    (hf : Integrable f rho) :
    (∫ x, f x ∂rho) =
      ∫ r, ∫ x, f x ∂kappa r ∂sigma := by
  have hcomp : Integrable f (kappa ∘ₘ sigma) := by
    rw [hreconstruct]
    exact hf
  rw [← hreconstruct, Measure.comp_eq_comp_const_apply]
  simpa only [Kernel.const_apply] using
    (Kernel.integral_comp
      (η := kappa) (κ := Kernel.const Unit sigma) (a := ())
      hcomp)

/-- Replacing every conditional component by an arbitrary forward coupling
of the same raywise marginals preserves the global distance cost. -/
theorem assembledRaywiseCoupling_distanceCost_eq
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hSourceFirst :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetFirst :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    distanceCost
        (assembledRaywiseCoupling D gamma hSupported gammaLift) =
      distanceCost gamma := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  letI : IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  have hInputCoupling :=
    maximalRayInputComponent_isCoupling_ae D gamma hSupported
  have hAssembledCoupling :=
    assembledRaywiseComponent_isCoupling_ae
      D gamma gammaLift hLiftedForward
  have hInputOnRay :=
    D.component_endpoints_mem_closure_ae gamma hSupported
  have hAssembledOnRay :=
    assembledRaywiseComponent_on_ray_ae
      D gamma hSupported gammaLift hLiftedForward
  have hInputForward :=
    maximalRayComponent_coordinate_forward_ae D gamma hSupported
  have hAssembledForward :=
    assembledRaywiseComponent_coordinate_forward_ae
      D gamma gammaLift hLiftedForward
  have hSourceCoordinateFirst :=
    maximalRayCoordinateSource_firstMoment_ae D hSourceFirst
  have hTargetCoordinateFirst :=
    maximalRayCoordinateTarget_firstMoment_ae
      D gamma hSupported hTargetFirst
  have hFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        (∫ z, dist z.1 z.2 ∂D.component gamma R) =
          ∫ z, dist z.1 z.2
            ∂assembledRaywiseKernel D gamma gammaLift R := by
    filter_upwards
        [hInputCoupling, hAssembledCoupling, hInputOnRay,
          hAssembledOnRay, hInputForward, hAssembledForward,
          hSourceCoordinateFirst, hTargetCoordinateFirst] with
        R hInputCpl hAssembledCpl hInputRay hAssembledRay
          hInputFwd hAssembledFwd hSource hTarget
    have hCost :=
      fiber_distanceCost_eq D gamma gammaLift R
        hInputCpl hAssembledCpl hInputRay hAssembledRay
        hInputFwd hAssembledFwd hSource hTarget
    simpa [distanceCost, profileCost, dist_eq_norm] using hCost
  have hInputIntegrable :
      Integrable (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
    simpa only [dist_eq_norm] using
      distanceIntegrableOfMarginalFirstMoments
        hSourceFirst hTargetFirst gamma
  have hAssembledIntegrable :
      Integrable (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)) := by
    simpa only [dist_eq_norm] using
      distanceIntegrableOfMarginalFirstMoments
        hSourceFirst hTargetFirst
        (assembledRaywiseCoupling D gamma hSupported gammaLift)
  have hInputIntegral :
      (∫ z, dist z.1 z.2
          ∂(gamma.plan : Measure (Euclidean n × Euclidean n))) =
        ∫ R, ∫ z, dist z.1 z.2 ∂D.component gamma R
          ∂(D.sigma : Measure (OrientedOpenRay n)) :=
    integral_comp_eq_integral_fiber
      (D.sigma : Measure (OrientedOpenRay n))
      (D.component gamma)
      (gamma.plan : Measure (Euclidean n × Euclidean n))
      (D.component_reconstruction gamma hSupported)
      (fun z => dist z.1 z.2) hInputIntegrable
  have hAssembledIntegral :
      (∫ z, dist z.1 z.2
          ∂((assembledRaywiseCoupling
            D gamma hSupported gammaLift).plan :
              Measure (Euclidean n × Euclidean n))) =
        ∫ R, ∫ z, dist z.1 z.2
            ∂assembledRaywiseKernel D gamma gammaLift R
          ∂(D.sigma : Measure (OrientedOpenRay n)) :=
    integral_comp_eq_integral_fiber
      (D.sigma : Measure (OrientedOpenRay n))
      (assembledRaywiseKernel D gamma gammaLift)
      ((assembledRaywiseCoupling
        D gamma hSupported gammaLift).plan :
          Measure (Euclidean n × Euclidean n))
      (assembledRaywiseKernel_reconstruction
        D gamma hSupported gammaLift)
      (fun z => dist z.1 z.2) hAssembledIntegrable
  change
    (∫ z, dist z.1 z.2
      ∂((assembledRaywiseCoupling
        D gamma hSupported gammaLift).plan :
          Measure (Euclidean n × Euclidean n))) =
      ∫ z, dist z.1 z.2
        ∂(gamma.plan : Measure (Euclidean n × Euclidean n))
  rw [hAssembledIntegral, hInputIntegral]
  apply integral_congr_ae
  filter_upwards [hFiber] with R hR
  exact hR.symm

/-- Distance optimality transfers from the supported input coupling to its
forward raywise replacement. -/
theorem assembledRaywiseCoupling_isDistanceOptimal_of_input
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hSourceFirst :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetFirst :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hOptimal : IsDistanceOptimal gamma) :
    IsDistanceOptimal
      (assembledRaywiseCoupling D gamma hSupported gammaLift) := by
  refine ⟨mem_univ _, ?_⟩
  intro eta _heta
  change
    distanceCost
        (assembledRaywiseCoupling D gamma hSupported gammaLift) ≤
      distanceCost eta
  rw [assembledRaywiseCoupling_distanceCost_eq
    D gamma hSupported gammaLift hLiftedForward
    hSourceFirst hTargetFirst]
  exact hOptimal.2 eta (mem_univ eta)

end ConcaveOTLimit
