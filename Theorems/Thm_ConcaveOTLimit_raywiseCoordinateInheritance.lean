import Theorems.Thm_ConcaveOTLimit_rayCoarea
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Coordinate fibers -/

noncomputable def maximalRayCoordinateSource
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (R : OrientedOpenRay n) :
    FiniteMeasure Real :=
  (maximalRaySourceFiber D R).map (rayCoordinate R)

noncomputable def maximalRayCoordinateTarget
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (R : OrientedOpenRay n) :
    FiniteMeasure Real :=
  (maximalRayTargetFiber D gamma R).map (rayCoordinate R)

noncomputable def assembledRaywiseCoordinateComponent
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n) :
    FiniteMeasure (Real × Real) :=
  (assembledRaywiseComponentFiber D gamma gammaLift R).map
    (Prod.map (rayCoordinate R) (rayCoordinate R))

/-- The properties inherited by the coordinate pushforwards on one maximal
ray. The strict-exponential profile is global, so its admissibility is stated
separately below. -/
structure RaywiseCoordinateInheritance
    {n : Nat} (Gamma : Set (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (component : FiniteMeasure (Euclidean n × Euclidean n)) : Prop where
  rayIsMaximal : R.IsMaximalTransportRay Gamma
  componentOnRay :
    ∀ᵐ z ∂(component : Measure (Euclidean n × Euclidean n)),
      z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier
  coordinateIsCoupling :
    IsFiniteCoupling
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R))
      (component.map
        (Prod.map (rayCoordinate R) (rayCoordinate R)))
  coordinateSourceAtomless :
    IsAtomlessFinite (source.map (rayCoordinate R))
  coordinateMarginalsMutuallySingular :
    FiniteMutuallySingular
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R))
  coordinateTargetDominates :
    StochasticallyDominates
      (target.map (rayCoordinate R))
      (source.map (rayCoordinate R))
  coordinateComponentForward :
    ∀ᵐ z ∂(component.map
        (Prod.map (rayCoordinate R) (rayCoordinate R)) :
          Measure (Real × Real)),
      z.1 ≤ z.2
  coordinateSourceFirstMoment :
    Integrable (fun x : Real => |x|)
      (source.map (rayCoordinate R) : Measure Real)
  coordinateTargetFirstMoment :
    Integrable (fun y : Real => |y|)
      (target.map (rayCoordinate R) : Measure Real)

namespace RaywiseCoordinateInheritance

noncomputable def coordinateCoupling
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {R : OrientedOpenRay n}
    {source target : FiniteMeasure (Euclidean n)}
    {component : FiniteMeasure (Euclidean n × Euclidean n)}
    (h :
      RaywiseCoordinateInheritance Gamma R source target component) :
    FiniteCoupling
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R)) :=
  ⟨component.map (Prod.map (rayCoordinate R) (rayCoordinate R)),
    h.coordinateIsCoupling⟩

theorem coordinateCoupling_isForward
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {R : OrientedOpenRay n}
    {source target : FiniteMeasure (Euclidean n)}
    {component : FiniteMeasure (Euclidean n × Euclidean n)}
    (h :
      RaywiseCoordinateInheritance Gamma R source target component) :
    IsForwardPlan h.coordinateCoupling :=
  h.coordinateComponentForward

end RaywiseCoordinateInheritance

/-! ## Coupling and forwardness adapters -/

theorem assembledRaywiseCoordinateComponent_isCoupling_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
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
        (maximalRayCoordinateSource D R)
        (maximalRayCoordinateTarget D gamma R)
        (assembledRaywiseCoordinateComponent D gamma gammaLift R) := by
  filter_upwards
      [assembledRaywiseComponent_isCoupling_ae
        D gamma gammaLift hLiftedForward] with R hCoupling
  let eta :
      FiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R) :=
    ⟨assembledRaywiseComponentFiber D gamma gammaLift R, hCoupling⟩
  simpa only [maximalRayCoordinateSource, maximalRayCoordinateTarget,
    assembledRaywiseCoordinateComponent] using
    (mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
      (measurable_rayCoordinate R) (measurable_rayCoordinate R)).property

theorem assembledRaywiseCoordinateComponent_forward_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hForward :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂(assembledRaywiseComponentFiber
            D gamma gammaLift R :
          Measure (Euclidean n × Euclidean n)),
          rayCoordinate R z.1 ≤ rayCoordinate R z.2) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(assembledRaywiseCoordinateComponent
          D gamma gammaLift R : Measure (Real × Real)),
        z.1 ≤ z.2 := by
  filter_upwards [hForward] with R hR
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

/-! ## First-moment inheritance -/

private theorem integrable_fiber_ae_of_reconstruction
    {R X E : Type*} [MeasurableSpace R] [MeasurableSpace X]
    [NormedAddCommGroup E]
    (sigma : Measure R) [SFinite sigma]
    (kappa : Kernel R X) [IsSFiniteKernel kappa]
    (rho : Measure X)
    (hreconstruct : kappa ∘ₘ sigma = rho)
    (f : X → E) (hf : Integrable f rho) :
    ∀ᵐ r ∂sigma, Integrable f (kappa r) := by
  have hcomp : Integrable f (kappa ∘ₘ sigma) := by
    rw [hreconstruct]
    exact hf
  exact
    ((Measure.integrable_comp_iff hcomp.aestronglyMeasurable).mp hcomp).1

private theorem abs_rayCoordinate_le
    {n : Nat} (R : OrientedOpenRay n) (x : Euclidean n) :
    |rayCoordinate R x| ≤ ‖x‖ + ‖R.anchor‖ := by
  have hDirectionNorm : ‖R.direction‖ = 1 := R.property.1
  calc
    |rayCoordinate R x| ≤
        ‖x - R.anchor‖ * ‖R.direction‖ :=
      abs_real_inner_le_norm (x - R.anchor) R.direction
    _ = ‖x - R.anchor‖ := by rw [hDirectionNorm, mul_one]
    _ ≤ ‖x‖ + ‖R.anchor‖ := norm_sub_le x R.anchor

theorem finiteFirstMoment_map_rayCoordinate
    {n : Nat} (R : OrientedOpenRay n)
    (rho : FiniteMeasure (Euclidean n))
    (hFirst : Integrable (fun x : Euclidean n => ‖x‖)
      (rho : Measure (Euclidean n))) :
    Integrable (fun t : Real => |t|)
      (rho.map (rayCoordinate R) : Measure Real) := by
  have hBound :
      Integrable (fun x : Euclidean n => ‖x‖ + ‖R.anchor‖)
        (rho : Measure (Euclidean n)) :=
    hFirst.add (integrable_const ‖R.anchor‖)
  have hCoordinate :
      Integrable (rayCoordinate R) (rho : Measure (Euclidean n)) := by
    apply hBound.mono
    · exact (continuous_rayCoordinate R).aestronglyMeasurable
    · filter_upwards with x
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg R.anchor))] using
        abs_rayCoordinate_le R x
  apply
    (integrable_map_measure
      continuous_abs.aestronglyMeasurable
      (measurable_rayCoordinate R).aemeasurable).2
  simpa only [Function.comp_apply, Real.norm_eq_abs] using hCoordinate.norm

theorem maximalRayCoordinateSource_firstMoment_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hFirst :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n))) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      Integrable (fun t : Real => |t|)
        (maximalRayCoordinateSource D R : Measure Real) := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  have hFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        Integrable (fun x : Euclidean n => ‖x‖) (D.source R) :=
    integrable_fiber_ae_of_reconstruction
      (D.sigma : Measure (OrientedOpenRay n)) D.source
      (mu : Measure (Euclidean n)) D.source_reconstruction
      (fun x : Euclidean n => ‖x‖) hFirst
  filter_upwards [hFiber] with R hR
  apply finiteFirstMoment_map_rayCoordinate R (maximalRaySourceFiber D R)
  simpa only [maximalRaySourceFiber_toMeasure] using hR

theorem maximalRayCoordinateTarget_firstMoment_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (hFirst :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      Integrable (fun t : Real => |t|)
        (maximalRayCoordinateTarget D gamma R : Measure Real) := by
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  have hFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        Integrable (fun y : Euclidean n => ‖y‖)
          (maximalRayTargetKernel D gamma R) :=
    integrable_fiber_ae_of_reconstruction
      (D.sigma : Measure (OrientedOpenRay n))
      (maximalRayTargetKernel D gamma)
      (nu : Measure (Euclidean n))
      (maximalRayTargetKernel_reconstruction D gamma hSupported)
      (fun y : Euclidean n => ‖y‖) hFirst
  filter_upwards [hFiber] with R hR
  apply finiteFirstMoment_map_rayCoordinate R
    (maximalRayTargetFiber D gamma R)
  simpa only [maximalRayTargetFiber_toMeasure] using hR

/-! ## Strict-exponential profile -/

theorem strictExponentialProfile_strictConcave :
    StrictConcaveOn Real (Ici 0) strictExponentialProfile := by
  have hExpNeg :
      StrictConvexOn Real (Ici 0)
        (fun d : Real => Real.exp (-d)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hxyNeg : -x ≠ -y := by
      intro h
      apply hxy
      have h' := congrArg (fun z : Real => -z) h
      simpa only [neg_neg] using h'
    have h :=
      strictConvexOn_exp.2 (mem_univ (-x)) (mem_univ (-y))
        hxyNeg ha hb hab
    simp only [smul_eq_mul]
    rw [show -(a * x + b * y) = a * -x + b * -y by ring]
    exact h
  have hNeg :
      StrictConcaveOn Real (Ici 0)
        (fun d : Real => -Real.exp (-d)) := by
    simpa only [Pi.neg_apply] using hExpNeg.neg
  apply (hNeg.add_const 1).congr
  intro d _hd
  simp only [Pi.add_apply, sub_eq_add_neg, strictExponentialProfile]
  exact add_comm _ _

theorem strictExponentialProfile_admissible :
    AdmissibleStrictlyConcaveProfile strictExponentialProfile := by
  refine ⟨strictExponentialProfile_strictConcave, 0, le_rfl, ?_⟩
  intro d hd
  simp only [neg_zero, zero_mul]
  unfold strictExponentialProfile
  exact sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd))

/-! ## Assembled inheritance -/

theorem assembledRaywiseCoordinateInheritance_ae_of_weakPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hSingular : FiniteMutuallySingular mu nu)
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      RaywiseCoordinateInheritance Gamma R
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R) := by
  have hCoupling :=
    assembledRaywiseCoordinateComponent_isCoupling_ae
      D gamma gammaLift hLiftedForward
  have hOnRay :=
    assembledRaywiseComponent_on_ray_ae
      D gamma hSupported gammaLift hLiftedForward
  have hForwardPhysical :=
    assembledRaywiseComponent_coordinate_forward_ae
      D gamma gammaLift hLiftedForward
  have hForward :=
    assembledRaywiseCoordinateComponent_forward_ae
      D gamma gammaLift hForwardPhysical
  have hAtomless :=
    maximalRaySource_coordinateAtomless_of_weakPremise
      D hRegularity gamma hSupported hmuAC hAtomless
  have hFiberSingular :=
    maximalRayCoordinateMarginals_mutuallySingular_ae
      D gamma hSupported hSingular
  have hDominates :=
    assembledRaywiseCoordinateTargetDominates
      D gamma gammaLift
      (assembledRaywiseComponent_isCoupling_ae
        D gamma gammaLift hLiftedForward)
      hForwardPhysical
  have hSourceFirst :=
    maximalRayCoordinateSource_firstMoment_ae D hFirstMu
  have hTargetFirst :=
    maximalRayCoordinateTarget_firstMoment_ae
      D gamma hSupported hFirstNu
  filter_upwards
      [D.ray_isMaximal_ae, hOnRay, hCoupling, hAtomless,
        hFiberSingular, hDominates, hForward, hSourceFirst,
        hTargetFirst] with
      R hMaximal hRay hCpl hAtom hSing hOrder hFwd hMu hNu
  exact {
    rayIsMaximal := hMaximal
    componentOnRay := hRay
    coordinateIsCoupling := hCpl
    coordinateSourceAtomless := hAtom
    coordinateMarginalsMutuallySingular := hSing
    coordinateTargetDominates := hOrder
    coordinateComponentForward := hFwd
    coordinateSourceFirstMoment := hMu
    coordinateTargetFirstMoment := hNu
  }

theorem assembledRaywiseCoordinateInheritance_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hSingular : FiniteMutuallySingular mu nu)
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      RaywiseCoordinateInheritance Gamma R
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R) := by
  exact assembledRaywiseCoordinateInheritance_ae_of_weakPremise
    D hRegularity gamma hSupported gammaLift hLiftedForward
    hmuAC
    (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
      mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
    hSingular hFirstMu hFirstNu

/-- The complete raywise-inheritance step: the bounded strict-exponential
profile is admissible, and almost every assembled maximal-ray component
inherits all one-dimensional hypotheses needed by the direct Juillet
theorems. -/
theorem raywiseCoordinateInheritance_of_weakPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hSingular : FiniteMutuallySingular mu nu)
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    AdmissibleStrictlyConcaveProfile strictExponentialProfile ∧
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        RaywiseCoordinateInheritance Gamma R
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R)
          (assembledRaywiseComponentFiber D gamma gammaLift R) := by
  exact ⟨strictExponentialProfile_admissible,
    assembledRaywiseCoordinateInheritance_ae_of_weakPremise
      D hRegularity gamma hSupported gammaLift hLiftedForward
      hmuAC hAtomless hSingular hFirstMu hFirstNu⟩

theorem raywiseCoordinateInheritance
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hSingular : FiniteMutuallySingular mu nu)
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    AdmissibleStrictlyConcaveProfile strictExponentialProfile ∧
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        RaywiseCoordinateInheritance Gamma R
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R)
          (assembledRaywiseComponentFiber D gamma gammaLift R) := by
  exact raywiseCoordinateInheritance_of_weakPremise
    D hRegularity gamma hSupported gammaLift hLiftedForward
    hmuAC
    (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
      mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
    hSingular hFirstMu hFirstNu

end ConcaveOTLimit
