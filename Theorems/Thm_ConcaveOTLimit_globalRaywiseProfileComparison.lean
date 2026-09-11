import Theorems.Thm_ConcaveOTLimit_raywiseExcursionIdentification
import Theorems.Thm_ConcaveOTLimit_raywiseDistancePreservation
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Profile costs under ray coordinates -/

theorem profileCost_mapFiniteCoupling_rayCoordinate_eq
    {n : Nat} (R : OrientedOpenRay n)
    {source target : FiniteMeasure (Euclidean n)}
    (eta : FiniteCoupling source target)
    (hOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile) :
    profileCost profile
        (mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R) (measurable_rayCoordinate R)) =
      profileCost profile eta := by
  unfold profileCost
  simp only [mapFiniteCoupling_plan, FiniteMeasure.toMeasure_map]
  change
    (∫ z, profile ‖z.1 - z.2‖
      ∂Measure.map (rayCoordinatePair R)
        (eta.plan : Measure (Euclidean n × Euclidean n))) =
      ∫ z, profile ‖z.1 - z.2‖
        ∂(eta.plan : Measure (Euclidean n × Euclidean n))
  have hMeasurable :
      Measurable (fun z : Real × Real => profile ‖z.1 - z.2‖) :=
    (concaveProfileDistanceLowerSemicontinuous
      (E := Real) hProfile.1).measurable
  rw [integral_map
    (μ := (eta.plan : Measure (Euclidean n × Euclidean n)))
    (φ := rayCoordinatePair R)
    (f := fun z : Real × Real => profile ‖z.1 - z.2‖)
    (measurable_rayCoordinatePair R).aemeasurable
    hMeasurable.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hOnRay] with z hz
  simp only [rayCoordinatePair]
  rw [← dist_eq_norm_rayCoordinate_sub_of_mem_closure R hz.1 hz.2,
    dist_eq_norm]

namespace RaywiseExcursionIdentification

/-- C173 comparison on one physical ray, together with strict equality
rigidity after pulling equality back through the ray coordinates. -/
theorem profileComparison_and_strictRigidity
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {R : OrientedOpenRay n}
    {source target : FiniteMeasure (Euclidean n)}
    {physical : FiniteCoupling source target}
    {hInheritance :
      RaywiseCoordinateInheritance Gamma R source target physical.plan}
    (hIdentification :
      RaywiseExcursionIdentification
        R source target physical hInheritance)
    (hPositive : 0 < (source.map (rayCoordinate R)).mass)
    (eta : FiniteCoupling source target)
    (hEtaOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hEtaForward :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (profile : Real -> Real)
    (hProfile : AdmissibleConcaveProfile profile) :
    profileCost profile physical <= profileCost profile eta ∧
      (AdmissibleStrictlyConcaveProfile profile ->
        profileCost profile physical = profileCost profile eta ->
          eta = physical) := by
  let etaCoordinate :
      FiniteCoupling
        (source.map (rayCoordinate R))
        (target.map (rayCoordinate R)) :=
    mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
      (measurable_rayCoordinate R) (measurable_rayCoordinate R)
  have hEtaCoordinateForward : IsForwardPlan etaCoordinate :=
    mapFiniteCoupling_rayCoordinate_isForward
      R eta hEtaForward
  have hMass :
      (source.map (rayCoordinate R)).mass =
        (target.map (rayCoordinate R)).mass :=
    finiteCoupling_marginalMass_eq hInheritance.coordinateCoupling
  have hVariational :=
    oneDimensionalExcursionVariational
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R))
      hMass hPositive
      hInheritance.coordinateSourceFirstMoment
      hInheritance.coordinateTargetFirstMoment
      hInheritance.coordinateMarginalsMutuallySingular
      hInheritance.coordinateSourceAtomless
      hInheritance.coordinateTargetDominates
      hInheritance.coordinateCoupling
      hIdentification.coordinateIsExcursion
  have hCoordinatePhysical :
      hInheritance.coordinateCoupling =
        mapFiniteCoupling physical
          (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R)
          (measurable_rayCoordinate R) := by
    apply Subtype.ext
    rfl
  have hPhysicalCost :
      profileCost profile hInheritance.coordinateCoupling =
        profileCost profile physical := by
    rw [hCoordinatePhysical]
    exact
      profileCost_mapFiniteCoupling_rayCoordinate_eq
        R physical hInheritance.componentOnRay hProfile
  have hEtaCost :
      profileCost profile etaCoordinate =
        profileCost profile eta :=
    profileCost_mapFiniteCoupling_rayCoordinate_eq
      R eta hEtaOnRay hProfile
  have hCoordinateLe :
      profileCost profile hInheritance.coordinateCoupling <=
        profileCost profile etaCoordinate :=
    (hVariational.2.2.1 profile hProfile).2
      etaCoordinate hEtaCoordinateForward
  refine ⟨?_, ?_⟩
  · calc
      profileCost profile physical =
          profileCost profile hInheritance.coordinateCoupling :=
        hPhysicalCost.symm
      _ <= profileCost profile etaCoordinate := hCoordinateLe
      _ = profileCost profile eta := hEtaCost
  · intro hStrict hCost
    have hCoordinateCost :
        profileCost profile hInheritance.coordinateCoupling =
          profileCost profile etaCoordinate := by
      calc
        profileCost profile hInheritance.coordinateCoupling =
            profileCost profile physical := hPhysicalCost
        _ = profileCost profile eta := hCost
        _ = profileCost profile etaCoordinate := hEtaCost.symm
    have hUnique :=
      hVariational.2.2.2 profile hStrict
    have hEtaMinimal :
        IsMinimizerOn
          {xi :
              FiniteCoupling
                (source.map (rayCoordinate R))
                (target.map (rayCoordinate R)) |
            IsForwardPlan xi}
          (profileCost profile) etaCoordinate := by
      refine ⟨hEtaCoordinateForward, ?_⟩
      intro xi hXi
      calc
        profileCost profile etaCoordinate =
            profileCost profile hInheritance.coordinateCoupling :=
          hCoordinateCost.symm
        _ <= profileCost profile xi := hUnique.1.2 xi hXi
    have hCoordinateEq :
        etaCoordinate = hInheritance.coordinateCoupling :=
      hUnique.2 etaCoordinate hEtaMinimal
    apply
      hIdentification.componentDeterminedByCoordinates
        eta hEtaOnRay
    have hPlanEq :=
      congrArg
        (fun xi :
          FiniteCoupling
            (source.map (rayCoordinate R))
            (target.map (rayCoordinate R)) => xi.plan)
        hCoordinateEq
    change
      eta.plan.map (rayCoordinatePair R) =
        hInheritance.coordinateCoupling.plan
    simpa only [etaCoordinate, mapFiniteCoupling_plan,
      rayCoordinatePair] using hPlanEq

end RaywiseExcursionIdentification

/-! ## Supported competitor components -/

variable {n : Nat}
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

/-- A supported competitor disintegrates into couplings of the same canonical
source and target fibers as the selected assembled coupling. -/
theorem supportedCompetitorComponent_isCoupling_ae
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma eta : FiniteCoupling mu nu)
    (hGamma : IsSupported gamma Gamma)
    (hEta : IsSupported eta Gamma) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (maximalRayInputComponentFiber D eta R) := by
  filter_upwards
      [D.component_map_fst_ae_eq_source eta hEta,
        supportedComponent_target_ae_eq_maximalRayTargetKernel
          D gamma eta hGamma hEta] with R hfst hsnd
  constructor
  · apply FiniteMeasure.toMeasure_injective
    simpa [firstMarginal, Kernel.map_apply _ measurable_fst] using hfst
  · apply FiniteMeasure.toMeasure_injective
    simpa [secondMarginal, Kernel.map_apply _ measurable_snd] using hsnd

private theorem integral_eq_integral_kernel_of_reconstruction
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (sigma : Measure R)
    (kappa : Kernel R X)
    (rho : Measure X)
    (hReconstruct : kappa ∘ₘ sigma = rho)
    (f : X -> Real)
    (hf : Integrable f rho) :
    (∫ x, f x ∂rho) =
      ∫ r, ∫ x, f x ∂kappa r ∂sigma := by
  have hComp : Integrable f (kappa ∘ₘ sigma) := by
    rw [hReconstruct]
    exact hf
  rw [← hReconstruct, Measure.comp_eq_comp_const_apply]
  simpa only [Kernel.const_apply] using
    (Kernel.integral_comp
      (η := kappa) (κ := Kernel.const Unit sigma) (a := ())
      hComp)

private theorem integrable_integral_kernel_of_comp
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (sigma : Measure R)
    (kappa : Kernel R X)
    (f : X -> Real)
    (hf : StronglyMeasurable f)
    (hComp : Integrable f (kappa ∘ₘ sigma)) :
    Integrable (fun r => ∫ x, f x ∂kappa r) sigma := by
  have hNorm :
      Integrable (fun r => ∫ x, ‖f x‖ ∂kappa r) sigma :=
    ((Measure.integrable_comp_iff
      (κ := kappa) hComp.aestronglyMeasurable).mp hComp).2
  apply Integrable.mono hNorm
    (hf.integral_kernel (κ := kappa)).aestronglyMeasurable
  filter_upwards with r
  calc
    ‖∫ x, f x ∂kappa r‖ <=
        ∫ x, ‖f x‖ ∂kappa r :=
      norm_integral_le_integral_norm _
    _ = ‖∫ x, ‖f x‖ ∂kappa r‖ := by
      rw [Real.norm_of_nonneg]
      exact integral_nonneg fun _ => norm_nonneg _

/-! ## Global comparison and rigidity -/

/-- Integrating the C173 comparison over the maximal-ray disintegration gives
global profile comparison. Equality for a strict profile forces equality of
the coordinate components, then of the physical components, and finally of
the reconstructed global couplings. -/
theorem assembledRaywiseCoupling_profileComparison_and_strictRigidity
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hIdentification :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        CanonicalRaywiseExcursionIdentification
          D gamma gammaLift R)
    (eta : FiniteCoupling mu nu)
    (hEta : IsSupported eta Gamma)
    (profile : Real -> Real)
    (hProfile : AdmissibleConcaveProfile profile) :
    profileCost profile
        (assembledRaywiseCoupling
          D gamma hSupported gammaLift) <=
      profileCost profile eta ∧
        (AdmissibleStrictlyConcaveProfile profile ->
          profileCost profile
              (assembledRaywiseCoupling
                D gamma hSupported gammaLift) =
            profileCost profile eta ->
          eta =
            assembledRaywiseCoupling
              D gamma hSupported gammaLift) := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (D.component eta) :=
    D.component_isMarkovKernel eta
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  letI : IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  let cost : Euclidean n × Euclidean n -> Real :=
    fun z => profile ‖z.1 - z.2‖
  let assembledFiberCost : OrientedOpenRay n -> Real :=
    fun R => ∫ z, cost z ∂assembledRaywiseKernel D gamma gammaLift R
  let competitorFiberCost : OrientedOpenRay n -> Real :=
    fun R => ∫ z, cost z ∂D.component eta R
  have hEtaCoupling :=
    supportedCompetitorComponent_isCoupling_ae
      D gamma eta hSupported hEta
  have hEtaOnRay :=
    D.component_endpoints_mem_closure_ae eta hEta
  have hEtaForward :=
    maximalRayComponent_coordinate_forward_ae D eta hEta
  have hRaywiseLe :
      assembledFiberCost ≤ᵐ[
        (D.sigma : Measure (OrientedOpenRay n))]
          competitorFiberCost := by
    filter_upwards
        [hIdentification, hEtaCoupling, hEtaOnRay,
          hEtaForward] with
        R hRIdentification hRCoupling hROnRay hRForward
    obtain ⟨hRAssembledCoupling, hRInheritance, hRExcursion⟩ :=
      hRIdentification
    let etaPhysical :
        FiniteCoupling
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R) :=
      ⟨maximalRayInputComponentFiber D eta R, hRCoupling⟩
    have hPositive :
        0 <
          ((maximalRaySourceFiber D R).map
            (rayCoordinate R)).mass := by
      change 0 < (maximalRayCoordinateSource D R).mass
      rw [maximalRayCoordinateSource_mass_eq_one D R]
      exact zero_lt_one
    have hLocal :=
      RaywiseExcursionIdentification.profileComparison_and_strictRigidity
        hRExcursion hPositive etaPhysical
        (by
          simpa only [etaPhysical,
            maximalRayInputComponentFiber_toMeasure] using hROnRay)
        (by
          simpa only [etaPhysical,
            maximalRayInputComponentFiber_toMeasure] using hRForward)
        profile hProfile
    simpa only [assembledFiberCost, competitorFiberCost, cost,
      profileCost, assembledRaywisePhysicalCoupling_plan,
      assembledRaywiseComponentFiber_toMeasure,
      etaPhysical, maximalRayInputComponentFiber_toMeasure] using hLocal.1
  have hAssembledGlobalIntegrable :
      Integrable cost
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)) := by
    exact
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hProfile hFirstMu hFirstNu
        (assembledRaywiseCoupling D gamma hSupported gammaLift)
  have hEtaGlobalIntegrable :
      Integrable cost
        (eta.plan : Measure (Euclidean n × Euclidean n)) := by
    exact
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hProfile hFirstMu hFirstNu eta
  have hAssembledCompIntegrable :
      Integrable cost
        (assembledRaywiseKernel D gamma gammaLift ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) := by
    rw [assembledRaywiseKernel_reconstruction
      D gamma hSupported gammaLift]
    exact hAssembledGlobalIntegrable
  have hEtaCompIntegrable :
      Integrable cost
        (D.component eta ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) := by
    rw [D.component_reconstruction eta hEta]
    exact hEtaGlobalIntegrable
  have hCostStronglyMeasurable : StronglyMeasurable cost := by
    exact
      ((concaveProfileDistanceLowerSemicontinuous
        (E := Euclidean n) hProfile.1).measurable).stronglyMeasurable
  have hAssembledFiberIntegrable :
      Integrable assembledFiberCost
        (D.sigma : Measure (OrientedOpenRay n)) := by
    simpa only [assembledFiberCost] using
      integrable_integral_kernel_of_comp
        (D.sigma : Measure (OrientedOpenRay n))
        (assembledRaywiseKernel D gamma gammaLift)
        cost hCostStronglyMeasurable hAssembledCompIntegrable
  have hEtaFiberIntegrable :
      Integrable competitorFiberCost
        (D.sigma : Measure (OrientedOpenRay n)) := by
    simpa only [competitorFiberCost] using
      integrable_integral_kernel_of_comp
        (D.sigma : Measure (OrientedOpenRay n))
        (D.component eta)
        cost hCostStronglyMeasurable hEtaCompIntegrable
  have hAssembledIntegral :
      profileCost profile
          (assembledRaywiseCoupling
            D gamma hSupported gammaLift) =
        ∫ R, assembledFiberCost R
          ∂(D.sigma : Measure (OrientedOpenRay n)) := by
    exact
      integral_eq_integral_kernel_of_reconstruction
        (D.sigma : Measure (OrientedOpenRay n))
        (assembledRaywiseKernel D gamma gammaLift)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n))
        (assembledRaywiseKernel_reconstruction
          D gamma hSupported gammaLift)
        cost hAssembledGlobalIntegrable
  have hEtaIntegral :
      profileCost profile eta =
        ∫ R, competitorFiberCost R
          ∂(D.sigma : Measure (OrientedOpenRay n)) := by
    exact
      integral_eq_integral_kernel_of_reconstruction
        (D.sigma : Measure (OrientedOpenRay n))
        (D.component eta)
        (eta.plan : Measure (Euclidean n × Euclidean n))
        (D.component_reconstruction eta hEta)
        cost hEtaGlobalIntegrable
  refine ⟨?_, ?_⟩
  · rw [hAssembledIntegral, hEtaIntegral]
    exact
      integral_mono_ae
        hAssembledFiberIntegrable hEtaFiberIntegrable hRaywiseLe
  · intro hStrict hGlobalCost
    have hFiberCostEq :
        assembledFiberCost =ᵐ[
          (D.sigma : Measure (OrientedOpenRay n))]
            competitorFiberCost := by
      apply
        (integral_eq_iff_of_ae_le
          hAssembledFiberIntegrable hEtaFiberIntegrable
          hRaywiseLe).mp
      rw [← hAssembledIntegral, ← hEtaIntegral]
      exact hGlobalCost
    have hComponentEq :
        D.component eta =ᵐ[
          (D.sigma : Measure (OrientedOpenRay n))]
            assembledRaywiseKernel D gamma gammaLift := by
      filter_upwards
          [hIdentification, hEtaCoupling, hEtaOnRay,
            hEtaForward, hFiberCostEq] with
          R hRIdentification hRCoupling hROnRay hRForward hRCost
      obtain ⟨hRAssembledCoupling, hRInheritance, hRExcursion⟩ :=
        hRIdentification
      let etaPhysical :
          FiniteCoupling
            (maximalRaySourceFiber D R)
            (maximalRayTargetFiber D gamma R) :=
        ⟨maximalRayInputComponentFiber D eta R, hRCoupling⟩
      have hPositive :
          0 <
            ((maximalRaySourceFiber D R).map
              (rayCoordinate R)).mass := by
        change 0 < (maximalRayCoordinateSource D R).mass
        rw [maximalRayCoordinateSource_mass_eq_one D R]
        exact zero_lt_one
      have hLocal :=
        RaywiseExcursionIdentification.profileComparison_and_strictRigidity
          hRExcursion hPositive etaPhysical
          (by
            simpa only [etaPhysical,
              maximalRayInputComponentFiber_toMeasure] using hROnRay)
          (by
            simpa only [etaPhysical,
              maximalRayInputComponentFiber_toMeasure] using hRForward)
          profile hProfile
      have hLocalCost :
          profileCost profile
              (assembledRaywisePhysicalCoupling
                D gamma gammaLift R hRAssembledCoupling) =
            profileCost profile etaPhysical := by
        simpa only [assembledFiberCost, competitorFiberCost, cost,
          profileCost, assembledRaywisePhysicalCoupling_plan,
          assembledRaywiseComponentFiber_toMeasure,
          etaPhysical, maximalRayInputComponentFiber_toMeasure] using hRCost
      have hPhysicalEq :
          etaPhysical =
            assembledRaywisePhysicalCoupling
              D gamma gammaLift R hRAssembledCoupling :=
        hLocal.2 hStrict hLocalCost
      have hPlanEq :=
        congrArg
          (fun xi :
            FiniteCoupling
              (maximalRaySourceFiber D R)
              (maximalRayTargetFiber D gamma R) => xi.plan)
          hPhysicalEq
      have hMeasureEq :=
        congrArg
          (fun rho : FiniteMeasure (Euclidean n × Euclidean n) =>
            (rho : Measure (Euclidean n × Euclidean n)))
          hPlanEq
      simpa only [etaPhysical,
        assembledRaywisePhysicalCoupling_plan,
        maximalRayInputComponentFiber_toMeasure,
        assembledRaywiseComponentFiber_toMeasure] using hMeasureEq
    apply Subtype.ext
    apply FiniteMeasure.toMeasure_injective
    calc
      (eta.plan : Measure (Euclidean n × Euclidean n)) =
          D.component eta ∘ₘ
            (D.sigma : Measure (OrientedOpenRay n)) :=
        (D.component_reconstruction eta hEta).symm
      _ =
          assembledRaywiseKernel D gamma gammaLift ∘ₘ
            (D.sigma : Measure (OrientedOpenRay n)) :=
        Measure.comp_congr hComponentEq
      _ =
          ((assembledRaywiseCoupling
            D gamma hSupported gammaLift).plan :
              Measure (Euclidean n × Euclidean n)) :=
        assembledRaywiseKernel_reconstruction
          D gamma hSupported gammaLift

/-- The two profile fields of
`CanonicalRaywiseReplacementResidualInputs` follow from canonical fiber
minimality and the already established raywise identification theorem. -/
theorem canonicalRaywiseReplacement_profileFields_of_fiberMinimality_of_weakPremise
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hMarginals : MarginalHypotheses n mu nu)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift) :
    (∀ eta : FiniteCoupling mu nu,
      IsSupported eta Gamma ->
        ∀ profile : Real -> Real,
          AdmissibleConcaveProfile profile ->
            profileCost profile
                (assembledRaywiseCoupling
                  D gamma hSupported gammaLift) <=
              profileCost profile eta) ∧
      (∀ eta : FiniteCoupling mu nu,
        IsSupported eta Gamma ->
          ∀ profile : Real -> Real,
            AdmissibleStrictlyConcaveProfile profile ->
              profileCost profile
                  (assembledRaywiseCoupling
                    D gamma hSupported gammaLift) =
                  profileCost profile eta ->
                eta =
                  assembledRaywiseCoupling
                    D gamma hSupported gammaLift) := by
  have hIdentification :=
    canonicalRaywiseExcursionIdentification_ae_of_weakPremise
      D hRegularity gamma hSupported gammaLift hLiftedForward
      hMarginals.sourceAbsolutelyContinuous hAtomless
      hMarginals.mutuallySingular
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
      hFiberMinimal
  constructor
  · intro eta hEta profile hProfile
    exact
      (assembledRaywiseCoupling_profileComparison_and_strictRigidity
        D gamma hSupported gammaLift
        hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        hIdentification eta hEta profile hProfile).1
  · intro eta hEta profile hStrict hCost
    have hProfile : AdmissibleConcaveProfile profile :=
      ⟨hStrict.1.concaveOn, hStrict.2⟩
    exact
      (assembledRaywiseCoupling_profileComparison_and_strictRigidity
        D gamma hSupported gammaLift
        hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        hIdentification eta hEta profile hProfile).2 hStrict hCost

theorem canonicalRaywiseReplacement_profileFields_of_fiberMinimality
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hMarginals : MarginalHypotheses n mu nu)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift) :
    (∀ eta : FiniteCoupling mu nu,
      IsSupported eta Gamma ->
        ∀ profile : Real -> Real,
          AdmissibleConcaveProfile profile ->
            profileCost profile
                (assembledRaywiseCoupling
                  D gamma hSupported gammaLift) <=
              profileCost profile eta) ∧
      (∀ eta : FiniteCoupling mu nu,
        IsSupported eta Gamma ->
          ∀ profile : Real -> Real,
            AdmissibleStrictlyConcaveProfile profile ->
              profileCost profile
                  (assembledRaywiseCoupling
                    D gamma hSupported gammaLift) =
                  profileCost profile eta ->
                eta =
                  assembledRaywiseCoupling
                    D gamma hSupported gammaLift) := by
  exact
    canonicalRaywiseReplacement_profileFields_of_fiberMinimality_of_weakPremise
      D hRegularity hMarginals gamma hSupported gammaLift
      hLiftedForward
      (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
        mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
      hFiberMinimal

/-! ## Residual-input reduction -/

/-- The four genuinely profile-independent fields left in the assembly
boundary. The comparison and rigidity fields are derived below. -/
structure CanonicalRaywiseReplacementProfileIndependentInputs
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

/-- Construct the original six-field residual package from only its four
profile-independent fields. -/
theorem canonicalRaywiseReplacementResidualInputs_of_profileIndependent_of_weakPremise
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hMarginals : MarginalHypotheses n mu nu)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift)
    (hInput :
      CanonicalRaywiseReplacementProfileIndependentInputs
        D gamma hSupported gammaLift) :
    CanonicalRaywiseReplacementResidualInputs
      D gamma hSupported gammaLift := by
  have hProfileFields :=
    canonicalRaywiseReplacement_profileFields_of_fiberMinimality_of_weakPremise
      D hRegularity hMarginals gamma hSupported gammaLift
      hLiftedForward hAtomless hFiberMinimal
  exact {
    sameRayClosureMeasurable := hInput.sameRayClosureMeasurable
    fiberMinimalityIdentifiesExcursion :=
      hInput.fiberMinimalityIdentifiesExcursion
    conditionalDeterminism := hInput.conditionalDeterminism
    cyclicDistanceOptimal := hInput.cyclicDistanceOptimal
    profileComparison := hProfileFields.1
    strictProfileRigidity := hProfileFields.2
  }

theorem canonicalRaywiseReplacementResidualInputs_of_profileIndependent
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hMarginals : MarginalHypotheses n mu nu)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift)
    (hInput :
      CanonicalRaywiseReplacementProfileIndependentInputs
        D gamma hSupported gammaLift) :
    CanonicalRaywiseReplacementResidualInputs
      D gamma hSupported gammaLift := by
  exact
    canonicalRaywiseReplacementResidualInputs_of_profileIndependent_of_weakPremise
      D hRegularity hMarginals gamma hSupported gammaLift
      hLiftedForward
      (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
        mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
      hFiberMinimal hInput

end ConcaveOTLimit
