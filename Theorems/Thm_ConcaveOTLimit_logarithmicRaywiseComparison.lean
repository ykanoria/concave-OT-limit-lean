import Theorems.Thm_ConcaveOTLimit_logarithmicSecondaryUniquenessAssembly
import Theorems.Thm_ConcaveOTLimit_globalRaywiseProfileComparison
import Theorems.Thm_ConcaveOTLimit_logarithmicProfileStrictConcave
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientCostTendstoOfOrliczBound
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientOrliczBound
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientTendstoLogarithmic
import Theorems.Thm_ConcaveOTLimit_powerProfileCostDecomposition
import Theorems.Thm_ConcaveOTLimit_powerProfileStrictConcave
import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_fixedMassPlanNormalization
import Theorems.Thm_ConcaveOTLimit_logarithmicProfileLePowerDifferenceQuotient
import Theorems.Thm_ConcaveOTLimit_crossProductReroutingIntegralIdentity
import Theorems.Thm_ConcaveOTLimit_existsForwardBalancedCrossProductReroutingCoupling
import Theorems.Thm_ConcaveOTLimit_existsMeasurableStrictForwardTopologicalSupportOnCarrier
import Theorems.Thm_ConcaveOTLimit_existsPositiveBalancedSwapCoefficient
import Theorems.Thm_ConcaveOTLimit_forwardPairsDistanceTwoCycleAndReroutingOfTie
import Theorems.Thm_ConcaveOTLimit_integralSwapGapPositive
import Theorems.Thm_ConcaveOTLimit_isJuilletExcursionPlanOfLexicographicSupport
import Theorems.Thm_ConcaveOTLimit_profileCostReroutingLtOfAddedLtRemoved
import Theorems.Thm_ConcaveOTLimit_strictCrossedForwardOfDistanceTieOnCarrier
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.Linarith

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Kernels carried by the public raywise witness -/

private noncomputable def finiteMeasureFamilyKernel
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (kappa : R -> FiniteMeasure X)
    (hMeasurable :
      forall s : Set X, MeasurableSet s ->
        Measurable fun r => (kappa r : Measure X) s) :
    Kernel R X :=
  ⟨fun r => (kappa r : Measure X),
    Measure.measurable_of_measurable_coe
      (fun r => (kappa r : Measure X)) hMeasurable⟩

private noncomputable def raywiseSourceKernel
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  finiteMeasureFamilyKernel D.source D.sourceEvaluationMeasurable

private noncomputable def raywiseTargetKernel
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    Kernel (OrientedOpenRay n) (Euclidean n) :=
  finiteMeasureFamilyKernel D.target D.targetEvaluationMeasurable

private noncomputable def raywiseComponentKernel
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n) :=
  finiteMeasureFamilyKernel D.component D.componentEvaluationMeasurable

@[simp]
private theorem raywiseSourceKernel_apply
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap)
    (R : OrientedOpenRay n) :
    raywiseSourceKernel D R = (D.source R : Measure (Euclidean n)) :=
  rfl

@[simp]
private theorem raywiseTargetKernel_apply
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap)
    (R : OrientedOpenRay n) :
    raywiseTargetKernel D R = (D.target R : Measure (Euclidean n)) :=
  rfl

@[simp]
private theorem raywiseComponentKernel_apply
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap)
    (R : OrientedOpenRay n) :
    raywiseComponentKernel D R =
      (D.component R : Measure (Euclidean n × Euclidean n)) :=
  rfl

private theorem raywiseSourceKernel_reconstruction
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    raywiseSourceKernel D ∘ₘ
        (D.sigma : Measure (OrientedOpenRay n)) =
      (mu : Measure (Euclidean n)) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable (raywiseSourceKernel D))]
  exact (D.sourceReconstruction s hs).symm

private theorem raywiseTargetKernel_reconstruction
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    raywiseTargetKernel D ∘ₘ
        (D.sigma : Measure (OrientedOpenRay n)) =
      (nu : Measure (Euclidean n)) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable (raywiseTargetKernel D))]
  exact (D.targetReconstruction s hs).symm

private theorem raywiseComponentKernel_reconstruction
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    raywiseComponentKernel D ∘ₘ
        (D.sigma : Measure (OrientedOpenRay n)) =
      (gamma : Measure (Euclidean n × Euclidean n)) := by
  ext s hs
  rw [Measure.bind_apply hs
    (Kernel.aemeasurable (raywiseComponentKernel D))]
  exact (D.planReconstruction s hs).symm

/-! The public `RaywiseExcursionDisintegration` reconstructs only its
distinguished plan.  Comparison with another supported plan therefore needs
the latter disintegrated over the same source and target fibers. -/

structure RaywiseSameFiberCompetitorDisintegration
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap)
    (eta : FiniteMeasure (Euclidean n × Euclidean n)) where
  component :
    OrientedOpenRay n -> FiniteMeasure (Euclidean n × Euclidean n)
  componentEvaluationMeasurable :
    forall s : Set (Euclidean n × Euclidean n), MeasurableSet s ->
      Measurable fun R =>
        (component R : Measure (Euclidean n × Euclidean n)) s
  planReconstruction :
    forall s : Set (Euclidean n × Euclidean n), MeasurableSet s ->
      (eta : Measure (Euclidean n × Euclidean n)) s =
        lintegral (D.sigma : Measure (OrientedOpenRay n))
          fun R =>
            (component R : Measure (Euclidean n × Euclidean n)) s
  componentIsCoupling :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsFiniteCoupling (D.source R) (D.target R) (component R)
  componentOnRay :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(component R :
          Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier /\ z.2 ∈ closure R.carrier
  coordinateComponentForward :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(component R :
          Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 <= rayCoordinate R z.2

private noncomputable def competitorComponentKernel
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma eta : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    {D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap}
    (E : RaywiseSameFiberCompetitorDisintegration D eta) :
    Kernel (OrientedOpenRay n) (Euclidean n × Euclidean n) :=
  finiteMeasureFamilyKernel E.component E.componentEvaluationMeasurable

@[simp]
private theorem competitorComponentKernel_apply
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma eta : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    {D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap}
    (E : RaywiseSameFiberCompetitorDisintegration D eta)
    (R : OrientedOpenRay n) :
    competitorComponentKernel E R =
      (E.component R : Measure (Euclidean n × Euclidean n)) :=
  rfl

private theorem competitorComponentKernel_reconstruction
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma eta : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    {D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap}
    (E : RaywiseSameFiberCompetitorDisintegration D eta) :
    competitorComponentKernel E ∘ₘ
        (D.sigma : Measure (OrientedOpenRay n)) =
      (eta : Measure (Euclidean n × Euclidean n)) := by
  ext s hs
  rw [Measure.bind_apply hs
    (Kernel.aemeasurable (competitorComponentKernel E))]
  exact (E.planReconstruction s hs).symm

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

private theorem logarithmicProfileCost_mapFiniteCoupling_rayCoordinate_eq
    {n : Nat} (R : OrientedOpenRay n)
    {source target : FiniteMeasure (Euclidean n)}
    (eta : FiniteCoupling source target)
    (hOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier) :
    profileCost logarithmicProfile
        (mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R) (measurable_rayCoordinate R)) =
      profileCost logarithmicProfile eta := by
  unfold profileCost
  simp only [mapFiniteCoupling_plan, FiniteMeasure.toMeasure_map]
  change
    (∫ z, logarithmicProfile ‖z.1 - z.2‖
      ∂Measure.map (rayCoordinatePair R)
        (eta.plan : Measure (Euclidean n × Euclidean n))) =
      ∫ z, logarithmicProfile ‖z.1 - z.2‖
        ∂(eta.plan : Measure (Euclidean n × Euclidean n))
  have hMeasurable :
      Measurable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖) := by
    unfold logarithmicProfile
    exact
      (Real.continuous_negMulLog.comp
        ((continuous_fst.sub continuous_snd).norm)).measurable
  rw [integral_map
    (μ := (eta.plan : Measure (Euclidean n × Euclidean n)))
    (φ := rayCoordinatePair R)
    (f := fun z : Real × Real =>
      logarithmicProfile ‖z.1 - z.2‖)
    (measurable_rayCoordinatePair R).aemeasurable
    hMeasurable.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hOnRay] with z hz
  simp only [rayCoordinatePair]
  rw [← dist_eq_norm_rayCoordinate_sub_of_mem_closure R hz.1 hz.2,
    dist_eq_norm]

private theorem logarithmicIntegrable_mapFiniteCoupling_rayCoordinate
    {n : Nat} (R : OrientedOpenRay n)
    {source target : FiniteMeasure (Euclidean n)}
    (eta : FiniteCoupling source target)
    (hOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Euclidean n × Euclidean n))) :
    Integrable
      (fun z : Real × Real =>
        logarithmicProfile ‖z.1 - z.2‖)
      ((mapFiniteCoupling eta
        (rayCoordinate R) (rayCoordinate R)
        (measurable_rayCoordinate R)
        (measurable_rayCoordinate R)).plan :
          Measure (Real × Real)) := by
  simp only [mapFiniteCoupling_plan, FiniteMeasure.toMeasure_map]
  have hContinuous :
      Continuous
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖) := by
    unfold logarithmicProfile
    exact
      Real.continuous_negMulLog.comp
        ((continuous_fst.sub continuous_snd).norm)
  apply
    (integrable_map_measure
      hContinuous.aestronglyMeasurable
      ((measurable_rayCoordinate R).prodMap
        (measurable_rayCoordinate R)).aemeasurable).2
  refine hIntegrable.congr ?_
  filter_upwards [hOnRay] with z hz
  change
    logarithmicProfile ‖z.1 - z.2‖ =
      logarithmicProfile
        ‖rayCoordinate R z.1 - rayCoordinate R z.2‖
  rw [← dist_eq_norm_rayCoordinate_sub_of_mem_closure R hz.1 hz.2,
    dist_eq_norm]

/-- The structural adapter absent from the public excursion witness: every
supported competitor must admit a disintegration over the witness's same
source and target fibers. -/
def RaywiseSameFiberCompetitorDisintegrationPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (Gamma : Set (Euclidean n × Euclidean n)) : Prop :=
  forall (gammaSharp : FiniteCoupling mu nu)
    (transportMap : Euclidean n -> Euclidean n)
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gammaSharp.plan transportMap),
    IsSupported gammaSharp Gamma ->
      forall eta : FiniteCoupling mu nu,
        IsSupported eta Gamma ->
          Nonempty
            (RaywiseSameFiberCompetitorDisintegration D eta.plan)

/-! ## The remaining one-dimensional logarithmic statement -/

/-- The smallest profile-specific rigidity input left after the power
profiles prove logarithmic comparison.  It only says that equality in the
logarithmic comparison forces the other forward coupling to have Juillet's
monotone-arch property.  Existing `monotoneArchPlan_unique` then identifies
the two couplings. -/
def OneDimensionalLogarithmicEqualityJuilletPremise : Prop :=
  forall {source target : FiniteMeasure Real}
    (gammaEC eta : FiniteCoupling source target),
    FiniteMutuallySingular source target ->
      IsAtomlessFinite source ->
        StochasticallyDominates target source ->
          IsJuilletExcursionPlan source target gammaEC.plan ->
            IsForwardPlan eta ->
              Integrable
                (fun z : Real × Real =>
                  logarithmicProfile ‖z.1 - z.2‖)
                (gammaEC.plan : Measure (Real × Real)) ->
                Integrable
                  (fun z : Real × Real =>
                    logarithmicProfile ‖z.1 - z.2‖)
                  (eta.plan : Measure (Real × Real)) ->
                  profileCost logarithmicProfile gammaEC =
                      profileCost logarithmicProfile eta ->
                    IsJuilletExcursionPlan source target eta.plan

private theorem powerProfile_admissibleStrict
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    AdmissibleStrictlyConcaveProfile (powerProfile epsilon) := by
  refine ⟨powerProfileStrictConcave hEpsilon, 0, le_rfl, ?_⟩
  intro d hd
  simp only [neg_zero, zero_mul]
  exact Real.rpow_nonneg hd _

private theorem psi_le_one_of_mem_unitInterval
    {r : Real} (hr : 0 <= r) (hrOne : r <= 1) :
    Psi r <= 1 := by
  have hLog :
      Real.log (1 + r) <= r := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + r by linarith)
    linarith
  unfold Psi
  have hMul := mul_le_mul_of_nonneg_left hLog hr
  nlinarith

private theorem powerDifferenceQuotient_nonpositive_of_one_le
    {epsilon r : Real} (hEpsilonPos : 0 < epsilon)
    (hr : 1 <= r) :
    (powerProfile epsilon r - r) / epsilon <= 0 := by
  have hPower : powerProfile epsilon r <= r := by
    unfold powerProfile
    simpa using
      Real.rpow_le_rpow_of_exponent_le hr
        (by linarith : 1 - epsilon <= 1)
  exact
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hPower)
      hEpsilonPos.le

private theorem abs_powerDifferenceQuotient_le_logarithmicBound
    {epsilon r : Real}
    (hEpsilonPos : 0 < epsilon)
    (hEpsilonLeHalf : epsilon <= 1 / 2)
    (hr : 0 <= r) :
    abs ((powerProfile epsilon r - r) / epsilon) <=
      3 + abs (logarithmicProfile r) := by
  by_cases hrOne : r <= 1
  · have hOrlicz :=
      powerDifferenceQuotientOrliczBound
        hEpsilonPos hEpsilonLeHalf hr
    have hPsi := psi_le_one_of_mem_unitInterval hr hrOne
    linarith [abs_nonneg (logarithmicProfile r)]
  · have hOne : 1 <= r := le_of_not_ge hrOne
    have hEpsilonLtOne : epsilon < 1 := by
      linarith
    have hLogLe :=
      logarithmicProfileLePowerDifferenceQuotient
        hEpsilonPos hEpsilonLtOne hr
    have hQuotientNonpositive :=
      powerDifferenceQuotient_nonpositive_of_one_le
        hEpsilonPos hOne
    have hLogNonpositive : logarithmicProfile r <= 0 := by
      unfold logarithmicProfile Real.negMulLog
      exact
        mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (zero_le_one.trans hOne))
          (Real.log_nonneg hOne)
    rw [abs_of_nonpos hQuotientNonpositive,
      abs_of_nonpos hLogNonpositive]
    linarith

private theorem powerDifferenceQuotient_integrable_of_logarithmic
    {X : Type*} [MeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]
    (cost : X -> Real)
    (hCostMeasurable : Measurable cost)
    (hCostNonnegative : ∀ x, 0 <= cost x)
    {epsilon : Real}
    (hEpsilonPos : 0 < epsilon)
    (hEpsilonLeHalf : epsilon <= 1 / 2)
    (hLogarithmic :
      Integrable (fun x => logarithmicProfile (cost x)) measure) :
    Integrable
      (fun x =>
        (powerProfile epsilon (cost x) - cost x) / epsilon)
      measure := by
  have hBound :
      Integrable
        (fun x => 3 + abs (logarithmicProfile (cost x)))
        measure :=
    (integrable_const 3).add hLogarithmic.abs
  refine hBound.mono' ?_ (ae_of_all _ fun x => ?_)
  · have hContinuous :
        Continuous
          (fun r : Real =>
            (powerProfile epsilon r - r) / epsilon) := by
      unfold powerProfile
      exact
        ((Real.continuous_rpow_const
          (by linarith)).sub continuous_id).div_const _
    exact
      (hContinuous.measurable.comp
        hCostMeasurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact
      abs_powerDifferenceQuotient_le_logarithmicBound
        hEpsilonPos hEpsilonLeHalf (hCostNonnegative x)

private theorem powerDifferenceQuotientCostTendstoOfLogarithmicIntegrable
    {X : Type*} [MeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]
    (cost : X -> Real)
    (hCostMeasurable : Measurable cost)
    (hCostNonnegative : ∀ x, 0 <= cost x)
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonLeHalf : ∀ n, epsilon n <= 1 / 2)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0))
    (hLogarithmic :
      Integrable (fun x => logarithmicProfile (cost x)) measure) :
    Tendsto
      (fun n =>
        integral measure
          (fun x =>
            (powerProfile (epsilon n) (cost x) - cost x) /
              epsilon n))
      atTop
      (nhds
        (integral measure
          (fun x => logarithmicProfile (cost x)))) := by
  have hEpsilonRight :
      Tendsto epsilon atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hEpsilonTendsto,
        Eventually.of_forall fun n => hEpsilonPos n⟩
  apply tendsto_integral_of_dominated_convergence
    (fun x => 3 + abs (logarithmicProfile (cost x)))
  · intro n
    have hContinuous :
        Continuous
          (fun r : Real =>
            (powerProfile (epsilon n) r - r) / epsilon n) := by
      unfold powerProfile
      exact
        ((Real.continuous_rpow_const
          (by linarith [hEpsilonLeHalf n])).sub continuous_id).div_const _
    exact
      (hContinuous.measurable.comp
        hCostMeasurable).aestronglyMeasurable
  · exact (integrable_const 3).add hLogarithmic.abs
  · intro n
    exact ae_of_all measure fun x => by
      rw [Real.norm_eq_abs]
      exact
        abs_powerDifferenceQuotient_le_logarithmicBound
          (hEpsilonPos n) (hEpsilonLeHalf n)
          (hCostNonnegative x)
  · filter_upwards [] with x
    simpa [Function.comp_def] using
      (powerDifferenceQuotientTendstoLogarithmic
        (hCostNonnegative x)).comp hEpsilonRight

/-- C173 power comparison passes to the logarithmic profile whenever both
logarithmic costs are integrable. -/
private theorem oneDimensionalLogarithmicCost_le
    {source target : FiniteMeasure Real}
    (gammaEC eta : FiniteCoupling source target)
    (hSourceFirst :
      Integrable (fun x : Real => |x|) (source : Measure Real))
    (hTargetFirst :
      Integrable (fun y : Real => |y|) (target : Measure Real))
    (hSingular : FiniteMutuallySingular source target)
    (hAtomless : IsAtomlessFinite source)
    (hOrder : StochasticallyDominates target source)
    (hEC : IsJuilletExcursionPlan source target gammaEC.plan)
    (hEtaForward : IsForwardPlan eta)
    (hGammaLogarithmic :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (gammaEC.plan : Measure (Real × Real)))
    (hEtaLogarithmic :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Real × Real))) :
    profileCost logarithmicProfile gammaEC <=
      profileCost logarithmicProfile eta := by
  by_cases hPositive : 0 < source.mass
  · let epsilon : Nat -> Real :=
      fun k => (1 / 2 : Real) * (1 / ((k : Real) + 1))
    have hEpsilonPos : ∀ k, 0 < epsilon k := by
      intro k
      dsimp [epsilon]
      positivity
    have hEpsilonLeHalf : ∀ k, epsilon k <= 1 / 2 := by
      intro k
      have hDenominator : 1 <= (k : Real) + 1 := by
        have hk : (0 : Real) <= (k : Real) := Nat.cast_nonneg k
        linarith
      have hInv : 1 / ((k : Real) + 1) <= 1 :=
        (div_le_one (by positivity)).2 hDenominator
      dsimp [epsilon]
      nlinarith
    have hEpsilonTendsto :
        Tendsto epsilon atTop (nhds 0) := by
      have hInv :
          Tendsto (fun k : Nat => (1 : Real) / ((k : Real) + 1))
            atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [epsilon] using
        tendsto_const_nhds.mul hInv
    have hEpsilonDomain :
        ∀ k, epsilon k ∈ epsilonDomain := by
      intro k
      exact
        ⟨hEpsilonPos k,
          (hEpsilonLeHalf k).trans_lt (by norm_num)⟩
    have hSourceIdentity :
        Integrable (fun x : Real => x) (source : Measure Real) := by
      apply
        (integrable_norm_iff
          continuous_id.aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs] using hSourceFirst
    have hTargetIdentity :
        Integrable (fun y : Real => y) (target : Measure Real) := by
      apply
        (integrable_norm_iff
          continuous_id.aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs] using hTargetFirst
    have hGammaForward : IsForwardPlan gammaEC :=
      isForwardPlanOfJuilletExcursionPlan
        hAtomless hOrder hEC
    have hDistanceEq :
        distanceCost gammaEC = distanceCost eta := by
      calc
        distanceCost gammaEC =
            (∫ y, y ∂(target : Measure Real)) -
              ∫ x, x ∂(source : Measure Real) :=
          (distanceCostEqMomentDifferenceIffForward
            gammaEC hSourceIdentity hTargetIdentity).2 hGammaForward
        _ = distanceCost eta :=
          ((distanceCostEqMomentDifferenceIffForward
            eta hSourceIdentity hTargetIdentity).2 hEtaForward).symm
    have hDistanceGamma :
        Integrable (fun z : Real × Real => ‖z.1 - z.2‖)
          (gammaEC.plan : Measure (Real × Real)) :=
      distanceIntegrableOfMarginalFirstMoments
        (by simpa only [Real.norm_eq_abs] using hSourceFirst)
        (by simpa only [Real.norm_eq_abs] using hTargetFirst)
        gammaEC
    have hDistanceEta :
        Integrable (fun z : Real × Real => ‖z.1 - z.2‖)
          (eta.plan : Measure (Real × Real)) :=
      distanceIntegrableOfMarginalFirstMoments
        (by simpa only [Real.norm_eq_abs] using hSourceFirst)
        (by simpa only [Real.norm_eq_abs] using hTargetFirst)
        eta
    have hVariational :=
      oneDimensionalExcursionVariational
        source target
        (finiteCoupling_marginalMass_eq gammaEC)
        hPositive hSourceFirst hTargetFirst hSingular
        hAtomless hOrder gammaEC hEC
    have hPowerComparison :
        ∀ k,
          profileCost (powerProfile (epsilon k)) gammaEC <=
            profileCost (powerProfile (epsilon k)) eta := by
      intro k
      have hStrict :=
        powerProfile_admissibleStrict (hEpsilonDomain k)
      exact
        (hVariational.2.2.1 (powerProfile (epsilon k))
          ⟨hStrict.1.concaveOn, hStrict.2⟩).2
            eta hEtaForward
    have hGammaQuotient :
        ∀ k,
          Integrable
            (fun z : Real × Real =>
              (powerProfile (epsilon k) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon k)
            (gammaEC.plan : Measure (Real × Real)) := by
      intro k
      exact
        powerDifferenceQuotient_integrable_of_logarithmic
          (gammaEC.plan : Measure (Real × Real))
          (fun z : Real × Real => ‖z.1 - z.2‖)
          ((measurable_fst.sub measurable_snd).norm)
          (fun z => norm_nonneg _)
          (hEpsilonPos k) (hEpsilonLeHalf k)
          hGammaLogarithmic
    have hEtaQuotient :
        ∀ k,
          Integrable
            (fun z : Real × Real =>
              (powerProfile (epsilon k) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon k)
            (eta.plan : Measure (Real × Real)) := by
      intro k
      exact
        powerDifferenceQuotient_integrable_of_logarithmic
          (eta.plan : Measure (Real × Real))
          (fun z : Real × Real => ‖z.1 - z.2‖)
          ((measurable_fst.sub measurable_snd).norm)
          (fun z => norm_nonneg _)
          (hEpsilonPos k) (hEpsilonLeHalf k)
          hEtaLogarithmic
    have hQuotientComparison :
        ∀ k,
          (∫ z,
              (powerProfile (epsilon k) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon k
              ∂(gammaEC.plan : Measure (Real × Real))) <=
            ∫ z,
              (powerProfile (epsilon k) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon k
              ∂(eta.plan : Measure (Real × Real)) := by
      intro k
      have hGammaDecomposition :=
        powerProfileCostDecomposition gammaEC
          (hEpsilonPos k).ne'
          hDistanceGamma (hGammaQuotient k)
      have hEtaDecomposition :=
        powerProfileCostDecomposition eta
          (hEpsilonPos k).ne'
          hDistanceEta (hEtaQuotient k)
      have hPowerLe := hPowerComparison k
      rw [hGammaDecomposition, hEtaDecomposition,
        hDistanceEq] at hPowerLe
      have hMulLe :=
        (add_le_add_iff_left (distanceCost eta)).mp hPowerLe
      exact
        (mul_le_mul_iff_right₀ (hEpsilonPos k)).mp hMulLe
    have hGammaTendsto :
        Tendsto
          (fun k =>
            ∫ z,
              (powerProfile (epsilon k) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon k
              ∂(gammaEC.plan : Measure (Real × Real)))
          atTop
          (nhds (profileCost logarithmicProfile gammaEC)) := by
      simpa only [profileCost] using
        powerDifferenceQuotientCostTendstoOfLogarithmicIntegrable
          (gammaEC.plan : Measure (Real × Real))
          (fun z : Real × Real => ‖z.1 - z.2‖)
          ((measurable_fst.sub measurable_snd).norm)
          (fun z => norm_nonneg _)
          epsilon hEpsilonPos hEpsilonLeHalf
          hEpsilonTendsto hGammaLogarithmic
    have hEtaTendsto :
        Tendsto
          (fun k =>
            ∫ z,
              (powerProfile (epsilon k) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon k
              ∂(eta.plan : Measure (Real × Real)))
          atTop
          (nhds (profileCost logarithmicProfile eta)) := by
      simpa only [profileCost] using
        powerDifferenceQuotientCostTendstoOfLogarithmicIntegrable
          (eta.plan : Measure (Real × Real))
          (fun z : Real × Real => ‖z.1 - z.2‖)
          ((measurable_fst.sub measurable_snd).norm)
          (fun z => norm_nonneg _)
          epsilon hEpsilonPos hEpsilonLeHalf
          hEpsilonTendsto hEtaLogarithmic
    exact
      le_of_tendsto_of_tendsto hGammaTendsto hEtaTendsto
        (Eventually.of_forall hQuotientComparison)
  · have hZero : source.mass = 0 :=
      le_antisymm (le_of_not_gt hPositive) bot_le
    have hGammaZero :=
      zeroMassFiniteCouplingPlan gammaEC hZero
    have hEtaZero :=
      zeroMassFiniteCouplingPlan eta hZero
    have hEq : eta = gammaEC := by
      apply Subtype.ext
      exact hEtaZero.2.2.trans hGammaZero.2.2.symm
    rw [hEq]

private theorem existsBoundedPositiveDisjointSwapBlocks
    {source target : FiniteMeasure Real}
    {eta : FiniteCoupling source target}
    {profile : Real -> Real}
    {A : Set Real}
    {p q : Real × Real}
    (hProfileContinuous : Continuous profile)
    (hpSupport :
      p ∈ Measure.support
        (eta.plan : Measure (Real × Real)))
    (hqSupport :
      q ∈ Measure.support
        (eta.plan : Measure (Real × Real)))
    (hpCarrier : p ∈ A ×ˢ Aᶜ)
    (hqCarrier : q ∈ A ×ˢ Aᶜ)
    (hpForward : p.1 < p.2)
    (hqForward : q.1 < q.2)
    (hTie :
      dist p.1 p.2 + dist q.1 q.2 =
        dist p.1 q.2 + dist q.1 p.2)
    (hFailure :
      profile (dist p.1 q.2) +
          profile (dist q.1 p.2) <
        profile (dist p.1 p.2) +
          profile (dist q.1 q.2)) :
    exists U V : Set (Real × Real), exists delta : Real,
      IsOpen U /\
      MeasurableSet U /\
      p ∈ U /\
      U ⊆ Metric.ball p 1 /\
      IsOpen V /\
      MeasurableSet V /\
      q ∈ V /\
      V ⊆ Metric.ball q 1 /\
      Disjoint U V /\
      0 < (eta.plan.restrict U).mass /\
      0 < (eta.plan.restrict V).mass /\
      0 < delta /\
      forall r, r ∈ U -> forall s, s ∈ V ->
        r.1 < s.2 /\
        s.1 < r.2 /\
        delta <=
          profile (dist r.1 r.2) +
              profile (dist s.1 s.2) -
            (profile (dist r.1 s.2) +
              profile (dist s.1 r.2)) := by
  have hCrossed : p.1 < q.2 ∧ q.1 < p.2 :=
    strictCrossedForwardOfDistanceTieOnCarrier
      hpCarrier.1 hpCarrier.2 hqCarrier.1 hqCarrier.2
      hpForward hqForward hTie
  let gap : ((Real × Real) × (Real × Real)) -> Real :=
    fun z =>
      profile (dist z.1.1 z.1.2) +
          profile (dist z.2.1 z.2.2) -
        (profile (dist z.1.1 z.2.2) +
          profile (dist z.2.1 z.1.2))
  have hGapContinuous : Continuous gap := by
    dsimp only [gap]
    exact
      ((hProfileContinuous.comp (by fun_prop)).add
        (hProfileContinuous.comp (by fun_prop))).sub
        ((hProfileContinuous.comp (by fun_prop)).add
          (hProfileContinuous.comp (by fun_prop)))
  have hGapPositive : 0 < gap (p, q) := by
    dsimp only [gap]
    exact sub_pos.mpr hFailure
  let delta : Real := gap (p, q) / 2
  have hDeltaPositive : 0 < delta := by
    dsimp only [delta]
    exact half_pos hGapPositive
  have hDeltaLt : delta < gap (p, q) := by
    dsimp only [delta]
    exact half_lt_self hGapPositive
  have hFirstCrossedEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        z.1.1 < z.2.2 := by
    exact
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hCrossed.1
  have hSecondCrossedEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        z.2.1 < z.1.2 := by
    exact
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hCrossed.2
  have hGapEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        delta < gap z :=
    hGapContinuous.continuousAt (Ioi_mem_nhds hDeltaLt)
  have hGoodEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        z.1.1 < z.2.2 /\
          z.2.1 < z.1.2 /\
          delta <= gap z := by
    filter_upwards
      [hFirstCrossedEventually, hSecondCrossedEventually,
        hGapEventually] with z hzFirst hzSecond hzGap
    exact ⟨hzFirst, hzSecond, hzGap.le⟩
  obtain
      ⟨U0, V0, hU0Open, hpU0, hV0Open, hqV0, hU0V0Good⟩ :=
    mem_nhds_prod_iff'.mp hGoodEventually
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact lt_irrefl _ hFailure
  obtain
      ⟨Up, Vq, hUpOpen, hVqOpen, hpUp, hqVq, hSeparated⟩ :=
    t2_separation hpq
  let U : Set (Real × Real) :=
    (U0 ∩ Up) ∩ Metric.ball p 1
  let V : Set (Real × Real) :=
    (V0 ∩ Vq) ∩ Metric.ball q 1
  have hUOpen : IsOpen U :=
    (hU0Open.inter hUpOpen).inter Metric.isOpen_ball
  have hVOpen : IsOpen V :=
    (hV0Open.inter hVqOpen).inter Metric.isOpen_ball
  have hpU : p ∈ U := by
    exact ⟨⟨hpU0, hpUp⟩, by simp⟩
  have hqV : q ∈ V := by
    exact ⟨⟨hqV0, hqVq⟩, by simp⟩
  have hUBall : U ⊆ Metric.ball p 1 :=
    fun _ hz => hz.2
  have hVBall : V ⊆ Metric.ball q 1 :=
    fun _ hz => hz.2
  have hUVDisjoint : Disjoint U V :=
    hSeparated.mono
      (fun _ hz => hz.1.2)
      (fun _ hz => hz.1.2)
  have hUMeasurePositive :
      0 < (eta.plan : Measure (Real × Real)) U :=
    (Measure.mem_support_iff_forall p).mp hpSupport U
      (hUOpen.mem_nhds hpU)
  have hVMeasurePositive :
      0 < (eta.plan : Measure (Real × Real)) V :=
    (Measure.mem_support_iff_forall q).mp hqSupport V
      (hVOpen.mem_nhds hqV)
  have hUPlanPositive : 0 < eta.plan U := by
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (eta.plan : Measure (Real × Real)) U = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null eta.plan U).mp hZero
    exact hUMeasurePositive.ne' hMeasureZero
  have hVPlanPositive : 0 < eta.plan V := by
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (eta.plan : Measure (Real × Real)) V = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null eta.plan V).mp hZero
    exact hVMeasurePositive.ne' hMeasureZero
  have hURestrictPositive :
      0 < (eta.plan.restrict U).mass := by
    simpa only [FiniteMeasure.restrict_mass] using hUPlanPositive
  have hVRestrictPositive :
      0 < (eta.plan.restrict V).mass := by
    simpa only [FiniteMeasure.restrict_mass] using hVPlanPositive
  refine
    ⟨U, V, delta, hUOpen, hUOpen.measurableSet, hpU, hUBall,
      hVOpen, hVOpen.measurableSet, hqV, hVBall, hUVDisjoint,
      hURestrictPositive, hVRestrictPositive, hDeltaPositive, ?_⟩
  intro r hr s hs
  have hrs : (r, s) ∈ U0 ×ˢ V0 :=
    ⟨hr.1.1, hs.1.1⟩
  exact hU0V0Good hrs

private theorem existsForwardIntegrableReroutingOfFailedSwap
    {source target : FiniteMeasure Real}
    {eta : FiniteCoupling source target}
    {profile : Real -> Real}
    {A : Set Real}
    {p q : Real × Real}
    (hProfileContinuous : Continuous profile)
    (hEtaIntegrable :
      Integrable
        (fun z : Real × Real =>
          profile ‖z.1 - z.2‖)
        (eta.plan : Measure (Real × Real)))
    (hForward : IsForwardPlan eta)
    (hpSupport :
      p ∈ Measure.support
        (eta.plan : Measure (Real × Real)))
    (hqSupport :
      q ∈ Measure.support
        (eta.plan : Measure (Real × Real)))
    (hpCarrier : p ∈ A ×ˢ Aᶜ)
    (hqCarrier : q ∈ A ×ˢ Aᶜ)
    (hpForward : p.1 < p.2)
    (hqForward : q.1 < q.2)
    (hTie :
      dist p.1 p.2 + dist q.1 q.2 =
        dist p.1 q.2 + dist q.1 p.2)
    (hFailure :
      profile (dist p.1 q.2) +
          profile (dist q.1 p.2) <
        profile (dist p.1 p.2) +
          profile (dist q.1 q.2)) :
    ∃ xi : FiniteCoupling source target,
      IsForwardPlan xi /\
        Integrable
          (fun z : Real × Real =>
            profile ‖z.1 - z.2‖)
          (xi.plan : Measure (Real × Real)) /\
        profileCost profile xi <
          profileCost profile eta := by
  obtain
      ⟨U, V, delta, hUOpen, hUMeasurable, hpU, hUBall,
        hVOpen, hVMeasurable, hqV, hVBall, hDisjoint,
        hUPositive, hVPositive, hDelta, hBlock⟩ :=
    existsBoundedPositiveDisjointSwapBlocks
      hProfileContinuous hpSupport hqSupport hpCarrier hqCarrier
      hpForward hqForward hTie hFailure
  have hCrossed :
      ∀ᵐ r ∂(eta.plan.restrict U : Measure (Real × Real)),
        ∀ᵐ s ∂(eta.plan.restrict V : Measure (Real × Real)),
          r.1 < s.2 ∧ s.1 < r.2 := by
    filter_upwards [ae_restrict_mem hUMeasurable] with r hr
    filter_upwards [ae_restrict_mem hVMeasurable] with s hs
    exact ⟨(hBlock r hr s hs).1, (hBlock r hr s hs).2.1⟩
  obtain ⟨c, hc, hCoeffU, hCoeffV⟩ :=
    existsPositiveBalancedSwapCoefficient
      (eta.plan.restrict U).mass
      (eta.plan.restrict V).mass
  let rho : FiniteMeasure (Real × Real) :=
    eta.plan.restrict U
  let sigma : FiniteMeasure (Real × Real) :=
    eta.plan.restrict V
  let direct : FiniteMeasure (Real × Real) :=
    sigma.mass • rho + rho.mass • sigma
  let crossed : FiniteMeasure (Real × Real) :=
    (firstMarginal rho).prod (secondMarginal sigma) +
      (firstMarginal sigma).prod (secondMarginal rho)
  let removed : FiniteMeasure (Real × Real) := c • direct
  let added : FiniteMeasure (Real × Real) := c • crossed
  obtain
      ⟨remainder, xi, hXiForward, _hRemovedLe,
        _hRemainderSub, hRemainderLe, hDecomposition, hXiPlan⟩ :=
    existsForwardBalancedCrossProductReroutingCoupling eta
      ⟨hUMeasurable, hVMeasurable⟩ hDisjoint c
      hCoeffU hCoeffV hForward hCrossed
  change remainder + removed = eta.plan at hDecomposition
  change xi.plan = remainder + added at hXiPlan
  let cost : Real × Real -> Real :=
    fun z => profile (dist z.1 z.2)
  have hCostContinuous : Continuous cost := by
    exact hProfileContinuous.comp (by fun_prop)
  have hCostMeasurable : Measurable cost :=
    hCostContinuous.measurable
  have hEtaCostIntegrable :
      Integrable cost
        (eta.plan : Measure (Real × Real)) := by
    simpa only [cost, dist_eq_norm] using hEtaIntegrable
  have hRhoLe :
      (rho : Measure (Real × Real)) ≤
        (eta.plan : Measure (Real × Real)) := by
    dsimp only [rho]
    exact Measure.restrict_le_self
  have hSigmaLe :
      (sigma : Measure (Real × Real)) ≤
        (eta.plan : Measure (Real × Real)) := by
    dsimp only [sigma]
    exact Measure.restrict_le_self
  have hRhoCost :
      Integrable cost (rho : Measure (Real × Real)) :=
    hEtaCostIntegrable.mono_measure hRhoLe
  have hSigmaCost :
      Integrable cost (sigma : Measure (Real × Real)) :=
    hEtaCostIntegrable.mono_measure hSigmaLe
  let K : Set ((Real × Real) × (Real × Real)) :=
    Metric.closedBall p 1 ×ˢ Metric.closedBall q 1
  have hKCompact : IsCompact K := by
    exact
      (isCompact_closedBall p 1).prod
        (isCompact_closedBall q 1)
  have hRhoClosedBall :
      ∀ᵐ r ∂(rho : Measure (Real × Real)),
        r ∈ Metric.closedBall p 1 := by
    dsimp only [rho]
    filter_upwards [ae_restrict_mem hUMeasurable] with r hr
    exact Metric.ball_subset_closedBall (hUBall hr)
  have hSigmaClosedBall :
      ∀ᵐ s ∂(sigma : Measure (Real × Real)),
        s ∈ Metric.closedBall q 1 := by
    dsimp only [sigma]
    filter_upwards [ae_restrict_mem hVMeasurable] with s hs
    exact Metric.ball_subset_closedBall (hVBall hs)
  have hProductMem :
      ∀ᵐ rs ∂((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
        Measure ((Real × Real) × (Real × Real))),
        rs ∈ K := by
    rw [FiniteMeasure.toMeasure_prod]
    apply
      (Measure.ae_prod_iff_ae_ae hKCompact.measurableSet).2
    filter_upwards [hRhoClosedBall] with r hr
    filter_upwards [hSigmaClosedBall] with s hs
    exact ⟨hr, hs⟩
  let firstCrossedCost :
      ((Real × Real) × (Real × Real)) -> Real :=
    fun rs => profile (dist rs.1.1 rs.2.2)
  have hFirstCrossedContinuous : Continuous firstCrossedCost := by
    exact hProfileContinuous.comp (by fun_prop)
  obtain ⟨C₁, hC₁⟩ :=
    hKCompact.exists_bound_of_continuousOn
      hFirstCrossedContinuous.continuousOn
  have hFirstCrossed :
      Integrable firstCrossedCost
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    apply Integrable.of_bound
      hFirstCrossedContinuous.aestronglyMeasurable C₁
    filter_upwards [hProductMem] with rs hrs
    exact hC₁ rs hrs
  let secondCrossedCost :
      ((Real × Real) × (Real × Real)) -> Real :=
    fun rs => profile (dist rs.2.1 rs.1.2)
  have hSecondCrossedContinuous : Continuous secondCrossedCost := by
    exact hProfileContinuous.comp (by fun_prop)
  obtain ⟨C₂, hC₂⟩ :=
    hKCompact.exists_bound_of_continuousOn
      hSecondCrossedContinuous.continuousOn
  have hSecondCrossed :
      Integrable secondCrossedCost
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    apply Integrable.of_bound
      hSecondCrossedContinuous.aestronglyMeasurable C₂
    filter_upwards [hProductMem] with rs hrs
    exact hC₂ rs hrs
  have hFirstDirect :
      Integrable (fun rs : (Real × Real) × (Real × Real) =>
        cost rs.1)
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [FiniteMeasure.toMeasure_prod] using
      hRhoCost.comp_fst (sigma : Measure (Real × Real))
  have hSecondDirect :
      Integrable (fun rs : (Real × Real) × (Real × Real) =>
        cost rs.2)
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [FiniteMeasure.toMeasure_prod] using
      hSigmaCost.comp_snd (rho : Measure (Real × Real))
  let gap : ((Real × Real) × (Real × Real)) -> Real :=
    fun rs =>
      profile (dist rs.1.1 rs.1.2) +
          profile (dist rs.2.1 rs.2.2) -
        profile (dist rs.1.1 rs.2.2) -
        profile (dist rs.2.1 rs.1.2)
  have hGapIntegrable :
      Integrable gap
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [gap, cost, firstCrossedCost, secondCrossedCost,
      sub_eq_add_neg] using
      ((hFirstDirect.add hSecondDirect).sub hFirstCrossed).sub
        hSecondCrossed
  have hGapNested :
      ∀ᵐ r ∂(rho : Measure (Real × Real)),
        ∀ᵐ s ∂(sigma : Measure (Real × Real)),
          delta ≤ gap (r, s) := by
    dsimp only [rho, sigma]
    filter_upwards [ae_restrict_mem hUMeasurable] with r hr
    filter_upwards [ae_restrict_mem hVMeasurable] with s hs
    dsimp only [gap]
    linarith [(hBlock r hr s hs).2.2]
  have hGapMeasurable : Measurable gap := by
    dsimp only [gap]
    exact
      ((hCostMeasurable.comp
          (show
            Measurable
              (fun rs : (Real × Real) × (Real × Real) =>
                rs.1) by fun_prop)).add
        (hCostMeasurable.comp
          (show
            Measurable
              (fun rs : (Real × Real) × (Real × Real) =>
                rs.2) by fun_prop))).sub
        (hCostMeasurable.comp
          (show
            Measurable
              (fun rs : (Real × Real) × (Real × Real) =>
                (rs.1.1, rs.2.2)) by fun_prop)) |>.sub
        (hCostMeasurable.comp
          (show
            Measurable
              (fun rs : (Real × Real) × (Real × Real) =>
                (rs.2.1, rs.1.2)) by fun_prop))
  have hGapAE :
      ∀ᵐ rs ∂((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
        Measure ((Real × Real) × (Real × Real))),
        delta ≤ gap rs := by
    rw [FiniteMeasure.toMeasure_prod]
    exact
      (Measure.ae_prod_iff_ae_ae
        (measurableSet_le measurable_const hGapMeasurable)).2
        hGapNested
  have hGapIntegralPositive :
      0 <
        ∫ rs, gap rs
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real))) :=
    integralSwapGapPositive rho sigma
      (by simpa only [rho] using hUPositive)
      (by simpa only [sigma] using hVPositive)
      hDelta hGapIntegrable hGapAE
  have hIntegralIdentity :
      (∫ z, profile (dist z.1 z.2)
          ∂(direct : Measure (Real × Real))) -
        (∫ z, profile (dist z.1 z.2)
          ∂(crossed : Measure (Real × Real))) =
      ∫ rs, gap rs
        ∂((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [direct, crossed, gap] using
      crossProductReroutingIntegralIdentity rho sigma
        profile
        (by simpa only [cost] using hCostMeasurable)
        (by simpa only [cost] using hRhoCost)
        (by simpa only [cost] using hSigmaCost)
        (by simpa only [firstCrossedCost] using hFirstCrossed)
        (by simpa only [secondCrossedCost] using hSecondCrossed)
  have hBaseCheaper :
      (∫ z, profile (dist z.1 z.2)
          ∂(crossed : Measure (Real × Real))) <
        ∫ z, profile (dist z.1 z.2)
          ∂(direct : Measure (Real × Real)) := by
    linarith [hIntegralIdentity, hGapIntegralPositive]
  let cross :
      ((Real × Real) × (Real × Real)) -> Real × Real :=
    fun rs => (rs.1.1, rs.2.2)
  have hCrossMeasurable : Measurable cross := by
    dsimp only [cross]
    fun_prop
  have hFirstMap :
      (firstMarginal rho).prod (secondMarginal sigma) =
        (rho.prod sigma).map cross := by
    simpa only [firstMarginal, secondMarginal, cross,
      Prod.map_apply] using
      FiniteMeasure.map_prod_map rho sigma
        measurable_fst measurable_snd
  have hSecondMap :
      (firstMarginal sigma).prod (secondMarginal rho) =
        (sigma.prod rho).map cross := by
    simpa only [firstMarginal, secondMarginal, cross,
      Prod.map_apply] using
      FiniteMeasure.map_prod_map sigma rho
        measurable_fst measurable_snd
  have hFirstMapIntegrable :
      Integrable cost
        (Measure.map cross
          ((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    apply
      (integrable_map_measure hCostMeasurable.aestronglyMeasurable
        hCrossMeasurable.aemeasurable).2
    simpa only [Function.comp_apply, cost, cross,
      firstCrossedCost] using hFirstCrossed
  have hSecondProductIntegrable :
      Integrable
        (fun sr : (Real × Real) × (Real × Real) =>
          cost (sr.1.1, sr.2.2))
        ((sigma.prod rho : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [Function.comp_apply, cost,
      secondCrossedCost] using hSecondCrossed.swap
  have hSecondMapIntegrable :
      Integrable cost
        (Measure.map cross
          ((sigma.prod rho : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    apply
      (integrable_map_measure hCostMeasurable.aestronglyMeasurable
        hCrossMeasurable.aemeasurable).2
    simpa only [Function.comp_apply, cross] using
      hSecondProductIntegrable
  have hFirstAddedIntegrable :
      Integrable cost
        (((firstMarginal rho).prod (secondMarginal sigma) :
          FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) := by
    rw [hFirstMap, FiniteMeasure.toMeasure_map]
    exact hFirstMapIntegrable
  have hSecondAddedIntegrable :
      Integrable cost
        (((firstMarginal sigma).prod (secondMarginal rho) :
          FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) := by
    rw [hSecondMap, FiniteMeasure.toMeasure_map]
    exact hSecondMapIntegrable
  have hCrossedIntegrable :
      Integrable cost (crossed : Measure (Real × Real)) := by
    dsimp only [crossed]
    rw [FiniteMeasure.toMeasure_add]
    exact
      hFirstAddedIntegrable.add_measure hSecondAddedIntegrable
  have hDirectIntegrable :
      Integrable cost (direct : Measure (Real × Real)) := by
    dsimp only [direct]
    rw [FiniteMeasure.toMeasure_add]
    exact
      hRhoCost.smul_measure_nnreal.add_measure
        hSigmaCost.smul_measure_nnreal
  have hRemovedIntegrable :
      Integrable cost (removed : Measure (Real × Real)) := by
    dsimp only [removed]
    rw [FiniteMeasure.toMeasure_smul]
    exact hDirectIntegrable.smul_measure_nnreal
  have hAddedIntegrable :
      Integrable cost (added : Measure (Real × Real)) := by
    dsimp only [added]
    rw [FiniteMeasure.toMeasure_smul]
    exact hCrossedIntegrable.smul_measure_nnreal
  have hRemainderIntegrable :
      Integrable cost
        (remainder : Measure (Real × Real)) :=
    hEtaCostIntegrable.mono_measure hRemainderLe
  have hScaledCheaper :
      (∫ z, cost z ∂(added : Measure (Real × Real))) <
        ∫ z, cost z ∂(removed : Measure (Real × Real)) := by
    dsimp only [added, removed]
    rw [FiniteMeasure.toMeasure_smul,
      FiniteMeasure.toMeasure_smul,
      integral_smul_nnreal_measure,
      integral_smul_nnreal_measure]
    simpa only [NNReal.smul_def, cost] using
      mul_lt_mul_of_pos_left hBaseCheaper
        (by exact_mod_cast hc : (0 : Real) < c)
  have hXiIntegrable :
      Integrable cost
        (xi.plan : Measure (Real × Real)) := by
    rw [hXiPlan, FiniteMeasure.toMeasure_add]
    exact hRemainderIntegrable.add_measure hAddedIntegrable
  refine
    ⟨xi, hXiForward,
      (by simpa only [cost, dist_eq_norm] using hXiIntegrable),
      ?_⟩
  apply profileCostReroutingLtOfAddedLtRemoved
    hDecomposition.symm hXiPlan
  · simpa only [cost, dist_eq_norm] using hRemainderIntegrable
  · simpa only [cost, dist_eq_norm] using hRemovedIntegrable
  · simpa only [cost, dist_eq_norm] using hAddedIntegrable
  · simpa only [cost, dist_eq_norm] using hScaledCheaper

/-- Equality in the logarithmic comparison forces the competing forward
coupling to have Juillet's monotone-arch support. -/
theorem oneDimensionalLogarithmicEqualityJuilletPremise :
    OneDimensionalLogarithmicEqualityJuilletPremise := by
  intro source target gammaEC eta hSingular hAtomless hOrder hEC
    hEtaForward hGammaIntegrable hEtaIntegrable hCost
  obtain ⟨A, hA, hSourceCarrier, hTargetCarrier⟩ := hSingular
  obtain
      ⟨support, hSupportMeasurable, hSupportFull, hSupportStrict,
        hSupportCarrier⟩ :=
    existsMeasurableStrictForwardTopologicalSupportOnCarrier
      hA hSourceCarrier hTargetCarrier hEtaForward
  have hLexicographic :
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            logarithmicProfile (dist x y) +
                logarithmicProfile (dist x' y') <=
              logarithmicProfile (dist x y') +
                logarithmicProfile (dist x' y)) := by
    intro x y x' y' hxy hx'y'
    have hxyData := hSupportCarrier hxy
    have hx'y'Data := hSupportCarrier hx'y'
    have hxyForward : x < y := hSupportStrict hxy
    have hx'y'Forward : x' < y' := hSupportStrict hx'y'
    refine
      ⟨(forwardPairsDistanceTwoCycleAndReroutingOfTie
        hxyForward.le hx'y'Forward.le).1, ?_⟩
    intro hTie
    by_contra hSecondary
    have hFailure :
        logarithmicProfile (dist x y') +
            logarithmicProfile (dist x' y) <
          logarithmicProfile (dist x y) +
            logarithmicProfile (dist x' y') :=
      lt_of_not_ge hSecondary
    obtain ⟨xi, hXiForward, hXiIntegrable, hXiCheaper⟩ :=
      existsForwardLogarithmicReroutingOfFailedSwap
        hEtaIntegrable hEtaForward
        hxyData.1 hx'y'Data.1 hxyData.2 hx'y'Data.2
        hxyForward hx'y'Forward hTie hFailure
    have hGammaLeXi :
        profileCost logarithmicProfile gammaEC <=
          profileCost logarithmicProfile xi :=
      oneDimensionalLogarithmicCost_le gammaEC xi
        (by
          exact
            (integrable_norm_iff
              continuous_id.aestronglyMeasurable).mpr
              (by
                simpa only [Real.norm_eq_abs] using
                  distanceIntegrableOfMarginalFirstMoments
                    (by
                      simpa only [Real.norm_eq_abs] using
                        (integrable_norm_iff
                          continuous_id.aestronglyMeasurable).mp
                            (by
                              simpa only [Real.norm_eq_abs] using
                                hGammaIntegrable.norm)))
                    (by
                      simpa only [Real.norm_eq_abs] using
                        (integrable_norm_iff
                          continuous_id.aestronglyMeasurable).mp
                            (by
                              simpa only [Real.norm_eq_abs] using
                                hGammaIntegrable.norm))
                    gammaEC))
        (by
          exact
            (integrable_norm_iff
              continuous_id.aestronglyMeasurable).mpr
              (by
                simpa only [Real.norm_eq_abs] using
                  distanceIntegrableOfMarginalFirstMoments
                    (by
                      simpa only [Real.norm_eq_abs] using
                        (integrable_norm_iff
                          continuous_id.aestronglyMeasurable).mp
                            (by
                              simpa only [Real.norm_eq_abs] using
                                hGammaIntegrable.norm))
                    (by
                      simpa only [Real.norm_eq_abs] using
                        (integrable_norm_iff
                          continuous_id.aestronglyMeasurable).mp
                            (by
                              simpa only [Real.norm_eq_abs] using
                                hGammaIntegrable.norm))
                    gammaEC))
        hSingular hAtomless hOrder hEC hXiForward
        hGammaIntegrable hXiIntegrable
    have hEtaLeXi :
        profileCost logarithmicProfile eta <=
          profileCost logarithmicProfile xi := by
      rw [← hCost]
      exact hGammaLeXi
    exact (not_lt_of_ge hEtaLeXi) hXiCheaper
  exact
    isJuilletExcursionPlanOfLexicographicSupport
      logarithmicProfileStrictConcave hSingular hEtaForward
      hSupportMeasurable hSupportFull hLexicographic

/-- C173 power comparison implies logarithmic comparison on one line.
Equality is reduced to the explicit equality-to-Juillet premise and the
proved uniqueness of monotone-arch couplings. -/
theorem oneDimensionalLogarithmicComparison_of_equalityJuilletPremise
    (hEquality : OneDimensionalLogarithmicEqualityJuilletPremise)
    {source target : FiniteMeasure Real}
    (gammaEC eta : FiniteCoupling source target)
    (hSourceFirst :
      Integrable (fun x : Real => |x|) (source : Measure Real))
    (hTargetFirst :
      Integrable (fun y : Real => |y|) (target : Measure Real))
    (hSingular : FiniteMutuallySingular source target)
    (hAtomless : IsAtomlessFinite source)
    (hOrder : StochasticallyDominates target source)
    (hEC : IsJuilletExcursionPlan source target gammaEC.plan)
    (hEtaForward : IsForwardPlan eta)
    (hGammaLogarithmic :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (gammaEC.plan : Measure (Real × Real)))
    (hEtaLogarithmic :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Real × Real))) :
    profileCost logarithmicProfile gammaEC <=
        profileCost logarithmicProfile eta /\
      (profileCost logarithmicProfile gammaEC =
          profileCost logarithmicProfile eta ->
        eta = gammaEC) := by
  refine
    ⟨oneDimensionalLogarithmicCost_le gammaEC eta
        hSourceFirst hTargetFirst hSingular hAtomless hOrder hEC
        hEtaForward hGammaLogarithmic hEtaLogarithmic,
      ?_⟩
  intro hCost
  have hEtaExcursion :=
    hEquality gammaEC eta hSingular hAtomless hOrder hEC
      hEtaForward hGammaLogarithmic hEtaLogarithmic hCost
  exact
    (monotoneArchPlan_unique
      hAtomless hOrder gammaEC eta hEC hEtaExcursion).symm

end ConcaveOTLimit
