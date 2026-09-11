import Theorems.Thm_ConcaveOTLimit_canonicalRationalGapMeasurableSelector
import Theorems.Thm_ConcaveOTLimit_crossProductReroutingIntegralIdentity
import Theorems.Thm_ConcaveOTLimit_existsForwardBalancedCrossProductReroutingCoupling
import Theorems.Thm_ConcaveOTLimit_existsMeasurableStrictForwardTopologicalSupportOnCarrier
import Theorems.Thm_ConcaveOTLimit_forwardPairsDistanceTwoCycleAndReroutingOfTie
import Theorems.Thm_ConcaveOTLimit_globalRaywiseProfileComparison
import Theorems.Thm_ConcaveOTLimit_integralSwapGapPositive
import Theorems.Thm_ConcaveOTLimit_isJuilletExcursionPlanOfLexicographicSupport
import Theorems.Thm_ConcaveOTLimit_logarithmicProfileLePowerDifferenceQuotient
import Theorems.Thm_ConcaveOTLimit_logarithmicProfileStrictConcave
import Theorems.Thm_ConcaveOTLimit_logarithmicSecondaryUniquenessAssembly
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientOrliczBound
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientTendstoLogarithmic
import Theorems.Thm_ConcaveOTLimit_powerProfileCostDecomposition
import Theorems.Thm_ConcaveOTLimit_profileCostReroutingLtOfAddedLtRemoved
import Theorems.Thm_ConcaveOTLimit_strictCrossedForwardOfDistanceTieOnCarrier
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Theorems.Thm_ConcaveOTLimit_uniqueSecondaryMinimizer
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.Linarith

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

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

private theorem oneDimensionalLogarithmicComparison
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
    (hGammaIntegrable :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (gammaEC.plan : Measure (Real × Real)))
    (hEtaIntegrable :
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
        hEtaForward hGammaIntegrable hEtaIntegrable,
      ?_⟩
  intro hCost
  obtain ⟨A, hA, hSourceCarrier, hTargetCarrier⟩ := hSingular
  have hSingular' : FiniteMutuallySingular source target :=
    ⟨A, hA, hSourceCarrier, hTargetCarrier⟩
  obtain
      ⟨support, hSupportMeasurable, hSupportFull, hSupportStrict,
        hSupportCarrier⟩ :=
    existsMeasurableStrictForwardTopologicalSupportOnCarrier
      hA hSourceCarrier hTargetCarrier hEtaForward
  have hLexicographic :
      ∀ {x y x' y' : Real},
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
      existsForwardIntegrableReroutingOfFailedSwap
        (by
          unfold logarithmicProfile
          exact Real.continuous_negMulLog)
        hEtaIntegrable hEtaForward
        hxyData.1 hx'y'Data.1 hxyData.2 hx'y'Data.2
        hxyForward hx'y'Forward hTie hFailure
    have hGammaLeXi :
        profileCost logarithmicProfile gammaEC <=
          profileCost logarithmicProfile xi :=
      oneDimensionalLogarithmicCost_le gammaEC xi
        hSourceFirst hTargetFirst hSingular' hAtomless hOrder hEC
        hXiForward hGammaIntegrable hXiIntegrable
    have hEtaLeXi :
        profileCost logarithmicProfile eta <=
          profileCost logarithmicProfile xi := by
      rw [← hCost]
      exact hGammaLeXi
    exact (not_lt_of_ge hEtaLeXi) hXiCheaper
  have hEtaExcursion :
      IsJuilletExcursionPlan source target eta.plan :=
    isJuilletExcursionPlanOfLexicographicSupport
      logarithmicProfileStrictConcave hSingular' hEtaForward
      hSupportMeasurable hSupportFull hLexicographic
  exact
    (monotoneArchPlan_unique
      hAtomless hOrder gammaEC eta hEC hEtaExcursion).symm

namespace CanonicalRaywiseExcursionIdentification

private theorem logarithmicComparison_and_rigidity
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    {R : OrientedOpenRay n}
    {source target : FiniteMeasure (Euclidean n)}
    {physical : FiniteCoupling source target}
    {hInheritance :
      RaywiseCoordinateInheritance Gamma R source target physical.plan}
    (hIdentification :
      RaywiseExcursionIdentification
        R source target physical hInheritance)
    (eta : FiniteCoupling source target)
    (hEtaOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hEtaForward :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (hPhysicalIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (physical.plan : Measure (Euclidean n × Euclidean n)))
    (hEtaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Euclidean n × Euclidean n))) :
    profileCost logarithmicProfile physical <=
        profileCost logarithmicProfile eta /\
      (profileCost logarithmicProfile physical =
          profileCost logarithmicProfile eta ->
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
  have hCoordinatePhysical :
      hInheritance.coordinateCoupling =
        mapFiniteCoupling physical
          (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R)
          (measurable_rayCoordinate R) := by
    apply Subtype.ext
    rfl
  have hPhysicalCost :
      profileCost logarithmicProfile hInheritance.coordinateCoupling =
        profileCost logarithmicProfile physical := by
    rw [hCoordinatePhysical]
    exact
      logarithmicProfileCost_mapFiniteCoupling_rayCoordinate_eq
        R physical hInheritance.componentOnRay
  have hEtaCost :
      profileCost logarithmicProfile etaCoordinate =
        profileCost logarithmicProfile eta :=
    logarithmicProfileCost_mapFiniteCoupling_rayCoordinate_eq
      R eta hEtaOnRay
  have hCoordinatePhysicalIntegrable :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (hInheritance.coordinateCoupling.plan :
          Measure (Real × Real)) := by
    rw [hCoordinatePhysical]
    exact
      logarithmicIntegrable_mapFiniteCoupling_rayCoordinate
        R physical hInheritance.componentOnRay hPhysicalIntegrable
  have hEtaCoordinateIntegrable :
      Integrable
        (fun z : Real × Real =>
          logarithmicProfile ‖z.1 - z.2‖)
        (etaCoordinate.plan : Measure (Real × Real)) :=
    logarithmicIntegrable_mapFiniteCoupling_rayCoordinate
      R eta hEtaOnRay hEtaIntegrable
  have hCoordinateComparison :=
    oneDimensionalLogarithmicComparison
      hInheritance.coordinateCoupling etaCoordinate
      hInheritance.coordinateSourceFirstMoment
      hInheritance.coordinateTargetFirstMoment
      hInheritance.coordinateMarginalsMutuallySingular
      hInheritance.coordinateSourceAtomless
      hInheritance.coordinateTargetDominates
      hIdentification.coordinateIsExcursion
      hEtaCoordinateForward
      hCoordinatePhysicalIntegrable hEtaCoordinateIntegrable
  constructor
  · calc
      profileCost logarithmicProfile physical =
          profileCost logarithmicProfile
            hInheritance.coordinateCoupling :=
        hPhysicalCost.symm
      _ <= profileCost logarithmicProfile etaCoordinate :=
        hCoordinateComparison.1
      _ = profileCost logarithmicProfile eta := hEtaCost
  · intro hCost
    have hCoordinateCost :
        profileCost logarithmicProfile
            hInheritance.coordinateCoupling =
          profileCost logarithmicProfile etaCoordinate := by
      calc
        profileCost logarithmicProfile
            hInheritance.coordinateCoupling =
            profileCost logarithmicProfile physical :=
          hPhysicalCost
        _ = profileCost logarithmicProfile eta := hCost
        _ = profileCost logarithmicProfile etaCoordinate :=
          hEtaCost.symm
    have hCoordinateEq :
        etaCoordinate = hInheritance.coordinateCoupling :=
      hCoordinateComparison.2 hCoordinateCost
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

end CanonicalRaywiseExcursionIdentification

private theorem maximalRayFiber_logarithmicComparison_and_rigidity
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n)
    (hIdentification :
      CanonicalRaywiseExcursionIdentification
        D gamma gammaLift R)
    (eta : FiniteCoupling mu nu)
    (hCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (maximalRayInputComponentFiber D eta R))
    (hOnRay :
      ∀ᵐ z ∂D.component eta R,
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hForward :
      ∀ᵐ z ∂D.component eta R,
        rayCoordinate R z.1 <= rayCoordinate R z.2)
    (hAssembledIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (assembledRaywiseKernel D gamma gammaLift R))
    (hEtaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (D.component eta R)) :
    (∫ z, logarithmicProfile ‖z.1 - z.2‖
        ∂assembledRaywiseKernel D gamma gammaLift R) <=
        ∫ z, logarithmicProfile ‖z.1 - z.2‖
          ∂D.component eta R /\
      ((∫ z, logarithmicProfile ‖z.1 - z.2‖
          ∂assembledRaywiseKernel D gamma gammaLift R) =
          ∫ z, logarithmicProfile ‖z.1 - z.2‖
            ∂D.component eta R ->
        D.component eta R =
          assembledRaywiseKernel D gamma gammaLift R) := by
  obtain ⟨hAssembledCoupling, _hInheritance, hExcursion⟩ :=
    hIdentification
  let etaPhysical :
      FiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R) :=
    ⟨maximalRayInputComponentFiber D eta R, hCoupling⟩
  have hLocal :=
    CanonicalRaywiseExcursionIdentification.logarithmicComparison_and_rigidity
      hExcursion etaPhysical
      (by
        simpa only [etaPhysical,
          maximalRayInputComponentFiber_toMeasure] using hOnRay)
      (by
        simpa only [etaPhysical,
          maximalRayInputComponentFiber_toMeasure] using hForward)
      (by
        simpa only [assembledRaywisePhysicalCoupling_plan,
          assembledRaywiseComponentFiber_toMeasure] using
            hAssembledIntegrable)
      (by
        simpa only [etaPhysical,
          maximalRayInputComponentFiber_toMeasure] using
            hEtaIntegrable)
  constructor
  · simpa only [profileCost,
      assembledRaywisePhysicalCoupling_plan,
      assembledRaywiseComponentFiber_toMeasure,
      etaPhysical, maximalRayInputComponentFiber_toMeasure] using
        hLocal.1
  · intro hCost
    have hLocalCost :
        profileCost logarithmicProfile
            (assembledRaywisePhysicalCoupling
              D gamma gammaLift R hAssembledCoupling) =
          profileCost logarithmicProfile etaPhysical := by
      simpa only [profileCost,
        assembledRaywisePhysicalCoupling_plan,
        assembledRaywiseComponentFiber_toMeasure,
        etaPhysical, maximalRayInputComponentFiber_toMeasure] using
          hCost
    have hPhysicalEq :
        etaPhysical =
          assembledRaywisePhysicalCoupling
            D gamma gammaLift R hAssembledCoupling :=
      hLocal.2 hLocalCost
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

private def assembledRaywiseLogarithmicFiberCost
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n) : Real :=
  ∫ z, logarithmicProfile ‖z.1 - z.2‖
    ∂assembledRaywiseKernel D gamma gammaLift R

private def maximalRayCompetitorLogarithmicFiberCost
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (eta : FiniteCoupling mu nu)
    (R : OrientedOpenRay n) : Real :=
  ∫ z, logarithmicProfile ‖z.1 - z.2‖ ∂D.component eta R

private structure AssembledRaywiseLogarithmicPointwiseData
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (eta : FiniteCoupling mu nu) : Prop where
  raywiseLe :
    assembledRaywiseLogarithmicFiberCost D gamma gammaLift ≤ᵐ[
      (D.sigma : Measure (OrientedOpenRay n))]
        maximalRayCompetitorLogarithmicFiberCost D eta
  assembledFiberPointwiseIntegrable :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (assembledRaywiseKernel D gamma gammaLift R)
  etaFiberPointwiseIntegrable :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (D.component eta R)

private structure AssembledRaywiseLogarithmicIntegralData
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (eta : FiniteCoupling mu nu) : Prop where
  assembledFiberIntegrable :
    Integrable
      (assembledRaywiseLogarithmicFiberCost D gamma gammaLift)
      (D.sigma : Measure (OrientedOpenRay n))
  etaFiberIntegrable :
    Integrable
      (maximalRayCompetitorLogarithmicFiberCost D eta)
      (D.sigma : Measure (OrientedOpenRay n))
  assembledIntegral :
    profileCost logarithmicProfile
        (assembledRaywiseCoupling
          D gamma hSupported gammaLift) =
      ∫ R, assembledRaywiseLogarithmicFiberCost
        D gamma gammaLift R
        ∂(D.sigma : Measure (OrientedOpenRay n))
  etaIntegral :
    profileCost logarithmicProfile eta =
      ∫ R, maximalRayCompetitorLogarithmicFiberCost D eta R
        ∂(D.sigma : Measure (OrientedOpenRay n))

private theorem assembledRaywiseLogarithmicFiberIntegrability
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (eta : FiniteCoupling mu nu)
    (hEta : IsSupported eta Gamma)
    (hAssembledIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)))
    (hEtaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Euclidean n × Euclidean n))) :
    (∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (assembledRaywiseKernel D gamma gammaLift R)) /\
      (∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            logarithmicProfile ‖z.1 - z.2‖)
          (D.component eta R)) := by
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
  constructor
  · have hComp :
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            logarithmicProfile ‖z.1 - z.2‖)
          (assembledRaywiseKernel D gamma gammaLift ∘ₘ
            (D.sigma : Measure (OrientedOpenRay n))) := by
      rw [assembledRaywiseKernel_reconstruction
        D gamma hSupported gammaLift]
      exact hAssembledIntegrable
    exact
      ((Measure.integrable_comp_iff
        hComp.aestronglyMeasurable).mp hComp).1
  · have hComp :
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            logarithmicProfile ‖z.1 - z.2‖)
          (D.component eta ∘ₘ
            (D.sigma : Measure (OrientedOpenRay n))) := by
      rw [D.component_reconstruction eta hEta]
      exact hEtaIntegrable
    exact
      ((Measure.integrable_comp_iff
        hComp.aestronglyMeasurable).mp hComp).1

private theorem assembledRaywiseLogarithmicFiberCost_le
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hIdentification :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        CanonicalRaywiseExcursionIdentification
          D gamma gammaLift R)
    (eta : FiniteCoupling mu nu)
    (hEta : IsSupported eta Gamma)
    (hAssembledFiberPointwiseIntegrable :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            logarithmicProfile ‖z.1 - z.2‖)
          (assembledRaywiseKernel D gamma gammaLift R))
    (hEtaFiberPointwiseIntegrable :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            logarithmicProfile ‖z.1 - z.2‖)
          (D.component eta R)) :
    assembledRaywiseLogarithmicFiberCost D gamma gammaLift ≤ᵐ[
      (D.sigma : Measure (OrientedOpenRay n))]
        maximalRayCompetitorLogarithmicFiberCost D eta := by
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
  have hEtaCoupling :=
    supportedCompetitorComponent_isCoupling_ae
      D gamma eta hSupported hEta
  have hEtaOnRay :=
    D.component_endpoints_mem_closure_ae eta hEta
  have hEtaForward :=
    maximalRayComponent_coordinate_forward_ae D eta hEta
  filter_upwards
      [hIdentification, hEtaCoupling, hEtaOnRay, hEtaForward,
        hAssembledFiberPointwiseIntegrable,
        hEtaFiberPointwiseIntegrable] with
      R hRIdentification hRCoupling hROnRay hRForward
        hRAssembledIntegrable hREtaIntegrable
  simpa only [assembledRaywiseLogarithmicFiberCost,
    maximalRayCompetitorLogarithmicFiberCost] using
    (maximalRayFiber_logarithmicComparison_and_rigidity
      D gamma gammaLift R hRIdentification eta hRCoupling
      hROnRay hRForward hRAssembledIntegrable
      hREtaIntegrable).1

private theorem assembledRaywiseLogarithmicPointwiseData
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hIdentification :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        CanonicalRaywiseExcursionIdentification
          D gamma gammaLift R)
    (eta : FiniteCoupling mu nu)
    (hEta : IsSupported eta Gamma)
    (hAssembledIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)))
    (hEtaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Euclidean n × Euclidean n))) :
    AssembledRaywiseLogarithmicPointwiseData
      D gamma gammaLift eta := by
  obtain
      ⟨hAssembledFiberPointwiseIntegrable,
        hEtaFiberPointwiseIntegrable⟩ :=
    assembledRaywiseLogarithmicFiberIntegrability
      D gamma hSupported gammaLift eta hEta
      hAssembledIntegrable hEtaIntegrable
  exact
    { raywiseLe :=
        assembledRaywiseLogarithmicFiberCost_le
          D gamma hSupported gammaLift hIdentification eta hEta
          hAssembledFiberPointwiseIntegrable
          hEtaFiberPointwiseIntegrable
      assembledFiberPointwiseIntegrable :=
        hAssembledFiberPointwiseIntegrable
      etaFiberPointwiseIntegrable := hEtaFiberPointwiseIntegrable }

set_option maxHeartbeats 500000 in
private theorem assembledRaywiseLogarithmicIntegralData
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (eta : FiniteCoupling mu nu)
    (hEta : IsSupported eta Gamma)
    (hAssembledIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)))
    (hEtaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Euclidean n × Euclidean n))) :
    AssembledRaywiseLogarithmicIntegralData
      D gamma hSupported gammaLift eta := by
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
  have hAssembledCompIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (assembledRaywiseKernel D gamma gammaLift ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) := by
    rw [assembledRaywiseKernel_reconstruction
      D gamma hSupported gammaLift]
    exact hAssembledIntegrable
  have hEtaCompIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (D.component eta ∘ₘ
          (D.sigma : Measure (OrientedOpenRay n))) := by
    rw [D.component_reconstruction eta hEta]
    exact hEtaIntegrable
  have hCostStronglyMeasurable :
      StronglyMeasurable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖) := by
    unfold logarithmicProfile
    exact
      (Real.continuous_negMulLog.comp
        ((continuous_fst.sub continuous_snd).norm)).stronglyMeasurable
  have hAssembledFiberIntegrable :
      Integrable
        (assembledRaywiseLogarithmicFiberCost D gamma gammaLift)
        (D.sigma : Measure (OrientedOpenRay n)) := by
    simpa only [assembledRaywiseLogarithmicFiberCost] using
      integrable_integral_kernel_of_comp
        (D.sigma : Measure (OrientedOpenRay n))
        (assembledRaywiseKernel D gamma gammaLift)
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        hCostStronglyMeasurable hAssembledCompIntegrable
  have hEtaFiberIntegrable :
      Integrable
        (maximalRayCompetitorLogarithmicFiberCost D eta)
        (D.sigma : Measure (OrientedOpenRay n)) := by
    simpa only [maximalRayCompetitorLogarithmicFiberCost] using
      integrable_integral_kernel_of_comp
        (D.sigma : Measure (OrientedOpenRay n))
        (D.component eta)
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        hCostStronglyMeasurable hEtaCompIntegrable
  have hAssembledIntegral :
      profileCost logarithmicProfile
          (assembledRaywiseCoupling
            D gamma hSupported gammaLift) =
        ∫ R, assembledRaywiseLogarithmicFiberCost
          D gamma gammaLift R
          ∂(D.sigma : Measure (OrientedOpenRay n)) := by
    simpa only [profileCost,
      assembledRaywiseLogarithmicFiberCost] using
      integral_eq_integral_kernel_of_reconstruction
        (D.sigma : Measure (OrientedOpenRay n))
        (assembledRaywiseKernel D gamma gammaLift)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n))
        (assembledRaywiseKernel_reconstruction
          D gamma hSupported gammaLift)
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        hAssembledIntegrable
  have hEtaIntegral :
      profileCost logarithmicProfile eta =
        ∫ R, maximalRayCompetitorLogarithmicFiberCost D eta R
          ∂(D.sigma : Measure (OrientedOpenRay n)) := by
    simpa only [profileCost,
      maximalRayCompetitorLogarithmicFiberCost] using
      integral_eq_integral_kernel_of_reconstruction
        (D.sigma : Measure (OrientedOpenRay n))
        (D.component eta)
        (eta.plan : Measure (Euclidean n × Euclidean n))
        (D.component_reconstruction eta hEta)
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        hEtaIntegrable
  exact
    { assembledFiberIntegrable := hAssembledFiberIntegrable
      etaFiberIntegrable := hEtaFiberIntegrable
      assembledIntegral := hAssembledIntegral
      etaIntegral := hEtaIntegral }

private theorem
    assembledRaywiseCoupling_logarithmicComparison_and_rigidity
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hIdentification :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        CanonicalRaywiseExcursionIdentification
          D gamma gammaLift R)
    (eta : FiniteCoupling mu nu)
    (hEta : IsSupported eta Gamma)
    (hAssembledIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        ((assembledRaywiseCoupling
          D gamma hSupported gammaLift).plan :
            Measure (Euclidean n × Euclidean n)))
    (hEtaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (eta.plan : Measure (Euclidean n × Euclidean n))) :
    profileCost logarithmicProfile
        (assembledRaywiseCoupling
          D gamma hSupported gammaLift) <=
      profileCost logarithmicProfile eta /\
        (profileCost logarithmicProfile
              (assembledRaywiseCoupling
                D gamma hSupported gammaLift) =
            profileCost logarithmicProfile eta ->
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
  let hPointwise :=
    assembledRaywiseLogarithmicPointwiseData
      D gamma hSupported gammaLift hIdentification eta hEta
      hAssembledIntegrable hEtaIntegrable
  let hIntegral :=
    assembledRaywiseLogarithmicIntegralData
      D gamma hSupported gammaLift eta hEta
      hAssembledIntegrable hEtaIntegrable
  have hEtaCoupling :=
    supportedCompetitorComponent_isCoupling_ae
      D gamma eta hSupported hEta
  have hEtaOnRay :=
    D.component_endpoints_mem_closure_ae eta hEta
  have hEtaForward :=
    maximalRayComponent_coordinate_forward_ae D eta hEta
  refine ⟨?_, ?_⟩
  · rw [hIntegral.assembledIntegral, hIntegral.etaIntegral]
    exact
      integral_mono_ae
        hIntegral.assembledFiberIntegrable
        hIntegral.etaFiberIntegrable hPointwise.raywiseLe
  · intro hGlobalCost
    have hFiberCostEq :
        assembledRaywiseLogarithmicFiberCost D gamma gammaLift =ᵐ[
          (D.sigma : Measure (OrientedOpenRay n))]
            maximalRayCompetitorLogarithmicFiberCost D eta := by
      apply
        (integral_eq_iff_of_ae_le
          hIntegral.assembledFiberIntegrable
          hIntegral.etaFiberIntegrable hPointwise.raywiseLe).mp
      rw [← hIntegral.assembledIntegral, ← hIntegral.etaIntegral]
      exact hGlobalCost
    have hComponentEq :
        D.component eta =ᵐ[
          (D.sigma : Measure (OrientedOpenRay n))]
            assembledRaywiseKernel D gamma gammaLift := by
      filter_upwards
          [hIdentification, hEtaCoupling, hEtaOnRay, hEtaForward,
            hPointwise.assembledFiberPointwiseIntegrable,
            hPointwise.etaFiberPointwiseIntegrable, hFiberCostEq] with
          R hRIdentification hRCoupling hROnRay hRForward
            hRAssembledIntegrable hREtaIntegrable hRCost
      apply
        (maximalRayFiber_logarithmicComparison_and_rigidity
          D gamma gammaLift R hRIdentification eta hRCoupling
          hROnRay hRForward hRAssembledIntegrable
          hREtaIntegrable).2
      exact hRCost
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

/-- Theorem 9: the intrinsic generalized excursion plan is also the unique
minimizer of the logarithmic secondary cost. -/
theorem logarithmicSecondaryUniqueness
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsUniqueSecondaryMinimizer
            logarithmicProfile gammaSharp := by
  let hMarginals := marginalHypothesesOfPower n mu nu hPower
  obtain
      ⟨gammaSharp, tSharp, hGraph, hIntrinsic,
        _uIntrinsic, _huIntrinsic, _GammaIntrinsic,
        _hGammaIntrinsic, _hSigmaIntrinsic,
        _hDisintegrationIntrinsic⟩ :=
    uniqueSecondaryMinimizer n mu nu hMarginals
  have hHalf : (1 / 2 : Real) ∈ epsilonDomain := by
    constructor <;> norm_num
  have hPowerStrict :
      AdmissibleStrictlyConcaveProfile
        (powerProfile (1 / 2)) :=
    powerProfile_admissibleStrict hHalf
  have hPowerConcave :
      AdmissibleConcaveProfile (powerProfile (1 / 2)) :=
    ⟨hPowerStrict.1.concaveOn, hPowerStrict.2⟩
  have hIntrinsicPower :
      IsUniqueSecondaryMinimizer
        (powerProfile (1 / 2)) gammaSharp :=
    hIntrinsic (powerProfile (1 / 2)) hPowerStrict
  have hGammaOptimal : IsDistanceOptimal gammaSharp :=
    hIntrinsicPower.1.1
  obtain ⟨w⟩ :=
    nonemptyDistanceDualWitness_of_marginalHypotheses
      n mu nu hMarginals
  let u :=
    uniqueSecondaryDistancePotential n mu nu hMarginals w
  let Gamma :=
    uniqueSecondaryContactSet n mu nu hMarginals w
  have hu : LipschitzWith 1 u := by
    simpa only [u] using
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals w).1
  have hContactCharacterization :
      ∀ eta : FiniteCoupling mu nu,
        IsDistanceOptimal eta <->
          IsSupported eta (distanceContactSet u) := by
    simpa only [u] using
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals w).2.1
  have hSigma : IsSigmaCompact Gamma := by
    simpa only [Gamma] using
      uniqueSecondaryContactSet_isSigmaCompact
        n mu nu hMarginals w
  have hDiagonal : ∀ x, (x, x) ∉ Gamma := by
    simpa only [Gamma] using
      uniqueSecondaryContactSet_diagonalFree
        n mu nu hMarginals w
  have hContactSubset : Gamma ⊆ distanceContactSet u := by
    simpa only [Gamma, u] using
      uniqueSecondaryContactSet_subset
        n mu nu hMarginals w
  have hSupportedOfOptimal :
      ∀ eta : FiniteCoupling mu nu,
        IsDistanceOptimal eta -> IsSupported eta Gamma := by
    intro eta hEtaOptimal
    have hEtaContact :
        IsSupported eta (distanceContactSet u) :=
      (hContactCharacterization eta).1 hEtaOptimal
    change
      IsSupported eta
        (distanceContactSet u \
          {z : Euclidean n × Euclidean n | z.1 = z.2})
    exact
      (isSupported_diagonalRemoved_iff
        eta hMarginals.mutuallySingular
        (distanceContactSet u)).2 hEtaContact
  have hGammaSupported : IsSupported gammaSharp Gamma :=
    hSupportedOfOptimal gammaSharp hGammaOptimal
  have hVolumeRegularity :
      Nonempty
        (RayRegularityHypotheses
          (volume : Measure (Euclidean n)) Gamma) :=
    (contactSetRayRegularity
      n mu nu hMarginals u hu Gamma hSigma hDiagonal
      hContactSubset).2.2
  let hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma :=
    (Classical.choice hVolumeRegularity).of_absolutelyContinuous
      hMarginals.sourceAbsolutelyContinuous
  let D : MaximalRayKernelDisintegration n mu nu Gamma :=
    Classical.choice
      (existsMaximalRayKernelDisintegration
        n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
        ⟨gammaSharp, hGammaSupported⟩)
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  have hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay :=
    countablyLipschitzRayCoordinateAtomlessPremise
      mu Gamma hRegularity D.rayAssignment D.defaultRay
  have hSelection :
      MaximalRayKernelDisintegration.CanonicalRayForwardRationalGapMeasurableSelectionPremise
        D gammaSharp :=
    MaximalRayKernelDisintegration.canonicalRayForwardRationalGapMeasurableSelectionPremise
      D gammaSharp
  obtain
      ⟨gammaLift, hCanonical, _hFiberMinimal, hIdentification⟩ :=
    existsCanonicalRayLiftedMinimizer_with_raywiseExcursionIdentification_of_weakPremise
      D hRegularity gammaSharp hGammaSupported
      hMarginals.sourceAbsolutelyContinuous hAtomless
      hMarginals.mutuallySingular
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
      hSelection
  have hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n) :=
    hCanonical.1
  let gammaRay : FiniteCoupling mu nu :=
    assembledRaywiseCoupling
      D gammaSharp hGammaSupported gammaLift
  have hGammaRayOptimal : IsDistanceOptimal gammaRay := by
    simpa only [gammaRay] using
      assembledRaywiseCoupling_isDistanceOptimal_of_input
        D gammaSharp hGammaSupported gammaLift hLiftedForward
        hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        hGammaOptimal
  have hPowerComparison :=
    assembledRaywiseCoupling_profileComparison_and_strictRigidity
      D gammaSharp hGammaSupported gammaLift
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
      hIdentification gammaSharp hGammaSupported
      (powerProfile (1 / 2)) hPowerConcave
  have hGammaLeRay :
      profileCost (powerProfile (1 / 2)) gammaSharp <=
        profileCost (powerProfile (1 / 2)) gammaRay :=
    hIntrinsicPower.1.2 gammaRay hGammaRayOptimal
  have hPowerCostEq :
      profileCost (powerProfile (1 / 2))
          (assembledRaywiseCoupling
            D gammaSharp hGammaSupported gammaLift) =
        profileCost (powerProfile (1 / 2)) gammaSharp := by
    exact le_antisymm hPowerComparison.1
      (by simpa only [gammaRay] using hGammaLeRay)
  have hGammaEqRay :
      gammaSharp = gammaRay := by
    simpa only [gammaRay] using
      hPowerComparison.2 hPowerStrict hPowerCostEq
  have hGammaRayLogIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (gammaRay.plan :
          Measure (Euclidean n × Euclidean n)) :=
    logarithmicCostIntegrableOfMarginalLogMoments
      hPower.sourceLogMoment hPower.targetLogMoment gammaRay
  have hLogarithmicComparison :
      ∀ eta : FiniteCoupling mu nu,
        IsDistanceOptimal eta ->
          profileCost logarithmicProfile gammaRay <=
              profileCost logarithmicProfile eta /\
            (profileCost logarithmicProfile gammaRay =
                profileCost logarithmicProfile eta ->
              eta = gammaRay) := by
    intro eta hEtaOptimal
    have hEtaSupported : IsSupported eta Gamma :=
      hSupportedOfOptimal eta hEtaOptimal
    have hEtaLogIntegrable :
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            logarithmicProfile ‖z.1 - z.2‖)
          (eta.plan : Measure (Euclidean n × Euclidean n)) :=
      logarithmicCostIntegrableOfMarginalLogMoments
        hPower.sourceLogMoment hPower.targetLogMoment eta
    simpa only [gammaRay] using
      assembledRaywiseCoupling_logarithmicComparison_and_rigidity
        D gammaSharp hGammaSupported gammaLift hIdentification
        eta hEtaSupported hGammaRayLogIntegrable hEtaLogIntegrable
  have hLogarithmicUnique :
      IsUniqueSecondaryMinimizer
        logarithmicProfile gammaSharp := by
    refine ⟨⟨hGammaOptimal, ?_⟩, ?_⟩
    · intro eta hEtaOptimal
      have hComparison :=
        (hLogarithmicComparison eta hEtaOptimal).1
      simpa only [hGammaEqRay] using hComparison
    · intro eta hEtaMinimizer
      have hEtaOptimal : IsDistanceOptimal eta :=
        hEtaMinimizer.1
      have hComparison :=
        hLogarithmicComparison eta hEtaOptimal
      have hSharpLeEta :
          profileCost logarithmicProfile gammaSharp <=
            profileCost logarithmicProfile eta := by
        simpa only [hGammaEqRay] using hComparison.1
      have hEtaLeSharp :
          profileCost logarithmicProfile eta <=
            profileCost logarithmicProfile gammaSharp :=
        hEtaMinimizer.2 gammaSharp hGammaOptimal
      have hRayCostEq :
          profileCost logarithmicProfile gammaRay =
            profileCost logarithmicProfile eta := by
        rw [← hGammaEqRay]
        exact le_antisymm hSharpLeEta hEtaLeSharp
      exact (hComparison.2 hRayCostEq).trans hGammaEqRay.symm
  exact
    ⟨gammaSharp, tSharp, hGraph, hIntrinsic, hLogarithmicUnique⟩

#print axioms logarithmicSecondaryUniqueness

end ConcaveOTLimit
