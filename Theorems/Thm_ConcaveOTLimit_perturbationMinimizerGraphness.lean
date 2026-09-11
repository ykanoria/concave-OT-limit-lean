import Definitions.Def_PerturbationMinimizerGraphPremise
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_concaveProfileDistanceLowerSemicontinuous
import Theorems.Thm_ConcaveOTLimit_distanceCyclicMonotoneSufficiency
import Theorems.Thm_ConcaveOTLimit_existsFiniteMeasureRemainderOfLe
import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular
import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer
import Theorems.Thm_ConcaveOTLimit_finiteMeasureReplacementPreservesMarginals
import Theorems.Thm_ConcaveOTLimit_profileCostReroutingLtOfAddedLtRemoved
import Theorems.Thm_ConcaveOTLimit_sInfLipschitzFamily
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialTouchUniqueness
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Support

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ConcaveOTLimit

variable {n : Nat}

private def radialIncrement (profile : Real -> Real) (r : Real) : Real :=
  profile r - profile 0

private theorem strictMonoOn_of_monotoneOn_of_strictConcaveOn_Ici
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile) :
    StrictMonoOn profile (Ici 0) := by
  intro a ha b hb hab
  have habLe : profile a <= profile b := hMono ha hb hab.le
  apply lt_of_le_of_ne habLe
  intro hEq
  let m : Real := (a + b) / 2
  have ha0 : 0 <= a := ha
  have hb0 : 0 <= b := hb
  have hm0 : 0 <= m := by
    dsimp only [m]
    linarith
  have hmb : m <= b := by
    dsimp only [m]
    linarith
  have hMidLe : profile m <= profile b :=
    hMono hm0 hb hmb
  have hMidStrict :=
    hStrict.lt_on_open_segment' ha hb hab.ne
      (a := (1 / 2 : Real)) (b := (1 / 2 : Real))
      (by norm_num) (by norm_num) (by norm_num)
  have hMidEq :
      (1 / 2 : Real) • a + (1 / 2 : Real) • b = m := by
    dsimp only [m]
    simp only [smul_eq_mul]
    ring
  rw [hMidEq, hEq] at hMidStrict
  simp only [min_self] at hMidStrict
  linarith

private theorem radialIncrement_nonnegative
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    {r : Real} (hr : 0 <= r) :
    0 <= radialIncrement profile r := by
  exact sub_nonneg.mpr (hMono (by simp) hr hr)

private theorem radialIncrement_pos
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    0 < radialIncrement profile r := by
  exact sub_pos.mpr
    (strictMonoOn_of_monotoneOn_of_strictConcaveOn_Ici hMono hStrict
      (by simp) hr.le hr)

private theorem radialIncrement_subadditive
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {a b : Real} (ha : 0 <= a) (hb : 0 <= b) :
    radialIncrement profile (a + b) <=
      radialIncrement profile a + radialIncrement profile b := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, radialIncrement]
  · have hsPos : 0 < a + b :=
      lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
    have hwa : 0 <= a / (a + b) := div_nonneg ha hsPos.le
    have hwb : 0 <= b / (a + b) := div_nonneg hb hsPos.le
    have hwSum : a / (a + b) + b / (a + b) = 1 := by
      field_simp
    have hA :=
      hConcave.2 hsPos.le (show (0 : Real) ∈ Ici 0 by simp)
        hwa hwb hwSum
    have hB :=
      hConcave.2 hsPos.le (show (0 : Real) ∈ Ici 0 by simp)
        hwb hwa (by linarith [hwSum])
    simp only [smul_eq_mul, mul_zero, add_zero] at hA hB
    have hArgA :
        a / (a + b) * (a + b) = a := by
      field_simp
    have hArgB :
        b / (a + b) * (a + b) = b := by
      field_simp
    rw [hArgA] at hA
    rw [hArgB] at hB
    dsimp only [radialIncrement]
    have hCoeff :
        a / (a + b) * profile (a + b) +
              b / (a + b) * profile 0 +
            (b / (a + b) * profile (a + b) +
              a / (a + b) * profile 0) =
          profile (a + b) + profile 0 := by
      calc
        _ =
            (a / (a + b) + b / (a + b)) * profile (a + b) +
              (a / (a + b) + b / (a + b)) * profile 0 := by
          ring
        _ = _ := by rw [hwSum]; ring
    linarith

private theorem radialIncrement_triangle
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {a b c : Euclidean n} :
    radialIncrement profile ‖a - c‖ <=
      radialIncrement profile ‖a - b‖ +
        radialIncrement profile ‖b - c‖ := by
  calc
    radialIncrement profile ‖a - c‖ <=
        radialIncrement profile (‖a - b‖ + ‖b - c‖) := by
      apply sub_le_sub_right
      apply hMono (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      exact norm_sub_le_norm_sub_add_norm_sub a b c
    _ <= _ :=
      radialIncrement_subadditive hConcave (norm_nonneg _) (norm_nonneg _)

private theorem exists_profile_lipschitzOn_Icc
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {d M : Real} (hd : 0 < d) :
    exists K : NNReal, LipschitzOnWith K profile (Icc d M) := by
  have hLocal : LocallyLipschitzOn (Ioi (0 : Real)) profile := by
    simpa only [interior_Ici] using hConcave.locallyLipschitzOn_interior
  have hSubset : Icc d M ⊆ Ioi (0 : Real) := by
    intro r hr
    exact hd.trans_le hr.1
  exact
    (hLocal.mono hSubset).exists_lipschitzOnWith_of_compact
      isCompact_Icc

private def profileSupergradient
    (profile : Real -> Real) (r : Real) : Real :=
  -derivWithin (fun t => -profile t) (Ioi r) r

private theorem hasDerivWithinAt_profileSupergradient
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    HasDerivWithinAt profile (profileSupergradient profile r)
      (Ioi r) r := by
  have hrInterior : r ∈ interior (Ici (0 : Real)) := by
    simpa only [interior_Ici] using hr
  have hNeg :=
    hConcave.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hrInterior
  simpa only [profileSupergradient, neg_neg] using hNeg.neg

private theorem profile_le_tangent
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {r t : Real} (hr : 0 < r) (ht : 0 <= t) :
    profile t <=
      profile r + profileSupergradient profile r * (t - r) := by
  let p := profileSupergradient profile r
  have hpDeriv :
      HasDerivWithinAt profile p (Ioi r) r :=
    hasDerivWithinAt_profileSupergradient hConcave hr
  rcases lt_trichotomy t r with htr | rfl | hrt
  · have hrInterior : r ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici] using hr
    have hNegRight :
        HasDerivWithinAt (fun s => -profile s) (-p) (Ioi r) r := by
      simpa only [p, profileSupergradient, neg_neg] using hpDeriv.neg
    have hNegLeftDiff :
        DifferentiableWithinAt Real (fun s => -profile s) (Iio r) r :=
      hConcave.neg.differentiableWithinAt_Iio_of_mem_interior hrInterior
    have hLeftLeRight :
        derivWithin (fun s => -profile s) (Iio r) r <= -p := by
      have :=
        hConcave.neg.leftDeriv_le_rightDeriv_of_mem_interior hrInterior
      exact this.trans_eq
        (hNegRight.derivWithin (uniqueDiffWithinAt_Ioi r))
    have hSlopeLe :
        slope (fun s => -profile s) t r <= -p := by
      exact
        (hConcave.neg.slope_le_leftDeriv ht hr.le htr
          hNegLeftDiff).trans hLeftLeRight
    rw [slope_def_field] at hSlopeLe
    have hden : 0 < r - t := sub_pos.mpr htr
    have :=
      (div_le_iff₀ hden).mp (by
        simpa only [Pi.neg_apply, neg_sub_neg] using hSlopeLe)
    linarith
  · simp
  · have hSlopeLe :
        slope profile r t <= p :=
      hConcave.slope_le_of_hasDerivWithinAt_Ioi
        hr.le ht hrt hpDeriv
    rw [slope_def_field] at hSlopeLe
    have := (div_le_iff₀ (sub_pos.mpr hrt)).mp hSlopeLe
    linarith

private theorem profileSupergradient_pos
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    0 < profileSupergradient profile r := by
  let s := r + 1
  have hrs : r < s := by dsimp only [s]; linarith
  have hs0 : 0 <= s := hr.le.trans hrs.le
  have hProfileLt :
      profile r < profile s :=
    strictMonoOn_of_monotoneOn_of_strictConcaveOn_Ici hMono hStrict
      hr.le hs0 hrs
  have hSlopePos : 0 < slope profile r s := by
    rw [slope_def_field]
    positivity
  have hSlopeLt :
      slope profile r s < profileSupergradient profile r :=
    hStrict.slope_lt_of_hasDerivWithinAt_Ioi
      hr.le hs0 hrs
      (hasDerivWithinAt_profileSupergradient hStrict.concaveOn hr)
  exact hSlopePos.trans hSlopeLt

private theorem profileSupergradient_strictAnti
    {profile : Real -> Real}
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r s : Real} (hr : 0 < r) (hrs : r < s) :
    profileSupergradient profile s <
      profileSupergradient profile r := by
  have hs : 0 < s := hr.trans hrs
  have hAtR :=
    hasDerivWithinAt_profileSupergradient hStrict.concaveOn hr
  have hAtS :=
    hasDerivWithinAt_profileSupergradient hStrict.concaveOn hs
  have hSlopeLt :
      slope profile r s < profileSupergradient profile r :=
    hStrict.slope_lt_of_hasDerivWithinAt_Ioi
      hr.le hs.le hrs hAtR
  have hSuperLeSlope :
      profileSupergradient profile s <= slope profile r s := by
    have hsInterior : s ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici] using hs
    have hNegRight :
        HasDerivWithinAt (fun t => -profile t)
          (-profileSupergradient profile s) (Ioi s) s := by
      simpa only [neg_neg] using hAtS.neg
    have hNegLeftDiff :
        DifferentiableWithinAt Real (fun t => -profile t) (Iio s) s :=
      hStrict.concaveOn.neg.differentiableWithinAt_Iio_of_mem_interior
        hsInterior
    have hLeftLeRight :
        derivWithin (fun t => -profile t) (Iio s) s <=
          -profileSupergradient profile s := by
      have :=
        hStrict.concaveOn.neg.leftDeriv_le_rightDeriv_of_mem_interior
          hsInterior
      exact this.trans_eq
        (hNegRight.derivWithin (uniqueDiffWithinAt_Ioi s))
    have hNegSlope :
        slope (fun t => -profile t) r s <=
          -profileSupergradient profile s :=
      (hStrict.concaveOn.neg.slope_le_leftDeriv
        hr.le hs.le hrs hNegLeftDiff).trans hLeftLeRight
    simpa only [slope_neg, neg_le_neg_iff] using hNegSlope
  exact hSuperLeSlope.trans_lt hSlopeLt

private def IsProfileCyclicallyMonotone
    {E : Type*} [NormedAddCommGroup E]
    (profile : Real -> Real) (Gamma : Set (E × E)) : Prop :=
  ∀ {I : Type} [Fintype I] (x y : I -> E),
    (∀ i, (x i, y i) ∈ Gamma) ->
      ∀ sigma : Equiv.Perm I,
        (∑ i, profile ‖x i - y i‖) <=
          ∑ i, profile ‖x i - y (sigma i)‖

private theorem firstMarginal_mass_eq'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (firstMarginal rho).mass = rho.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass]
  exact FiniteMeasure.map_apply rho measurable_fst MeasurableSet.univ
    |>.trans (by simp)

private theorem secondMarginal_mass_eq'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (secondMarginal rho).mass = rho.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass]
  exact FiniteMeasure.map_apply rho measurable_snd MeasurableSet.univ
    |>.trans (by simp)

private theorem firstMarginal_crossProduct'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho sigma : FiniteMeasure (X × Y)) :
    firstMarginal
        ((firstMarginal rho).prod (secondMarginal sigma)) =
      sigma.mass • firstMarginal rho := by
  unfold firstMarginal
  rw [FiniteMeasure.map_fst_prod]
  change
    (secondMarginal sigma).mass • rho.map Prod.fst =
      sigma.mass • rho.map Prod.fst
  rw [secondMarginal_mass_eq']

private theorem secondMarginal_crossProduct'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho sigma : FiniteMeasure (X × Y)) :
    secondMarginal
        ((firstMarginal rho).prod (secondMarginal sigma)) =
      rho.mass • secondMarginal sigma := by
  unfold secondMarginal
  rw [FiniteMeasure.map_snd_prod]
  change
    (firstMarginal rho).mass • sigma.map Prod.snd =
      rho.mass • sigma.map Prod.snd
  rw [firstMarginal_mass_eq']

private theorem firstMarginal_fintypeSum'
    {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (rho : I -> FiniteMeasure (X × Y)) :
    firstMarginal (∑ i, rho i) = ∑ i, firstMarginal (rho i) := by
  apply FiniteMeasure.toMeasure_injective
  simp only [firstMarginal, FiniteMeasure.toMeasure_map,
    FiniteMeasure.toMeasure_sum]
  change
    Measure.map Prod.fst
        (∑ i, (rho i : Measure (X × Y))) =
      ∑ i, Measure.map Prod.fst (rho i : Measure (X × Y))
  exact Measure.map_finset_sum' measurable_fst.aemeasurable

private theorem secondMarginal_fintypeSum'
    {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (rho : I -> FiniteMeasure (X × Y)) :
    secondMarginal (∑ i, rho i) = ∑ i, secondMarginal (rho i) := by
  apply FiniteMeasure.toMeasure_injective
  simp only [secondMarginal, FiniteMeasure.toMeasure_map,
    FiniteMeasure.toMeasure_sum]
  change
    Measure.map Prod.snd
        (∑ i, (rho i : Measure (X × Y))) =
      ∑ i, Measure.map Prod.snd (rho i : Measure (X × Y))
  exact Measure.map_finset_sum' measurable_snd.aemeasurable

private theorem firstMarginal_smul'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : NNReal) (rho : FiniteMeasure (X × Y)) :
    firstMarginal (c • rho) = c • firstMarginal rho := by
  unfold firstMarginal
  exact FiniteMeasure.map_smul c rho

private theorem secondMarginal_smul'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : NNReal) (rho : FiniteMeasure (X × Y)) :
    secondMarginal (c • rho) = c • secondMarginal rho := by
  unfold secondMarginal
  exact FiniteMeasure.map_smul c rho

private theorem normalizedRestriction_mass'
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) (_hRho : rho ≠ 0) :
    rho.normalize.toFiniteMeasure.mass = 1 :=
  ProbabilityMeasure.mass_toFiniteMeasure rho.normalize

private theorem normalizedRestriction_mem_ae'
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) (s : Set Omega)
    (hs : MeasurableSet s) (hRho : rho.restrict s ≠ 0) :
    ∀ᵐ z ∂((rho.restrict s).normalize.toFiniteMeasure :
      Measure Omega), z ∈ s := by
  rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero _ hRho,
    FiniteMeasure.toMeasure_smul]
  exact Measure.ae_smul_measure (ae_restrict_mem hs) _

private theorem integrable_and_integral_bounds_of_ae_abs_sub_lt
    {Omega : Type*} [MeasurableSpace Omega]
    (rho : FiniteMeasure Omega) (cost : Omega -> Real)
    (hCost : Measurable cost)
    (center delta : Real) (_hDelta : 0 <= delta)
    (hMass : rho.mass = 1)
    (hNear :
      ∀ᵐ z ∂(rho : Measure Omega),
        |cost z - center| < delta) :
    Integrable cost (rho : Measure Omega) /\
      center - delta <=
        ∫ z, cost z ∂(rho : Measure Omega) /\
      (∫ z, cost z ∂(rho : Measure Omega)) <=
        center + delta := by
  have hIntegrable :
      Integrable cost (rho : Measure Omega) := by
    refine (integrable_const (|center| + delta)).mono'
      hCost.aestronglyMeasurable ?_
    filter_upwards [hNear] with z hz
    calc
      ‖cost z‖ = |cost z| := Real.norm_eq_abs _
      _ = |center + (cost z - center)| := by
        congr 1
        ring
      _ <= |center| + |cost z - center| :=
        abs_add_le center (cost z - center)
      _ <= |center| + delta :=
        add_le_add le_rfl hz.le
  have hConstantIntegral (c : Real) :
      (∫ _z : Omega, c ∂(rho : Measure Omega)) = c := by
    rw [integral_const]
    simp only [FiniteMeasure.measureReal_eq_coe_coeFn, smul_eq_mul]
    change (rho.mass : Real) * c = c
    rw [hMass]
    simp
  refine ⟨hIntegrable, ?_, ?_⟩
  · calc
      center - delta =
          ∫ _z : Omega, center - delta
            ∂(rho : Measure Omega) :=
        (hConstantIntegral _).symm
      _ <= ∫ z, cost z ∂(rho : Measure Omega) := by
        apply integral_mono_ae (integrable_const _) hIntegrable
        filter_upwards [hNear] with z hz
        linarith [(abs_lt.mp hz).1]
  · calc
      (∫ z, cost z ∂(rho : Measure Omega)) <=
          ∫ _z : Omega, center + delta
            ∂(rho : Measure Omega) := by
        apply integral_mono_ae hIntegrable (integrable_const _)
        filter_upwards [hNear] with z hz
        linarith [(abs_lt.mp hz).2]
      _ = center + delta := hConstantIntegral _

private theorem profileCost_continuousAt_of_ne
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {x y : Euclidean n} (hxy : x ≠ y) :
    ContinuousAt
      (fun z : Euclidean n × Euclidean n =>
        profile ‖z.1 - z.2‖) (x, y) := by
  have hDistPos : 0 < ‖x - y‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hProfile :
      ContinuousAt profile ‖x - y‖ := by
    exact
      (hConcave.continuousOn_interior
        ‖x - y‖
        (by simpa only [interior_Ici] using hDistPos)).continuousAt
        (by simpa only [interior_Ici] using Ioi_mem_nhds hDistPos)
  exact hProfile.comp_of_eq
    ((continuous_fst.sub continuous_snd).norm.continuousAt) rfl

private theorem exists_common_profileCost_radius
    {I : Type*} [Fintype I] [Nonempty I]
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    (x y : I -> Euclidean n)
    (hCrossNe : ∀ i j, x i ≠ y j)
    {delta : Real} (hDelta : 0 < delta) :
    ∃ r : Real, 0 < r ∧
      ∀ i j (z : Euclidean n × Euclidean n),
        z.1 ∈ Metric.ball (x i) r ->
        z.2 ∈ Metric.ball (y j) r ->
        |profile ‖z.1 - z.2‖ -
            profile ‖x i - y j‖| < delta := by
  let cost : Euclidean n × Euclidean n -> Real :=
    fun z => profile ‖z.1 - z.2‖
  have hRadius (p : I × I) :
      ∃ r : Real, 0 < r ∧
        ∀ z ∈ Metric.ball (x p.1, y p.2) r,
          |cost z - cost (x p.1, y p.2)| < delta := by
    have hCont :
        ContinuousAt cost (x p.1, y p.2) := by
      exact profileCost_continuousAt_of_ne
        hConcave (hCrossNe p.1 p.2)
    have hEventually :
        {z | |cost z - cost (x p.1, y p.2)| < delta} ∈
          𝓝 (x p.1, y p.2) := by
      have hBall :
          Metric.ball (cost (x p.1, y p.2)) delta ∈
            𝓝 (cost (x p.1, y p.2)) :=
        Metric.ball_mem_nhds _ hDelta
      have := hCont hBall
      simpa only [Set.preimage_setOf_eq, Real.dist_eq] using this
    obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hEventually
    exact ⟨r, hr, fun z hz => hBall hz⟩
  choose radius hRadiusPos hRadiusGood using hRadius
  let r : Real :=
    Finset.univ.inf' Finset.univ_nonempty radius
  have hr : 0 < r := by
    apply
      (Finset.lt_inf'_iff (s := Finset.univ)
        Finset.univ_nonempty).2
    intro p _hp
    exact hRadiusPos p
  refine ⟨r, hr, ?_⟩
  intro i j z hzi hzj
  have hrLe : r <= radius (i, j) :=
    Finset.inf'_le _ (Finset.mem_univ (i, j))
  have hMem :
      z ∈ Metric.ball (x i, y j) (radius (i, j)) := by
    rw [← ball_prod_same]
    exact
      ⟨Metric.mem_ball.mpr
          ((Metric.mem_ball.mp hzi).trans_le hrLe),
        Metric.mem_ball.mpr
          ((Metric.mem_ball.mp hzj).trans_le hrLe)⟩
  simpa only [cost] using hRadiusGood (i, j) z hMem

private theorem profileMinimizer_supportCarrier_cyclic
    (n : Nat)
    {mu nu : FiniteMeasure (Euclidean n)}
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    (hCostMeasurable :
      Measurable
        (fun z : Euclidean n × Euclidean n =>
          profile ‖z.1 - z.2‖))
    (gamma : FiniteCoupling mu nu)
    (hGammaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          profile ‖z.1 - z.2‖)
        (gamma.plan : Measure (Euclidean n × Euclidean n)))
    (hMin : IsProfileMinimizer profile gamma)
    (A : Set (Euclidean n)) :
    IsProfileCyclicallyMonotone profile
      (Measure.support
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)) ∩
        (A ×ˢ Aᶜ)) := by
  classical
  intro I _ x y hSupport sigma
  cases isEmpty_or_nonempty I with
  | inl hEmpty =>
      letI := hEmpty
      simp
  | inr hNonempty =>
      letI := hNonempty
      by_contra hCycle
      let directCenter : Real :=
        ∑ i, profile ‖x i - y i‖
      let crossedCenter : Real :=
        ∑ i, profile ‖x i - y (sigma i)‖
      have hCenterStrict : crossedCenter < directCenter :=
        lt_of_not_ge hCycle
      let cardReal : Real := Fintype.card I
      have hCardReal : 0 < cardReal := by
        dsimp only [cardReal]
        exact_mod_cast Fintype.card_pos
      let delta : Real :=
        (directCenter - crossedCenter) / (4 * cardReal)
      have hDelta : 0 < delta := by
        dsimp only [delta]
        positivity
      have hDeltaSmall :
          2 * cardReal * delta <
            directCenter - crossedCenter := by
        have hCardRealNe : cardReal ≠ 0 := ne_of_gt hCardReal
        calc
          2 * cardReal * delta =
              (directCenter - crossedCenter) / 2 := by
            dsimp only [delta]
            field_simp
            ring
          _ < directCenter - crossedCenter := by
            linarith
      have hCrossNe (i j : I) : x i ≠ y j := by
        intro hEq
        have hxA : x i ∈ A := (hSupport i).2.1
        have hyA : y j ∉ A := (hSupport j).2.2
        exact hyA (hEq ▸ hxA)
      obtain ⟨r, hr, hCostNear⟩ :=
        exists_common_profileCost_radius
          hConcave x y hCrossNe hDelta
      let U : I -> Set (Euclidean n × Euclidean n) :=
        fun i => Metric.ball (x i) r ×ˢ Metric.ball (y i) r
      have hUOpen (i : I) : IsOpen (U i) :=
        Metric.isOpen_ball.prod Metric.isOpen_ball
      have hUMeasurable (i : I) : MeasurableSet (U i) :=
        (hUOpen i).measurableSet
      have hPointMem (i : I) : (x i, y i) ∈ U i :=
        ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
      let tau : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
        fun i => gamma.plan.restrict (U i)
      have hTauMassPositive (i : I) : 0 < (tau i).mass := by
        have hMeasurePositive :
            0 <
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) (U i) :=
          (Measure.mem_support_iff_forall (x i, y i)).mp
            (hSupport i).1 (U i)
            ((hUOpen i).mem_nhds (hPointMem i))
        have hPlanPositive : 0 < gamma.plan (U i) := by
          apply pos_iff_ne_zero.mpr
          intro hZero
          have hMeasureZero :
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) (U i) = 0 :=
            (FiniteMeasure.null_iff_toMeasure_null gamma.plan (U i)).mp
              hZero
          exact hMeasurePositive.ne' hMeasureZero
        simpa only [tau, FiniteMeasure.restrict_mass] using
          hPlanPositive
      have hTauNonzero (i : I) : tau i ≠ 0 :=
        (FiniteMeasure.mass_nonzero_iff (tau i)).mp
          (hTauMassPositive i).ne'
      let rho : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
        fun i => (tau i).normalize.toFiniteMeasure
      have hRhoMass (i : I) : (rho i).mass = 1 :=
        normalizedRestriction_mass' (tau i) (hTauNonzero i)
      have hRhoSupported (i : I) :
          ∀ᵐ z ∂(rho i :
            Measure (Euclidean n × Euclidean n)),
            z.1 ∈ Metric.ball (x i) r ∧
              z.2 ∈ Metric.ball (y i) r := by
        simpa only [rho, tau, U] using
          normalizedRestriction_mem_ae' gamma.plan (U i)
            (hUMeasurable i) (hTauNonzero i)
      let crossed :
          I -> FiniteMeasure (Euclidean n × Euclidean n) :=
        fun i =>
          (firstMarginal (rho i)).prod
            (secondMarginal (rho (sigma i)))
      have hCrossedMass (i : I) : (crossed i).mass = 1 := by
        calc
          (crossed i).mass =
              (firstMarginal (crossed i)).mass :=
            (firstMarginal_mass_eq' (crossed i)).symm
          _ = (firstMarginal (rho i)).mass := by
            rw [firstMarginal_crossProduct', hRhoMass]
            simp
          _ = (rho i).mass := firstMarginal_mass_eq' (rho i)
          _ = 1 := hRhoMass i
      have hFirstSupported (i : I) :
          ∀ᵐ a ∂(firstMarginal (rho i) :
            Measure (Euclidean n)),
            a ∈ Metric.ball (x i) r := by
        change
          ∀ᵐ a ∂Measure.map Prod.fst
            (rho i : Measure (Euclidean n × Euclidean n)),
            a ∈ Metric.ball (x i) r
        apply
          (ae_map_iff (p := fun a => a ∈ Metric.ball (x i) r)
            measurable_fst.aemeasurable
            Metric.isOpen_ball.measurableSet).2
        filter_upwards [hRhoSupported i] with z hz
        exact hz.1
      have hSecondSupported (i : I) :
          ∀ᵐ b ∂(secondMarginal (rho (sigma i)) :
            Measure (Euclidean n)),
            b ∈ Metric.ball (y (sigma i)) r := by
        change
          ∀ᵐ b ∂Measure.map Prod.snd
            (rho (sigma i) :
              Measure (Euclidean n × Euclidean n)),
            b ∈ Metric.ball (y (sigma i)) r
        apply
          (ae_map_iff
            (p := fun b => b ∈ Metric.ball (y (sigma i)) r)
            measurable_snd.aemeasurable
            Metric.isOpen_ball.measurableSet).2
        filter_upwards [hRhoSupported (sigma i)] with z hz
        exact hz.2
      have hCrossedSupported (i : I) :
          ∀ᵐ z ∂(crossed i :
            Measure (Euclidean n × Euclidean n)),
            z.1 ∈ Metric.ball (x i) r ∧
              z.2 ∈ Metric.ball (y (sigma i)) r := by
        rw [show
          (crossed i : Measure (Euclidean n × Euclidean n)) =
            (firstMarginal (rho i) :
              Measure (Euclidean n)).prod
              (secondMarginal (rho (sigma i)) :
                Measure (Euclidean n)) by
          rfl]
        apply
          (Measure.ae_prod_iff_ae_ae
            ((Metric.isOpen_ball.measurableSet.prod
              Metric.isOpen_ball.measurableSet))).2
        filter_upwards [hFirstSupported i] with a ha
        filter_upwards [hSecondSupported i] with b hb
        exact ⟨ha, hb⟩
      have hDirectNear (i : I) :
          ∀ᵐ z ∂(rho i :
            Measure (Euclidean n × Euclidean n)),
            |profile ‖z.1 - z.2‖ -
              profile ‖x i - y i‖| < delta := by
        filter_upwards [hRhoSupported i] with z hz
        exact hCostNear i i z hz.1 hz.2
      have hCrossedNear (i : I) :
          ∀ᵐ z ∂(crossed i :
            Measure (Euclidean n × Euclidean n)),
            |profile ‖z.1 - z.2‖ -
              profile ‖x i - y (sigma i)‖| < delta := by
        filter_upwards [hCrossedSupported i] with z hz
        exact hCostNear i (sigma i) z hz.1 hz.2
      have hDirectData (i : I) :
          Integrable
              (fun z : Euclidean n × Euclidean n =>
                profile ‖z.1 - z.2‖)
              (rho i :
                Measure (Euclidean n × Euclidean n)) /\
            profile ‖x i - y i‖ - delta <=
              ∫ z, profile ‖z.1 - z.2‖
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n)) /\
            (∫ z, profile ‖z.1 - z.2‖
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n))) <=
              profile ‖x i - y i‖ + delta :=
        integrable_and_integral_bounds_of_ae_abs_sub_lt
          (rho i)
          (fun z : Euclidean n × Euclidean n =>
            profile ‖z.1 - z.2‖)
          hCostMeasurable
          (profile ‖x i - y i‖) delta hDelta.le
          (hRhoMass i) (hDirectNear i)
      have hCrossedData (i : I) :
          Integrable
              (fun z : Euclidean n × Euclidean n =>
                profile ‖z.1 - z.2‖)
              (crossed i :
                Measure (Euclidean n × Euclidean n)) /\
            profile ‖x i - y (sigma i)‖ - delta <=
              ∫ z, profile ‖z.1 - z.2‖
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n)) /\
            (∫ z, profile ‖z.1 - z.2‖
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n))) <=
              profile ‖x i - y (sigma i)‖ + delta :=
        integrable_and_integral_bounds_of_ae_abs_sub_lt
          (crossed i)
          (fun z : Euclidean n × Euclidean n =>
            profile ‖z.1 - z.2‖)
          hCostMeasurable
          (profile ‖x i - y (sigma i)‖) delta hDelta.le
          (hCrossedMass i) (hCrossedNear i)
      let direct :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        ∑ i, rho i
      let rerouted :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        ∑ i, crossed i
      have hDirectIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              profile ‖z.1 - z.2‖)
            (direct : Measure (Euclidean n × Euclidean n)) := by
        dsimp only [direct]
        rw [FiniteMeasure.toMeasure_sum]
        exact integrable_finsetSum_measure.mpr fun i _ =>
          (hDirectData i).1
      have hReroutedIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              profile ‖z.1 - z.2‖)
            (rerouted : Measure (Euclidean n × Euclidean n)) := by
        dsimp only [rerouted]
        rw [FiniteMeasure.toMeasure_sum]
        exact integrable_finsetSum_measure.mpr fun i _ =>
          (hCrossedData i).1
      have hDirectIntegral :
          (∫ z, profile ‖z.1 - z.2‖
              ∂(direct :
                Measure (Euclidean n × Euclidean n))) =
            ∑ i,
              ∫ z, profile ‖z.1 - z.2‖
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n)) := by
        dsimp only [direct]
        rw [FiniteMeasure.toMeasure_sum]
        exact integral_finsetSum_measure fun i _ => (hDirectData i).1
      have hReroutedIntegral :
          (∫ z, profile ‖z.1 - z.2‖
              ∂(rerouted :
                Measure (Euclidean n × Euclidean n))) =
            ∑ i,
              ∫ z, profile ‖z.1 - z.2‖
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n)) := by
        dsimp only [rerouted]
        rw [FiniteMeasure.toMeasure_sum]
        exact
          integral_finsetSum_measure fun i _ => (hCrossedData i).1
      have hDirectLower :
          directCenter - cardReal * delta <=
            ∑ i,
              ∫ z, profile ‖z.1 - z.2‖
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n)) := by
        calc
          directCenter - cardReal * delta =
              ∑ i, (profile ‖x i - y i‖ - delta) := by
            simp [directCenter, cardReal]
          _ <=
              ∑ i,
                ∫ z, profile ‖z.1 - z.2‖
                  ∂(rho i :
                    Measure (Euclidean n × Euclidean n)) :=
            Finset.sum_le_sum fun i _ => (hDirectData i).2.1
      have hReroutedUpper :
          (∑ i,
              ∫ z, profile ‖z.1 - z.2‖
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n))) <=
            crossedCenter + cardReal * delta := by
        calc
          (∑ i,
              ∫ z, profile ‖z.1 - z.2‖
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n))) <=
              ∑ i,
                (profile ‖x i - y (sigma i)‖ + delta) :=
            Finset.sum_le_sum fun i _ => (hCrossedData i).2.2
          _ = crossedCenter + cardReal * delta := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
            dsimp only [crossedCenter, cardReal]
      have hReroutedCheaper :
          (∫ z, profile ‖z.1 - z.2‖
              ∂(rerouted :
                Measure (Euclidean n × Euclidean n))) <
            ∫ z, profile ‖z.1 - z.2‖
              ∂(direct :
                Measure (Euclidean n × Euclidean n)) := by
        rw [hDirectIntegral, hReroutedIntegral]
        linarith
      have hFirstMarginalRerouted :
          firstMarginal rerouted = firstMarginal direct := by
        rw [show firstMarginal rerouted =
            ∑ i, firstMarginal (crossed i) by
          exact firstMarginal_fintypeSum' crossed]
        rw [show firstMarginal direct =
            ∑ i, firstMarginal (rho i) by
          exact firstMarginal_fintypeSum' rho]
        apply Fintype.sum_congr
        intro i
        rw [firstMarginal_crossProduct', hRhoMass]
        simp
      have hSecondMarginalRerouted :
          secondMarginal rerouted = secondMarginal direct := by
        rw [show secondMarginal rerouted =
            ∑ i, secondMarginal (crossed i) by
          exact secondMarginal_fintypeSum' crossed]
        rw [show secondMarginal direct =
            ∑ i, secondMarginal (rho i) by
          exact secondMarginal_fintypeSum' rho]
        calc
          (∑ i, secondMarginal (crossed i)) =
              ∑ i, secondMarginal (rho (sigma i)) := by
            apply Fintype.sum_congr
            intro i
            rw [secondMarginal_crossProduct', hRhoMass]
            simp
          _ = ∑ i, secondMarginal (rho i) :=
            Equiv.sum_comp sigma (fun i => secondMarginal (rho i))
      let minimumMass : NNReal :=
        Finset.univ.inf' Finset.univ_nonempty
          (fun i => (tau i).mass)
      have hMinimumMassPositive : 0 < minimumMass := by
        apply
          (Finset.lt_inf'_iff (s := Finset.univ)
            Finset.univ_nonempty).2
        intro i _hi
        exact hTauMassPositive i
      have hMinimumMassLe (i : I) :
          minimumMass <= (tau i).mass :=
        Finset.inf'_le _ (Finset.mem_univ i)
      let cardNN : NNReal := Fintype.card I
      have hCardNN : 0 < cardNN := by
        dsimp only [cardNN]
        exact_mod_cast Fintype.card_pos
      let c : NNReal := minimumMass / cardNN
      have hc : 0 < c := by
        dsimp only [c]
        positivity
      let removed :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        c • direct
      let added :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        c • rerouted
      have hFirstMarginalAdded :
          firstMarginal added = firstMarginal removed := by
        dsimp only [added, removed]
        rw [firstMarginal_smul', firstMarginal_smul',
          hFirstMarginalRerouted]
      have hSecondMarginalAdded :
          secondMarginal added = secondMarginal removed := by
        dsimp only [added, removed]
        rw [secondMarginal_smul', secondMarginal_smul',
          hSecondMarginalRerouted]
      have hCoefficientLe (i : I) :
          c * (tau i).mass⁻¹ <= cardNN⁻¹ := by
        rw [show c * (tau i).mass⁻¹ = c / (tau i).mass by
          rw [div_eq_mul_inv]]
        rw [show cardNN⁻¹ = 1 / cardNN by
          rw [one_div]]
        apply
          (div_le_div_iff₀ (hTauMassPositive i) hCardNN).2
        dsimp only [c]
        rw [div_mul_cancel₀ _ hCardNN.ne']
        simpa using hMinimumMassLe i
      have hBlockLe (i : I) :
          (((c • rho i :
              FiniteMeasure (Euclidean n × Euclidean n))) :
              Measure (Euclidean n × Euclidean n)) <=
            (((cardNN⁻¹ • gamma.plan :
              FiniteMeasure (Euclidean n × Euclidean n))) :
              Measure (Euclidean n × Euclidean n)) := by
        have hTauLe :
            (tau i :
                Measure (Euclidean n × Euclidean n)) <=
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) := by
          dsimp only [tau]
          exact Measure.restrict_le_self
        change
          c • (rho i :
              Measure (Euclidean n × Euclidean n)) <=
            cardNN⁻¹ •
              (gamma.plan :
                Measure (Euclidean n × Euclidean n))
        rw [show
          (rho i :
              Measure (Euclidean n × Euclidean n)) =
            (tau i).mass⁻¹ •
              (tau i :
                Measure (Euclidean n × Euclidean n)) by
          dsimp only [rho]
          rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero
            _ (hTauNonzero i), FiniteMeasure.toMeasure_smul]]
        rw [smul_smul]
        apply Measure.le_iff'.2
        intro s
        simp only [Measure.coe_nnreal_smul_apply]
        exact
          mul_le_mul
            (ENNReal.coe_le_coe.mpr (hCoefficientLe i))
            (hTauLe s) (by exact bot_le) (by exact bot_le)
      have hConstantSum :
          (∑ _i : I, cardNN⁻¹ • gamma.plan) = gamma.plan := by
        rw [← Finset.sum_smul]
        simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        change (cardNN * cardNN⁻¹) • gamma.plan = gamma.plan
        rw [mul_inv_cancel₀ hCardNN.ne']
        simp
      have hRemovedAsSum :
          removed = ∑ i, c • rho i := by
        dsimp only [removed, direct]
        simpa only using
          (Finset.smul_sum
            (s := Finset.univ) (r := c) (f := rho))
      have hRemovedLe :
          (removed :
              Measure (Euclidean n × Euclidean n)) <=
            (gamma.plan :
              Measure (Euclidean n × Euclidean n)) := by
        rw [hRemovedAsSum, FiniteMeasure.toMeasure_sum]
        calc
          (∑ i,
              ((c • rho i :
                FiniteMeasure (Euclidean n × Euclidean n)) :
                Measure (Euclidean n × Euclidean n))) <=
              ∑ i,
                ((cardNN⁻¹ • gamma.plan :
                  FiniteMeasure
                    (Euclidean n × Euclidean n)) :
                  Measure (Euclidean n × Euclidean n)) :=
            Finset.sum_le_sum fun i _ => hBlockLe i
          _ = (gamma.plan :
                Measure (Euclidean n × Euclidean n)) := by
            rw [← FiniteMeasure.toMeasure_sum, hConstantSum]
      have hRemovedIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              profile ‖z.1 - z.2‖)
            (removed :
              Measure (Euclidean n × Euclidean n)) := by
        dsimp only [removed]
        exact hDirectIntegrable.smul_measure_nnreal
      have hAddedIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              profile ‖z.1 - z.2‖)
            (added :
              Measure (Euclidean n × Euclidean n)) := by
        dsimp only [added]
        exact hReroutedIntegrable.smul_measure_nnreal
      have hAddedCheaper :
          (∫ z, profile ‖z.1 - z.2‖
              ∂(added :
                Measure (Euclidean n × Euclidean n))) <
            ∫ z, profile ‖z.1 - z.2‖
              ∂(removed :
                Measure (Euclidean n × Euclidean n)) := by
        dsimp only [added, removed]
        simp only [FiniteMeasure.toMeasure_smul,
          integral_smul_nnreal_measure]
        exact
          mul_lt_mul_of_pos_left hReroutedCheaper
            (by exact_mod_cast hc)
      obtain
          ⟨remainder, _hRemainderEq, hRemainderLe,
            hDecomposition⟩ :=
        existsFiniteMeasureRemainderOfLe
          gamma.plan removed hRemovedLe
      have hReplacementMarginals :=
        finiteMeasureReplacementPreservesMarginals
          remainder removed added gamma.plan hDecomposition
          hFirstMarginalAdded hSecondMarginalAdded
      let etaPlan :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        remainder + added
      let eta : FiniteCoupling mu nu :=
        ⟨etaPlan,
          ⟨hReplacementMarginals.1.trans gamma.property.1,
            hReplacementMarginals.2.trans gamma.property.2⟩⟩
      have hRemainderIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              profile ‖z.1 - z.2‖)
            (remainder :
              Measure (Euclidean n × Euclidean n)) :=
        hGammaIntegrable.mono_measure hRemainderLe
      have hEtaCheaper :
          profileCost profile eta < profileCost profile gamma := by
        exact
          profileCostReroutingLtOfAddedLtRemoved
            (profile := profile) (gamma := gamma) (eta := eta)
            (remainder := remainder) (removed := removed)
            (added := added) hDecomposition.symm rfl
            hRemainderIntegrable hRemovedIntegrable hAddedIntegrable
            hAddedCheaper
      have hOptimalLe :
          profileCost profile gamma <= profileCost profile eta :=
        hMin.2 eta (mem_univ eta)
      exact (not_lt_of_ge hOptimalLe) hEtaCheaper

private structure ProfileMetric (n : Nat) where
  point : Euclidean n

@[reducible]
private def profilePseudoMetricSpace
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hConcave : ConcaveOn Real (Ici 0) profile) :
    PseudoMetricSpace (ProfileMetric n) where
  dist x y := radialIncrement profile ‖x.point - y.point‖
  dist_self x := by simp [radialIncrement]
  dist_comm x y := by
    rw [norm_sub_rev]
  dist_triangle x y z :=
    radialIncrement_triangle hMono hConcave

private theorem exists_profileContactPotential
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hConcave : ConcaveOn Real (Ici 0) profile)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hCyclic : IsProfileCyclicallyMonotone profile Gamma) :
    ∃ u : Euclidean n -> Real,
      (∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖) /\
      ∀ z ∈ Gamma,
        radialIncrement profile ‖z.1 - z.2‖ =
          u z.1 - u z.2 := by
  letI : PseudoMetricSpace (ProfileMetric n) :=
    profilePseudoMetricSpace hMono hConcave
  let Gamma' : Set (ProfileMetric n × ProfileMetric n) :=
    {z | (z.1.point, z.2.point) ∈ Gamma}
  have hDistanceCyclic :
      IsDistanceCyclicallyMonotone.{0, 0} Gamma' := by
    intro I _ x y hxy sigma
    change
      (∑ i,
        radialIncrement profile ‖(x i).point - (y i).point‖) <=
        ∑ i,
          radialIncrement profile
            ‖(x i).point - (y (sigma i)).point‖
    rw [show
        (∑ i,
          radialIncrement profile ‖(x i).point - (y i).point‖) =
            (∑ i, profile ‖(x i).point - (y i).point‖) -
              ∑ _i : I, profile 0 by
      simp only [radialIncrement, Finset.sum_sub_distrib]]
    rw [show
        (∑ i,
          radialIncrement profile
            ‖(x i).point - (y (sigma i)).point‖) =
            (∑ i,
              profile ‖(x i).point - (y (sigma i)).point‖) -
                ∑ _i : I, profile 0 by
      simp only [radialIncrement, Finset.sum_sub_distrib]]
    exact sub_le_sub_right
      (hCyclic (I := I)
        (fun i : I => (x i).point) (fun i : I => (y i).point)
        (fun i => by simpa only [Gamma', mem_setOf_eq] using hxy i)
        sigma) _
  obtain ⟨u, hu, hContact⟩ :=
    existsDistanceContactPotential_of_isDistanceCyclicallyMonotone
      (⟨0⟩ : ProfileMetric n) Gamma' hDistanceCyclic
  refine ⟨fun x => u ⟨x⟩, ?_, ?_⟩
  · intro x y
    have h := hu.dist_le_mul (⟨x⟩ : ProfileMetric n) ⟨y⟩
    change
      dist (u ⟨x⟩) (u ⟨y⟩) <=
        (1 : NNReal) * radialIncrement profile ‖x - y‖ at h
    simpa using h
  · intro z hz
    have h :=
      hContact
        (show
          ((⟨z.1⟩ : ProfileMetric n), ⟨z.2⟩) ∈ Gamma' by
            exact hz)
    change
      radialIncrement profile ‖z.1 - z.2‖ =
        u ⟨z.1⟩ - u ⟨z.2⟩ at h
    exact h

private theorem lipschitzOnWith_profile_Ici
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {d : Real} (hd : 0 < d) :
    LipschitzOnWith
      ⟨profileSupergradient profile (d / 2),
        (profileSupergradient_pos hMono hStrict (half_pos hd)).le⟩
      profile (Ici d) := by
  let K : NNReal :=
    ⟨profileSupergradient profile (d / 2),
      (profileSupergradient_pos hMono hStrict (half_pos hd)).le⟩
  apply LipschitzOnWith.of_le_add_mul K
  intro a ha b hb
  by_cases hab : a <= b
  · have hProfile : profile a <= profile b :=
      hMono (le_trans hd.le ha) (le_trans hd.le hb) hab
    exact hProfile.trans
      (le_add_of_nonneg_right (mul_nonneg K.property dist_nonneg))
  · have hba : b < a := lt_of_not_ge hab
    have hbPos : 0 < b := hd.trans_le hb
    have hHalfLtB : d / 2 < b :=
      (half_lt_self hd).trans_le hb
    have hSupergradientLe :
        profileSupergradient profile b <=
          profileSupergradient profile (d / 2) :=
      (profileSupergradient_strictAnti hStrict
        (half_pos hd) hHalfLtB).le
    have hTangent :=
      profile_le_tangent hStrict.concaveOn hbPos
        (hbPos.le.trans hba.le)
    change
      profile a <= profile b +
        profileSupergradient profile (d / 2) * dist a b
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hba)]
    calc
      profile a <=
          profile b +
            profileSupergradient profile b * (a - b) :=
        hTangent
      _ <=
          profile b +
            profileSupergradient profile (d / 2) * (a - b) := by
        gcongr

private def profileContactOuterTargets
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  {y | r <= dist a y}

private def profileContactInnerBall
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  Metric.ball a (r / 2)

private def profileContactEnvelope
    (profile : Real -> Real) (u : Euclidean n -> Real)
    (a : Euclidean n) (r : Real) (x : Euclidean n) : Real :=
  sInf
    (Set.range fun
      y : profileContactOuterTargets a r =>
        u y + radialIncrement profile (dist x y))

private theorem profilePotential_le_add
    {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖)
    (x y : Euclidean n) :
    u x <= u y + radialIncrement profile (dist x y) := by
  have hSub :
      u x - u y <= radialIncrement profile (dist x y) := by
    calc
      u x - u y <= |u x - u y| := le_abs_self _
      _ = dist (u x) (u y) := by rw [Real.dist_eq]
      _ <= radialIncrement profile ‖x - y‖ := hu x y
      _ = radialIncrement profile (dist x y) := by
        rw [dist_eq_norm]
  linarith

private theorem profileContactEnvelope_values_bddBelow
    {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖)
    (a : Euclidean n) (r : Real) (x : Euclidean n) :
    BddBelow
      (Set.range fun
        y : profileContactOuterTargets a r =>
          u y + radialIncrement profile (dist x y)) := by
  refine ⟨u x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact profilePotential_le_add hu x y

private theorem lipschitzOnWith_profileCost_of_outerTarget
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) {a y : Euclidean n}
    (hy : y ∈ profileContactOuterTargets a r) :
    LipschitzOnWith
      ⟨profileSupergradient profile ((r / 2) / 2),
        (profileSupergradient_pos hMono hStrict
          (half_pos (half_pos hr))).le⟩
      (fun x : Euclidean n =>
        radialIncrement profile (dist x y))
      (profileContactInnerBall a r) := by
  let C : NNReal :=
    ⟨profileSupergradient profile ((r / 2) / 2),
      (profileSupergradient_pos hMono hStrict
        (half_pos (half_pos hr))).le⟩
  have hProfile :
      LipschitzOnWith C profile (Ici (r / 2)) := by
    simpa only [C] using
      lipschitzOnWith_profile_Ici hMono hStrict (half_pos hr)
  have hDistanceLower
      {x : Euclidean n} (hx : x ∈ profileContactInnerBall a r) :
      r / 2 <= dist x y := by
    have hx' : dist x a < r / 2 := by
      simpa only [profileContactInnerBall, Metric.mem_ball] using hx
    have hy' : r <= dist a y := hy
    have hTriangle : dist a y <= dist a x + dist x y :=
      dist_triangle a x y
    rw [dist_comm a x] at hTriangle
    linarith
  apply LipschitzOnWith.of_le_add_mul C
  intro x hx x' hx'
  have hOneSided :=
    hProfile.le_add_mul
      (hDistanceLower hx) (hDistanceLower hx')
  have hDistance :
      dist (dist x y) (dist x' y) <= dist x x' :=
    dist_dist_dist_le_left x x' y
  have hScaledDistance :
      (C : Real) * dist (dist x y) (dist x' y) <=
        (C : Real) * dist x x' :=
    mul_le_mul_of_nonneg_left hDistance C.property
  dsimp only [radialIncrement]
  linarith

private theorem lipschitzOnWith_profileContactEnvelope
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖)
    {r : Real} (hr : 0 < r) (a : Euclidean n)
    (hOuter : (profileContactOuterTargets a r).Nonempty) :
    LipschitzOnWith
      ⟨profileSupergradient profile ((r / 2) / 2),
        (profileSupergradient_pos hMono hStrict
          (half_pos (half_pos hr))).le⟩
      (profileContactEnvelope profile u a r)
      (profileContactInnerBall a r) := by
  let C : NNReal :=
    ⟨profileSupergradient profile ((r / 2) / 2),
      (profileSupergradient_pos hMono hStrict
        (half_pos (half_pos hr))).le⟩
  let Outer := profileContactOuterTargets a r
  letI : Nonempty Outer := hOuter.to_subtype
  let f : Outer -> Euclidean n -> Real :=
    fun y x => u y + radialIncrement profile (dist x y)
  have hLipschitz (y : Outer) :
      LipschitzOnWith C (f y) (profileContactInnerBall a r) := by
    have hCost :=
      lipschitzOnWith_profileCost_of_outerTarget
        hMono hStrict hr y.property
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx x' hx'
    simpa only [f, Real.dist_eq, add_sub_add_left_eq_sub] using
      hCost.dist_le_mul x hx x' hx'
  have hBounded
      (x : Euclidean n) (_hx : x ∈ profileContactInnerBall a r) :
      BddBelow (Set.range fun y : Outer => f y x) := by
    simpa only [Outer, f] using
      profileContactEnvelope_values_bddBelow hu a r x
  simpa only [profileContactEnvelope, Outer, f] using
    lipschitzOnWith_sInf_range
      C f (profileContactInnerBall a r) hLipschitz hBounded

private theorem profileContactEnvelope_eq_of_contact
    {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖)
    {a x y : Euclidean n} {r : Real}
    (hy : y ∈ profileContactOuterTargets a r)
    (hContact :
      radialIncrement profile (dist x y) = u x - u y) :
    profileContactEnvelope profile u a r x = u x := by
  apply le_antisymm
  · apply csInf_le
      (profileContactEnvelope_values_bddBelow hu a r x)
    exact
      ⟨⟨y, hy⟩, by
        dsimp
        linarith⟩
  · apply le_csInf
    · exact
        ⟨u y + radialIncrement profile (dist x y),
          ⟨⟨y, hy⟩, rfl⟩⟩
    · rintro _ ⟨z, rfl⟩
      exact profilePotential_le_add hu x z

private theorem profileContactEnvelope_le_profile_add
    {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖)
    {a y : Euclidean n} {r : Real}
    (hy : y ∈ profileContactOuterTargets a r)
    (x : Euclidean n) :
    profileContactEnvelope profile u a r x <=
      profile (dist x y) + (u y - profile 0) := by
  have hInf :
      profileContactEnvelope profile u a r x <=
        u y + radialIncrement profile (dist x y) := by
    apply csInf_le
      (profileContactEnvelope_values_bddBelow hu a r x)
    exact ⟨⟨y, hy⟩, rfl⟩
  dsimp only [radialIncrement] at hInf
  linarith

private theorem profileContact_sourceAeUniqueFiber
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {mu : FiniteMeasure (Euclidean n)}
    (hMuAC : (mu : Measure (Euclidean n)) ≪ volume)
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          radialIncrement profile ‖x - y‖)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hOffDiagonal : ∀ z ∈ Gamma, z.1 ≠ z.2)
    (hContact :
      ∀ z ∈ Gamma,
        radialIncrement profile (dist z.1 z.2) =
          u z.1 - u z.2) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      ∀ y y', (x, y) ∈ Gamma ->
        (x, y') ∈ Gamma -> y = y' := by
  let center : Nat -> Euclidean n :=
    TopologicalSpace.denseSeq (Euclidean n)
  let radius : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hRadiusPos (k : Nat) : 0 < radius k := by
    dsimp only [radius]
    positivity
  have hDiffAE (m k : Nat) :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)),
        x ∈ profileContactInnerBall (center m) (radius k) ->
        (profileContactOuterTargets
          (center m) (radius k)).Nonempty ->
        DifferentiableAt Real
          (profileContactEnvelope
            profile u (center m) (radius k)) x := by
    by_cases hOuter :
        (profileContactOuterTargets
          (center m) (radius k)).Nonempty
    · have hLip :=
        lipschitzOnWith_profileContactEnvelope
          hMono hStrict hu (hRadiusPos k) (center m) hOuter
      filter_upwards
        [hLip.ae_differentiableWithinAt_of_mem_of_real]
        with x hx
      intro hxInner _hOuter
      apply (hx hxInner).differentiableAt
      exact Metric.isOpen_ball.mem_nhds hxInner
    · filter_upwards [] with x
      intro _hxInner hOuter'
      exact (hOuter hOuter').elim
  have hDiffAllVolume :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)),
        ∀ m k,
          x ∈ profileContactInnerBall (center m) (radius k) ->
          (profileContactOuterTargets
            (center m) (radius k)).Nonempty ->
          DifferentiableAt Real
            (profileContactEnvelope
              profile u (center m) (radius k)) x := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    exact hDiffAE m
  have hDiffAll :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ m k,
          x ∈ profileContactInnerBall (center m) (radius k) ->
          (profileContactOuterTargets
            (center m) (radius k)).Nonempty ->
          DifferentiableAt Real
            (profileContactEnvelope
              profile u (center m) (radius k)) x :=
    hMuAC.ae_le hDiffAllVolume
  filter_upwards [hDiffAll] with x hx
  intro y y' hxy hxy'
  have hxyNe : x ≠ y := hOffDiagonal (x, y) hxy
  have hxyNe' : x ≠ y' := hOffDiagonal (x, y') hxy'
  let d : Real := min (dist x y) (dist x y')
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (dist_pos.mpr hxyNe) (dist_pos.mpr hxyNe')
  obtain ⟨k, hk⟩ :=
    exists_nat_one_div_lt (show 0 < d / 4 by positivity)
  have hk' : radius k < d / 4 := by
    simpa only [radius, Nat.cast_add, Nat.cast_one] using hk
  obtain ⟨m, hm⟩ :=
    Metric.denseRange_iff.mp
      (TopologicalSpace.denseRange_denseSeq (Euclidean n))
      x (radius k / 4) (by positivity)
  have hm' : dist x (center m) < radius k / 4 := by
    simpa only [center, dist_comm] using hm
  have hxInner :
      x ∈ profileContactInnerBall (center m) (radius k) := by
    change dist x (center m) < radius k / 2
    linarith [hRadiusPos k]
  have hyOuter :
      y ∈ profileContactOuterTargets (center m) (radius k) := by
    change radius k <= dist (center m) y
    have hTriangle :
        dist x y <= dist x (center m) + dist (center m) y :=
      dist_triangle x (center m) y
    have hdLe : d <= dist x y := min_le_left _ _
    linarith
  have hyOuter' :
      y' ∈ profileContactOuterTargets (center m) (radius k) := by
    change radius k <= dist (center m) y'
    have hTriangle :
        dist x y' <= dist x (center m) + dist (center m) y' :=
      dist_triangle x (center m) y'
    have hdLe : d <= dist x y' := min_le_right _ _
    linarith
  have hOuter :
      (profileContactOuterTargets
        (center m) (radius k)).Nonempty :=
    ⟨y, hyOuter⟩
  have hDiff :
      DifferentiableAt Real
        (profileContactEnvelope
          profile u (center m) (radius k)) x :=
    hx m k hxInner hOuter
  have hTouch :
      profileContactEnvelope
          profile u (center m) (radius k) x =
        profile (dist x y) + (u y - profile 0) := by
    rw [profileContactEnvelope_eq_of_contact
      hu hyOuter (hContact (x, y) hxy)]
    have hc := hContact (x, y) hxy
    dsimp only [radialIncrement] at hc
    linarith
  have hTouch' :
      profileContactEnvelope
          profile u (center m) (radius k) x =
        profile (dist x y') + (u y' - profile 0) := by
    rw [profileContactEnvelope_eq_of_contact
      hu hyOuter' (hContact (x, y') hxy')]
    have hc := hContact (x, y') hxy'
    dsimp only [radialIncrement] at hc
    linarith
  exact
    strictConcaveRadialUpperTouches_target_unique_of_differentiableAt
      hMono hStrict hDiff hxyNe hxyNe'
      (profileContactEnvelope_le_profile_add hu hyOuter) hTouch
      (profileContactEnvelope_le_profile_add hu hyOuter') hTouch'

/-- Every integrable minimizer of an increasing strictly concave radial
profile is a graph plan when the source is absolutely continuous and the
marginals are mutually singular. The perturbation specialization below has
integrable profile cost for every coupling by the marginal first moments. -/
theorem existsGraphPlan_of_strictConcaveProfileMinimizer
    (n : Nat)
    {mu nu : FiniteMeasure (Euclidean n)}
    (hSingular : FiniteMutuallySingular mu nu)
    (hMuAC : (mu : Measure (Euclidean n)) ≪ volume)
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (gamma : FiniteCoupling mu nu)
    (hIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          profile ‖z.1 - z.2‖)
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)))
    (hMin : IsProfileMinimizer profile gamma) :
    ∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T := by
  obtain ⟨A, _hAMeasurable, hMuA, hNuA⟩ := hSingular
  let Gamma : Set (Euclidean n × Euclidean n) :=
    Measure.support
      (gamma.plan :
        Measure (Euclidean n × Euclidean n)) ∩
      (A ×ˢ Aᶜ)
  have hCostMeasurable :
      Measurable
        (fun z : Euclidean n × Euclidean n =>
          profile ‖z.1 - z.2‖) :=
    (concaveProfileDistanceLowerSemicontinuous
      hStrict.concaveOn).measurable
  have hCyclic :
      IsProfileCyclicallyMonotone profile Gamma :=
    profileMinimizer_supportCarrier_cyclic
      n hStrict.concaveOn hCostMeasurable gamma
      hIntegrable hMin A
  obtain ⟨u, hu, hContactNorm⟩ :=
    exists_profileContactPotential
      hMono hStrict.concaveOn Gamma hCyclic
  have hMuCarrier :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)), x ∈ A := by
    apply ae_iff.mpr
    change (mu : Measure (Euclidean n)) Aᶜ = 0
    exact hMuA
  have hNuCarrier :
      ∀ᵐ y ∂(nu : Measure (Euclidean n)), y ∈ Aᶜ := by
    apply ae_iff.mpr
    have hSet :
        {y : Euclidean n | y ∉ Aᶜ} = A := by
      ext y
      simp only [mem_setOf_eq, mem_compl_iff, not_not]
    rw [hSet]
    exact hNuA
  obtain ⟨hSourceCarrier, hTargetCarrier⟩ :=
    finiteCouplingMarginalAeTransfer
      gamma hMuCarrier hNuCarrier
  have hSupported : IsSupported gamma Gamma := by
    filter_upwards
      [(Measure.support_mem_ae :
        ∀ᵐ z ∂(gamma.plan :
          Measure (Euclidean n × Euclidean n)),
          z ∈ Measure.support
            (gamma.plan :
              Measure (Euclidean n × Euclidean n))),
        hSourceCarrier, hTargetCarrier]
      with z hzSupport hzSource hzTarget
    exact ⟨hzSupport, hzSource, hzTarget⟩
  have hOffDiagonal :
      ∀ z ∈ Gamma, z.1 ≠ z.2 := by
    intro z hz hEq
    exact hz.2.2 (hEq ▸ hz.2.1)
  have hContact :
      ∀ z ∈ Gamma,
        radialIncrement profile (dist z.1 z.2) =
          u z.1 - u z.2 := by
    intro z hz
    simpa only [dist_eq_norm] using hContactNorm z hz
  have hUnique :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ y y', (x, y) ∈ Gamma ->
          (x, y') ∈ Gamma -> y = y' :=
    profileContact_sourceAeUniqueFiber
      hMono hStrict hMuAC hu Gamma hOffDiagonal hContact
  exact
    existsGraphPlanOfSupportedSourceAeUniqueFiber_polish
      gamma Gamma hSupported hUnique

/-- Every minimizer of every admissible perturbation profile is induced by
a measurable transport map. -/
theorem perturbationMinimizerGraphPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    PerturbationMinimizerGraphPremise n mu nu := by
  intro family firstOrder hFamily epsilon hEpsilon gamma hMin
  have hStrict :
      StrictConcaveOn Real (Ici 0) (family epsilon) :=
    hFamily.strictlyConcave hEpsilon
  have hProfile :
      AdmissibleConcaveProfile (family epsilon) := by
    refine ⟨hStrict.concaveOn, 0, le_rfl, ?_⟩
    intro d hd
    have hNonnegative := hFamily.nonnegative hEpsilon hd
    linarith
  have hIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          family epsilon ‖z.1 - z.2‖)
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)) :=
    admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
      hProfile hMarginals.sourceFirstMoment
        hMarginals.targetFirstMoment gamma
  exact
    existsGraphPlan_of_strictConcaveProfileMinimizer
      n hMarginals.mutuallySingular
      hMarginals.sourceAbsolutelyContinuous
      (hFamily.increasing hEpsilon) hStrict
      gamma hIntegrable hMin

end ConcaveOTLimit
