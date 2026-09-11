import Theorems.Thm_ConcaveOTLimit_radialRpowGradientInjective
import Mathlib.Analysis.Convex.Deriv

open Filter Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ConcaveOTLimit

private theorem strictMonoOn_of_monotoneOn_of_strictConcaveOn_Ici'
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
  have hMidLe : profile m <= profile b := hMono hm0 hb hmb
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

private def radialTouchProfileSupergradient
    (profile : Real -> Real) (r : Real) : Real :=
  -derivWithin (fun t => -profile t) (Ioi r) r

private theorem hasDerivWithinAt_radialTouchProfileSupergradient
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    HasDerivWithinAt profile
      (radialTouchProfileSupergradient profile r) (Ioi r) r := by
  have hrInterior : r ∈ interior (Ici (0 : Real)) := by
    simpa only [interior_Ici] using hr
  have hNeg :=
    hConcave.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hrInterior
  simpa only [radialTouchProfileSupergradient, neg_neg] using hNeg.neg

private theorem profile_le_radialTouch_tangent
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {r t : Real} (hr : 0 < r) (ht : 0 <= t) :
    profile t <=
      profile r +
        radialTouchProfileSupergradient profile r * (t - r) := by
  let p := radialTouchProfileSupergradient profile r
  have hpDeriv :
      HasDerivWithinAt profile p (Ioi r) r :=
    hasDerivWithinAt_radialTouchProfileSupergradient hConcave hr
  rcases lt_trichotomy t r with htr | rfl | hrt
  · have hrInterior : r ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici] using hr
    have hNegRight :
        HasDerivWithinAt (fun s => -profile s) (-p) (Ioi r) r := by
      simpa only [p, radialTouchProfileSupergradient, neg_neg] using
        hpDeriv.neg
    have hNegLeftDiff :
        DifferentiableWithinAt Real (fun s => -profile s) (Iio r) r :=
      hConcave.neg.differentiableWithinAt_Iio_of_mem_interior hrInterior
    have hLeftLeRight :
        derivWithin (fun s => -profile s) (Iio r) r <= -p := by
      have h :=
        hConcave.neg.leftDeriv_le_rightDeriv_of_mem_interior hrInterior
      exact h.trans_eq
        (hNegRight.derivWithin (uniqueDiffWithinAt_Ioi r))
    have hSlopeLe :
        slope (fun s => -profile s) t r <= -p :=
      (hConcave.neg.slope_le_leftDeriv ht hr.le htr
        hNegLeftDiff).trans hLeftLeRight
    rw [slope_def_field] at hSlopeLe
    have hden : 0 < r - t := sub_pos.mpr htr
    have hScaled :=
      (div_le_iff₀ hden).mp (by
        simpa only [Pi.neg_apply, neg_sub_neg] using hSlopeLe)
    linarith
  · simp
  · have hSlopeLe :
        slope profile r t <= p :=
      hConcave.slope_le_of_hasDerivWithinAt_Ioi
        hr.le ht hrt hpDeriv
    rw [slope_def_field] at hSlopeLe
    have hScaled := (div_le_iff₀ (sub_pos.mpr hrt)).mp hSlopeLe
    linarith

private theorem radialTouchProfileSupergradient_pos
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    0 < radialTouchProfileSupergradient profile r := by
  let s := r + 1
  have hrs : r < s := by
    dsimp only [s]
    linarith
  have hs0 : 0 <= s := hr.le.trans hrs.le
  have hProfileLt : profile r < profile s :=
    strictMonoOn_of_monotoneOn_of_strictConcaveOn_Ici'
      hMono hStrict hr.le hs0 hrs
  have hSlopePos : 0 < slope profile r s := by
    rw [slope_def_field]
    positivity
  have hSlopeLt :
      slope profile r s <
        radialTouchProfileSupergradient profile r :=
    hStrict.slope_lt_of_hasDerivWithinAt_Ioi
      hr.le hs0 hrs
      (hasDerivWithinAt_radialTouchProfileSupergradient
        hStrict.concaveOn hr)
  exact hSlopePos.trans hSlopeLt

private theorem radialTouchProfileSupergradient_strictAnti
    {profile : Real -> Real}
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r s : Real} (hr : 0 < r) (hrs : r < s) :
    radialTouchProfileSupergradient profile s <
      radialTouchProfileSupergradient profile r := by
  have hs : 0 < s := hr.trans hrs
  have hAtR :=
    hasDerivWithinAt_radialTouchProfileSupergradient
      hStrict.concaveOn hr
  have hAtS :=
    hasDerivWithinAt_radialTouchProfileSupergradient
      hStrict.concaveOn hs
  have hSlopeLt :
      slope profile r s <
        radialTouchProfileSupergradient profile r :=
    hStrict.slope_lt_of_hasDerivWithinAt_Ioi
      hr.le hs.le hrs hAtR
  have hSuperLeSlope :
      radialTouchProfileSupergradient profile s <=
        slope profile r s := by
    have hsInterior : s ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici] using hs
    have hNegRight :
        HasDerivWithinAt (fun t => -profile t)
          (-radialTouchProfileSupergradient profile s) (Ioi s) s := by
      simpa only [neg_neg] using hAtS.neg
    have hNegLeftDiff :
        DifferentiableWithinAt Real (fun t => -profile t) (Iio s) s :=
      hStrict.concaveOn.neg.differentiableWithinAt_Iio_of_mem_interior
        hsInterior
    have hLeftLeRight :
        derivWithin (fun t => -profile t) (Iio s) s <=
          -radialTouchProfileSupergradient profile s := by
      have h :=
        hStrict.concaveOn.neg.leftDeriv_le_rightDeriv_of_mem_interior
          hsInterior
      exact h.trans_eq
        (hNegRight.derivWithin (uniqueDiffWithinAt_Ioi s))
    have hNegSlope :
        slope (fun t => -profile t) r s <=
          -radialTouchProfileSupergradient profile s :=
      (hStrict.concaveOn.neg.slope_le_leftDeriv
        hr.le hs.le hrs hNegLeftDiff).trans hLeftLeRight
    simpa only [slope_neg, neg_le_neg_iff] using hNegSlope
  exact hSuperLeSlope.trans_lt hSlopeLt

private theorem fderiv_eq_radialTouch_tangent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {profile : Real -> Real} {v : E -> Real} {c : Real} {x y : E}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    (hDifferentiable : DifferentiableAt Real v x)
    (hxy : x ≠ y)
    (hUpper :
      ∀ᶠ z in 𝓝 x, v z <= profile (dist z y) + c)
    (hTouch : v x = profile (dist x y) + c) :
    fderiv Real v x =
      (radialTouchProfileSupergradient profile (dist x y) *
          dist x y ^ (-1 : Real)) • innerSL Real (x - y) := by
  let r := dist x y
  let p := radialTouchProfileSupergradient profile r
  let tangent : E -> Real :=
    fun z => profile r + p * (dist z y - r) + c
  let gap : E -> Real := fun z => tangent z - v z
  have hr : 0 < r := dist_pos.mpr hxy
  have hGapMin : IsLocalMin gap x := by
    change ∀ᶠ z in 𝓝 x, gap x <= gap z
    filter_upwards [hUpper] with z hz
    have hTangentBound :
        profile (dist z y) <=
          profile r + p * (dist z y - r) :=
      profile_le_radialTouch_tangent hConcave hr (dist_nonneg)
    dsimp only [gap, tangent]
    rw [hTouch]
    simp only [r, sub_self, mul_zero, add_zero]
    linarith
  have hTangentDerivative :
      HasFDerivAt tangent
        ((p * dist x y ^ (-1 : Real)) • innerSL Real (x - y)) x := by
    have hDistDerivative :
        HasFDerivAt (fun z : E => dist z y)
          ((dist x y ^ (-1 : Real)) • innerSL Real (x - y)) x := by
      convert hasFDerivAt_dist_rpow_left_of_ne (1 : Real) hxy using 1
      · ext z
        rw [Real.rpow_one]
      · norm_num
    dsimp only [tangent]
    simpa only [smul_smul] using
      ((hDistDerivative.sub_const r)
        |>.const_mul p |>.const_add (profile r) |>.add_const c)
  have hGapDerivative :
      HasFDerivAt gap
        ((p * dist x y ^ (-1 : Real)) • innerSL Real (x - y) -
          fderiv Real v x) x := by
    exact hTangentDerivative.sub hDifferentiable.hasFDerivAt
  have hDerivativeZero :=
    hGapMin.hasFDerivAt_eq_zero hGapDerivative
  simpa only [p, r] using (sub_eq_zero.mp hDerivativeZero).symm

/-- A differentiable function cannot be touched from above near one point
by two translates of the same increasing strictly concave radial profile
with distinct non-diagonal centers. The profile itself need not be
differentiable. -/
theorem strictConcaveRadialUpperTouches_target_unique_of_eventually
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {profile : Real -> Real} {v : E -> Real}
    {c c' : Real} {x y y' : E}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (hDifferentiable : DifferentiableAt Real v x)
    (hxy : x ≠ y) (hxy' : x ≠ y')
    (hUpper :
      ∀ᶠ z in 𝓝 x, v z <= profile (dist z y) + c)
    (hTouch : v x = profile (dist x y) + c)
    (hUpper' :
      ∀ᶠ z in 𝓝 x, v z <= profile (dist z y') + c')
    (hTouch' : v x = profile (dist x y') + c') :
    y = y' := by
  let r := dist x y
  let r' := dist x y'
  let p := radialTouchProfileSupergradient profile r
  let p' := radialTouchProfileSupergradient profile r'
  have hr : 0 < r := dist_pos.mpr hxy
  have hr' : 0 < r' := dist_pos.mpr hxy'
  have hp : 0 < p :=
    radialTouchProfileSupergradient_pos hMono hStrict hr
  have hp' : 0 < p' :=
    radialTouchProfileSupergradient_pos hMono hStrict hr'
  have hGradient :=
    fderiv_eq_radialTouch_tangent
      hStrict.concaveOn hDifferentiable hxy hUpper hTouch
  have hGradient' :=
    fderiv_eq_radialTouch_tangent
      hStrict.concaveOn hDifferentiable hxy' hUpper' hTouch'
  have hLinearGradient :
      (p * r ^ (-1 : Real)) • innerSL Real (x - y) =
        (p' * r' ^ (-1 : Real)) • innerSL Real (x - y') := by
    simpa only [p, p', r, r'] using hGradient.symm.trans hGradient'
  have hVectorGradient :
      (p * r ^ (-1 : Real)) • (x - y) =
        (p' * r' ^ (-1 : Real)) • (x - y') := by
    apply (innerSL_inj (𝕜 := Real)).mp
    simpa only [map_smul] using hLinearGradient
  have hNormGradient := congrArg norm hVectorGradient
  have hSlopeEq : p = p' := by
    have hCoefficientNonneg : 0 <= p * r ^ (-1 : Real) :=
      mul_nonneg hp.le (Real.rpow_nonneg hr.le _)
    have hCoefficientNonneg' : 0 <= p' * r' ^ (-1 : Real) :=
      mul_nonneg hp'.le (Real.rpow_nonneg hr'.le _)
    have hCancel : (p * r ^ (-1 : Real)) * r = p := by
      rw [Real.rpow_neg_one]
      field_simp
    have hCancel' : (p' * r' ^ (-1 : Real)) * r' = p' := by
      rw [Real.rpow_neg_one]
      field_simp
    rw [norm_smul, norm_smul,
      Real.norm_of_nonneg hCoefficientNonneg,
      Real.norm_of_nonneg hCoefficientNonneg',
      show ‖x - y‖ = r by simp only [r, dist_eq_norm],
      show ‖x - y'‖ = r' by simp only [r', dist_eq_norm],
      hCancel, hCancel'] at hNormGradient
    exact hNormGradient
  have hRadiusEq : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · have :=
        radialTouchProfileSupergradient_strictAnti hStrict hr hlt
      change p' < p at this
      exact False.elim ((ne_of_lt this) hSlopeEq.symm)
    · exact heq
    · have :=
        radialTouchProfileSupergradient_strictAnti hStrict hr' hgt
      change p < p' at this
      exact False.elim ((ne_of_lt this) hSlopeEq)
  have hCoefficientEq :
      p * r ^ (-1 : Real) = p' * r' ^ (-1 : Real) := by
    rw [hSlopeEq, hRadiusEq]
  rw [hCoefficientEq] at hVectorGradient
  have hCoefficientNe : p' * r' ^ (-1 : Real) ≠ 0 := by
    positivity
  have hDifference : x - y = x - y' := by
    rw [← sub_eq_zero]
    apply (smul_eq_zero_iff_right hCoefficientNe).mp
    rw [smul_sub, hVectorGradient, sub_self]
  exact sub_right_injective hDifference

/-- Global-upper-bound wrapper for
`strictConcaveRadialUpperTouches_target_unique_of_eventually`. -/
theorem strictConcaveRadialUpperTouches_target_unique_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {profile : Real -> Real} {v : E -> Real}
    {c c' : Real} {x y y' : E}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (hDifferentiable : DifferentiableAt Real v x)
    (hxy : x ≠ y) (hxy' : x ≠ y')
    (hUpper : ∀ z, v z <= profile (dist z y) + c)
    (hTouch : v x = profile (dist x y) + c)
    (hUpper' : ∀ z, v z <= profile (dist z y') + c')
    (hTouch' : v x = profile (dist x y') + c') :
    y = y' := by
  apply
    strictConcaveRadialUpperTouches_target_unique_of_eventually
      hMono hStrict hDifferentiable hxy hxy'
      (Filter.Eventually.of_forall hUpper) hTouch
      (Filter.Eventually.of_forall hUpper') hTouch'

end ConcaveOTLimit
