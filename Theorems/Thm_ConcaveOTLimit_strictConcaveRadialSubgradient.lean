import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual

open Filter Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ConcaveOTLimit

/-- The right derivative of a concave profile, expressed through the
corresponding convex function. -/
def concaveProfileRightSupergradient
    (profile : Real -> Real) (r : Real) : Real :=
  -derivWithin (fun t => -profile t) (Ioi r) r

theorem hasDerivWithinAt_concaveProfileRightSupergradient
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    HasDerivWithinAt profile
      (concaveProfileRightSupergradient profile r) (Ioi r) r := by
  have hrInterior : r ∈ interior (Ici (0 : Real)) := by
    simpa only [interior_Ici] using hr
  have hRight :=
    hConcave.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hrInterior
  simpa only [concaveProfileRightSupergradient, neg_neg] using hRight.neg

theorem concaveProfile_le_rightSupergradient_tangent
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {r t : Real} (hr : 0 < r) (ht : 0 <= t) :
    profile t <= profile r +
      concaveProfileRightSupergradient profile r * (t - r) := by
  let p := concaveProfileRightSupergradient profile r
  have hpDeriv : HasDerivWithinAt profile p (Ioi r) r :=
    hasDerivWithinAt_concaveProfileRightSupergradient hConcave hr
  rcases lt_trichotomy t r with htr | rfl | hrt
  · have hrInterior : r ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici] using hr
    have hNegRight :
        HasDerivWithinAt (fun s => -profile s) (-p) (Ioi r) r := by
      simpa only [p, concaveProfileRightSupergradient, neg_neg] using
        hpDeriv.neg
    have hNegLeftDiff :
        DifferentiableWithinAt Real (fun s => -profile s) (Iio r) r :=
      hConcave.neg.differentiableWithinAt_Iio_of_mem_interior hrInterior
    have hLeftLeRight :
        derivWithin (fun s => -profile s) (Iio r) r <= -p := by
      exact
        (hConcave.neg.leftDeriv_le_rightDeriv_of_mem_interior
          hrInterior).trans_eq
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
  · have hSlopeLe : slope profile r t <= p :=
      hConcave.slope_le_of_hasDerivWithinAt_Ioi
        hr.le ht hrt hpDeriv
    rw [slope_def_field] at hSlopeLe
    have hScaled := (div_le_iff₀ (sub_pos.mpr hrt)).mp hSlopeLe
    linarith

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

theorem concaveProfileRightSupergradient_pos
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) :
    0 < concaveProfileRightSupergradient profile r := by
  let s := r + 1
  have hrs : r < s := by
    dsimp only [s]
    linarith
  have hs0 : 0 <= s := hr.le.trans hrs.le
  have hProfileLt : profile r < profile s :=
    strictMonoOn_of_monotoneOn_of_strictConcaveOn_Ici hMono hStrict
      hr.le hs0 hrs
  have hSlopePos : 0 < slope profile r s := by
    rw [slope_def_field]
    positivity
  have hSlopeLt :
      slope profile r s <
        concaveProfileRightSupergradient profile r :=
    hStrict.slope_lt_of_hasDerivWithinAt_Ioi
      hr.le hs0 hrs
      (hasDerivWithinAt_concaveProfileRightSupergradient
        hStrict.concaveOn hr)
  exact hSlopePos.trans hSlopeLt

theorem concaveProfileRightSupergradient_strictAnti
    {profile : Real -> Real}
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r s : Real} (hr : 0 < r) (hrs : r < s) :
    concaveProfileRightSupergradient profile s <
      concaveProfileRightSupergradient profile r := by
  have hs : 0 < s := hr.trans hrs
  have hAtR :=
    hasDerivWithinAt_concaveProfileRightSupergradient
      hStrict.concaveOn hr
  have hAtS :=
    hasDerivWithinAt_concaveProfileRightSupergradient
      hStrict.concaveOn hs
  have hSlopeLt :
      slope profile r s <
        concaveProfileRightSupergradient profile r :=
    hStrict.slope_lt_of_hasDerivWithinAt_Ioi
      hr.le hs.le hrs hAtR
  have hSuperLeSlope :
      concaveProfileRightSupergradient profile s <=
        slope profile r s := by
    have hsInterior : s ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici] using hs
    have hNegRight :
        HasDerivWithinAt (fun t => -profile t)
          (-concaveProfileRightSupergradient profile s) (Ioi s) s := by
      simpa only [neg_neg] using hAtS.neg
    have hNegLeftDiff :
        DifferentiableWithinAt Real (fun t => -profile t) (Iio s) s :=
      hStrict.concaveOn.neg.differentiableWithinAt_Iio_of_mem_interior
        hsInterior
    have hLeftLeRight :
        derivWithin (fun t => -profile t) (Iio s) s <=
          -concaveProfileRightSupergradient profile s := by
      exact
        (hStrict.concaveOn.neg.leftDeriv_le_rightDeriv_of_mem_interior
          hsInterior).trans_eq
          (hNegRight.derivWithin (uniqueDiffWithinAt_Ioi s))
    have hNegSlope :
        slope (fun t => -profile t) r s <=
          -concaveProfileRightSupergradient profile s :=
      (hStrict.concaveOn.neg.slope_le_leftDeriv
        hr.le hs.le hrs hNegLeftDiff).trans hLeftLeRight
    simpa only [slope_neg, neg_le_neg_iff] using hNegSlope
  exact hSuperLeSlope.trans_lt hSlopeLt

private theorem fderiv_eq_positiveDistanceUpperTouch
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {v : E -> Real} {q c : Real} {x y : E}
    (hDifferentiable : DifferentiableAt Real v x)
    (hxy : x ≠ y)
    (hUpper : ∀ z, v z <= q * dist z y + c)
    (hTouch : v x = q * dist x y + c) :
    fderiv Real v x =
      q • fderiv Real (fun z : E => dist z y) x := by
  let gap : E -> Real := fun z => q * dist z y + c - v z
  have hGapMin : IsLocalMin gap x := by
    change ∀ᶠ z in 𝓝 x, gap x <= gap z
    filter_upwards [] with z
    dsimp only [gap]
    rw [hTouch]
    linarith [hUpper z]
  have hDistDifferentiable :
      DifferentiableAt Real (fun z : E => dist z y) x := by
    simpa only [dist_eq_norm] using
      ((differentiableAt_id.sub_const y).norm Real
        (sub_ne_zero.mpr hxy))
  have hGapDerivative :
      HasFDerivAt gap
        (q • fderiv Real (fun z : E => dist z y) x -
          fderiv Real v x) x := by
    dsimp only [gap]
    exact
      ((hDistDifferentiable.hasFDerivAt.const_mul q).add_const c).sub
        hDifferentiable.hasFDerivAt
  have hDerivativeZero :=
    hGapMin.hasFDerivAt_eq_zero hGapDerivative
  exact (sub_eq_zero.mp hDerivativeZero).symm

private theorem hasFDerivAt_norm_of_ne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {w : E} (hw : w ≠ 0) :
    HasFDerivAt (fun z : E => ‖z‖)
      (‖w‖⁻¹ • innerSL Real w) w := by
  have hSqNe : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have h :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt.sqrt hSqNe
  convert h using 1
  · funext z
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
  · rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg w)]
    ext z
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      innerSL_apply_apply]
    field_simp
    simp only [two_smul]
    ring

private theorem hasFDerivAt_dist_left_of_ne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y : E} (hxy : x ≠ y) :
    HasFDerivAt (fun z : E => dist z y)
      (‖x - y‖⁻¹ • innerSL Real (x - y)) x := by
  simpa only [dist_eq_norm, ContinuousLinearMap.comp_id] using
    (hasFDerivAt_norm_of_ne (sub_ne_zero.mpr hxy)).comp x
      ((hasFDerivAt_id x).sub_const y)

private theorem fderiv_dist_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y : E} (hxy : x ≠ y) :
    ‖fderiv Real (fun z : E => dist z y) x‖ = 1 := by
  rw [(hasFDerivAt_dist_left_of_ne hxy).fderiv, norm_smul,
    innerSL_apply_norm,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]

private theorem fderiv_dist_injective_target
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y y' : E} (hxy : x ≠ y) (hxy' : x ≠ y')
    (hDist : dist x y = dist x y')
    (hDeriv :
      fderiv Real (fun z : E => dist z y) x =
        fderiv Real (fun z : E => dist z y') x) :
    y = y' := by
  rw [(hasFDerivAt_dist_left_of_ne hxy).fderiv,
    (hasFDerivAt_dist_left_of_ne hxy').fderiv] at hDeriv
  have hDirection :
      ‖x - y‖⁻¹ • (x - y) = ‖x - y'‖⁻¹ • (x - y') := by
    apply (innerSL_inj (𝕜 := Real)).mp
    simpa only [map_smul] using hDeriv
  have hNormEq : ‖x - y‖ = ‖x - y'‖ := by
    simpa only [dist_eq_norm] using hDist
  rw [hNormEq] at hDirection
  have hCoefficientNe : ‖x - y'‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy'))
  have hDifference : x - y = x - y' := by
    rw [← sub_eq_zero]
    apply (smul_eq_zero_iff_right hCoefficientNe).mp
    rw [smul_sub, hDirection, sub_self]
  exact sub_right_injective hDifference

/-- A differentiable function cannot be touched from above at one point by
two translates of an increasing strictly concave radial profile with
different noncentral centers. No differentiability of the profile is
assumed. -/
theorem strictConcaveRadialUpperTouches_target_unique
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
  let r := dist x y
  let r' := dist x y'
  let q := concaveProfileRightSupergradient profile r
  let q' := concaveProfileRightSupergradient profile r'
  have hr : 0 < r := dist_pos.mpr hxy
  have hr' : 0 < r' := dist_pos.mpr hxy'
  have hq : 0 < q :=
    concaveProfileRightSupergradient_pos hMono hStrict hr
  have hq' : 0 < q' :=
    concaveProfileRightSupergradient_pos hMono hStrict hr'
  have hLinearUpper :
      ∀ z, v z <= q * dist z y + (profile r + c - q * r) := by
    intro z
    have hTangent :=
      concaveProfile_le_rightSupergradient_tangent
        hStrict.concaveOn hr (dist_nonneg : 0 <= dist z y)
    change profile (dist z y) <=
      profile r + q * (dist z y - r) at hTangent
    linarith [hUpper z]
  have hLinearTouch :
      v x = q * dist x y + (profile r + c - q * r) := by
    rw [hTouch]
    change profile r + c = q * r + (profile r + c - q * r)
    ring
  have hLinearUpper' :
      ∀ z, v z <= q' * dist z y' +
        (profile r' + c' - q' * r') := by
    intro z
    have hTangent :=
      concaveProfile_le_rightSupergradient_tangent
        hStrict.concaveOn hr' (dist_nonneg : 0 <= dist z y')
    change profile (dist z y') <=
      profile r' + q' * (dist z y' - r') at hTangent
    linarith [hUpper' z]
  have hLinearTouch' :
      v x = q' * dist x y' + (profile r' + c' - q' * r') := by
    rw [hTouch']
    change profile r' + c' = q' * r' + (profile r' + c' - q' * r')
    ring
  have hGradient :=
    fderiv_eq_positiveDistanceUpperTouch hDifferentiable hxy
      hLinearUpper hLinearTouch
  have hGradient' :=
    fderiv_eq_positiveDistanceUpperTouch hDifferentiable hxy'
      hLinearUpper' hLinearTouch'
  have hScaledDeriv :
      q • fderiv Real (fun z : E => dist z y) x =
        q' • fderiv Real (fun z : E => dist z y') x :=
    hGradient.symm.trans hGradient'
  have hqEq : q = q' := by
    have hNormEq := congrArg norm hScaledDeriv
    rw [norm_smul, norm_smul, fderiv_dist_norm hxy,
      fderiv_dist_norm hxy'] at hNormEq
    simpa only [Real.norm_of_nonneg hq.le,
      Real.norm_of_nonneg hq'.le, mul_one] using hNormEq
  have hrEq : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · have :=
        concaveProfileRightSupergradient_strictAnti hStrict hr hlt
      exact False.elim (this.ne (by simpa [q, q'] using hqEq.symm))
    · exact heq
    · have :=
        concaveProfileRightSupergradient_strictAnti hStrict hr' hgt
      exact False.elim (this.ne (by simpa [q, q'] using hqEq))
  have hDeriv :
      fderiv Real (fun z : E => dist z y) x =
        fderiv Real (fun z : E => dist z y') x := by
    rw [hqEq] at hScaledDeriv
    rw [← sub_eq_zero]
    apply (smul_eq_zero_iff_right hq'.ne').mp
    rw [smul_sub, hScaledDeriv, sub_self]
  exact fderiv_dist_injective_target hxy hxy' hrEq hDeriv

end ConcaveOTLimit
