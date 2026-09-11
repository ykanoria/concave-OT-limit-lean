import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

open Filter Set Topology
open scoped RealInnerProductSpace

namespace ConcaveOTLimit

/-- A positive sublinear real power is Lipschitz when its arguments are
bounded away from zero. -/
theorem abs_rpow_sub_rpow_le_of_lower_bound
    {p delta a b : Real}
    (hp0 : 0 < p) (hp1 : p < 1) (hDelta : 0 < delta)
    (ha : delta ≤ a) (hb : delta ≤ b) :
    |a ^ p - b ^ p| ≤
      p * delta ^ (p - 1) * |a - b| := by
  have hDerivative :
      ∀ t ∈ Ici delta,
        HasDerivWithinAt
          (fun r : Real => r ^ p)
          (p * t ^ (p - 1)) (Ici delta) t := by
    intro t ht
    exact
      (Real.hasDerivAt_rpow_const
        (Or.inl (ne_of_gt (hDelta.trans_le ht)))).hasDerivWithinAt
  have hDerivativeBound :
      ∀ t ∈ Ici delta,
        ‖p * t ^ (p - 1)‖ ≤ p * delta ^ (p - 1) := by
    intro t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg hp0.le
          (Real.rpow_nonneg (le_trans hDelta.le ht) (p - 1)))]
    exact
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hDelta ht
          (sub_nonpos.mpr hp1.le))
        hp0.le
  have hMeanValue :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hDerivative hDerivativeBound (convex_Ici delta) ha hb
  simpa only [Real.norm_eq_abs, abs_sub_comm] using hMeanValue

/-- Two source points admitting power contacts of length at least `delta`
obey a uniform Lipschitz estimate whenever they are closer than
`delta / 2`. -/
theorem powerContactPotential_dist_le_of_close
    {E : Type*} [PseudoMetricSpace E]
    {u : E → Real} {p delta : Real}
    (hp0 : 0 < p) (hp1 : p < 1) (hDelta : 0 < delta)
    (hPotential :
      ∀ a b, dist (u a) (u b) ≤ dist a b ^ p)
    {x x' y y' : E}
    (hxyLength : delta ≤ dist x y)
    (hx'y'Length : delta ≤ dist x' y')
    (hClose : dist x x' < delta / 2)
    (hContact : dist x y ^ p = u x - u y)
    (hContact' : dist x' y' ^ p = u x' - u y') :
    dist (u x) (u x') ≤
      p * (delta / 2) ^ (p - 1) * dist x x' := by
  have hHalf : 0 < delta / 2 := by positivity
  have hPotentialSub (a b : E) :
      u a - u b ≤ dist a b ^ p := by
    calc
      u a - u b ≤ dist (u a) (u b) := by
        simpa only [Real.dist_eq] using le_abs_self (u a - u b)
      _ ≤ dist a b ^ p := hPotential a b
  have hx'yLower : delta / 2 ≤ dist x' y := by
    have hTriangle := dist_triangle x x' y
    linarith
  have hxyLower : delta / 2 ≤ dist x y := by
    linarith
  have hxy'Lower : delta / 2 ≤ dist x y' := by
    have hTriangle := dist_triangle x' x y'
    rw [dist_comm x' x] at hTriangle
    linarith
  have hx'y'Lower : delta / 2 ≤ dist x' y' := by
    linarith
  let C : Real := p * (delta / 2) ^ (p - 1)
  have hC : 0 ≤ C := by
    exact
      mul_nonneg hp0.le
        (Real.rpow_nonneg hHalf.le (p - 1))
  have hForwardRaw :
      u x' - u x ≤ dist x' y ^ p - dist x y ^ p := by
    rw [hContact]
    linarith [hPotentialSub x' y]
  have hForwardPower :
      |dist x' y ^ p - dist x y ^ p| ≤
        C * |dist x' y - dist x y| := by
    exact
      abs_rpow_sub_rpow_le_of_lower_bound
        hp0 hp1 hHalf hx'yLower hxyLower
  have hForward :
      u x' - u x ≤ C * dist x x' := by
    calc
      u x' - u x ≤ dist x' y ^ p - dist x y ^ p :=
        hForwardRaw
      _ ≤ |dist x' y ^ p - dist x y ^ p| :=
        le_abs_self _
      _ ≤ C * |dist x' y - dist x y| :=
        hForwardPower
      _ ≤ C * dist x' x :=
        mul_le_mul_of_nonneg_left (abs_dist_sub_le x' x y) hC
      _ = C * dist x x' := by rw [dist_comm x' x]
  have hReverseRaw :
      u x - u x' ≤ dist x y' ^ p - dist x' y' ^ p := by
    rw [hContact']
    linarith [hPotentialSub x y']
  have hReversePower :
      |dist x y' ^ p - dist x' y' ^ p| ≤
        C * |dist x y' - dist x' y'| := by
    exact
      abs_rpow_sub_rpow_le_of_lower_bound
        hp0 hp1 hHalf hxy'Lower hx'y'Lower
  have hReverse :
      u x - u x' ≤ C * dist x x' := by
    calc
      u x - u x' ≤ dist x y' ^ p - dist x' y' ^ p :=
        hReverseRaw
      _ ≤ |dist x y' ^ p - dist x' y' ^ p| :=
        le_abs_self _
      _ ≤ C * |dist x y' - dist x' y'| :=
        hReversePower
      _ ≤ C * dist x x' :=
        mul_le_mul_of_nonneg_left (abs_dist_sub_le x x' y') hC
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith, hReverse⟩

/-- The usual derivative formula for a real power of the norm holds at every
nonzero point, with no restriction on the exponent. -/
theorem hasFDerivAt_norm_rpow_of_ne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (x : E) (p : Real) (hx : x ≠ 0) :
    HasFDerivAt
      (fun z : E => ‖z‖ ^ p)
      ((p * ‖x‖ ^ (p - 2)) • innerSL Real x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert!
    (hasStrictFDerivAt_norm_sq x).rpow_const
      (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _),
    ← Nat.cast_smul_eq_nsmul Real, smul_smul]
  ring_nf

/-- Away from its center, a radial power has the expected derivative in its
source variable. -/
theorem hasFDerivAt_dist_rpow_left_of_ne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y : E} (p : Real) (hxy : x ≠ y) :
    HasFDerivAt
      (fun z : E => dist z y ^ p)
      ((p * dist x y ^ (p - 2)) • innerSL Real (x - y)) x := by
  simpa only [dist_eq_norm, ContinuousLinearMap.comp_id] using
    (hasFDerivAt_norm_rpow_of_ne (x - y) p
      (sub_ne_zero.mpr hxy)).comp x
      ((hasFDerivAt_id x).sub_const y)

/-- If a differentiable function is touched from above by a translated
radial power, its derivative is the radial power gradient. -/
theorem fderiv_eq_powerUpperTouchGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {v : E → Real} {p c : Real} {x y : E}
    (hDifferentiable : DifferentiableAt Real v x)
    (hxy : x ≠ y)
    (hUpper : ∀ z, v z ≤ dist z y ^ p + c)
    (hTouch : v x = dist x y ^ p + c) :
    fderiv Real v x =
      (p * dist x y ^ (p - 2)) • innerSL Real (x - y) := by
  let gap : E → Real :=
    fun z => dist z y ^ p + c - v z
  have hGapMin : IsLocalMin gap x := by
    change ∀ᶠ z in 𝓝 x, gap x ≤ gap z
    filter_upwards [] with z
    dsimp only [gap]
    rw [hTouch]
    linarith [hUpper z]
  have hGapDerivative :
      HasFDerivAt gap
        ((p * dist x y ^ (p - 2)) • innerSL Real (x - y) -
          fderiv Real v x) x := by
    dsimp only [gap]
    exact
      ((hasFDerivAt_dist_rpow_left_of_ne p hxy).add_const c).sub
        hDifferentiable.hasFDerivAt
  have hDerivativeZero :=
    hGapMin.hasFDerivAt_eq_zero hGapDerivative
  exact (sub_eq_zero.mp hDerivativeZero).symm

/-- At a differentiability point of a snowflake-Lipschitz potential, a
contact pair determines the potential's derivative. -/
theorem fderiv_eq_powerContactGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {u : E → Real} {p : Real} {x y : E}
    (hPotential :
      ∀ a b, dist (u a) (u b) ≤ dist a b ^ p)
    (hDifferentiable : DifferentiableAt Real u x)
    (hxy : x ≠ y)
    (hContact : dist x y ^ p = u x - u y) :
    fderiv Real u x =
      (p * dist x y ^ (p - 2)) • innerSL Real (x - y) := by
  apply
    fderiv_eq_powerUpperTouchGradient
      hDifferentiable hxy
  · intro z
    have hDifferenceLeDist :
        u z - u y ≤ dist (u z) (u y) := by
      simpa only [Real.dist_eq] using le_abs_self (u z - u y)
    linarith [hDifferenceLeDist.trans (hPotential z y)]
  · linarith

/-- For a nonunit exponent, the vector part of the gradient of
`v ↦ ‖v‖ ^ p` is injective away from the origin. -/
theorem radialRpowGradientCore_injOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {p : Real} (hp : p ≠ 1) :
    Set.InjOn
      (fun v : E => ‖v‖ ^ (p - 2) • v)
      {v : E | v ≠ 0} := by
  intro v hv w hw hGradient
  have hvPos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hNormV :
      ‖‖v‖ ^ (p - 2) • v‖ = ‖v‖ ^ (p - 1) := by
    rw [norm_smul,
      Real.norm_of_nonneg
        (Real.rpow_nonneg (norm_nonneg v) (p - 2))]
    calc
      ‖v‖ ^ (p - 2) * ‖v‖ =
          ‖v‖ ^ ((p - 2) + 1) :=
        (Real.rpow_add_one hvPos.ne' (p - 2)).symm
      _ = ‖v‖ ^ (p - 1) := by ring_nf
  have hNormW :
      ‖‖w‖ ^ (p - 2) • w‖ = ‖w‖ ^ (p - 1) := by
    rw [norm_smul,
      Real.norm_of_nonneg
        (Real.rpow_nonneg (norm_nonneg w) (p - 2))]
    calc
      ‖w‖ ^ (p - 2) * ‖w‖ =
          ‖w‖ ^ ((p - 2) + 1) :=
        (Real.rpow_add_one hwPos.ne' (p - 2)).symm
      _ = ‖w‖ ^ (p - 1) := by ring_nf
  have hPowerNorm :
      ‖v‖ ^ (p - 1) = ‖w‖ ^ (p - 1) := by
    rw [← hNormV, ← hNormW]
    exact congrArg norm hGradient
  have hNorm : ‖v‖ = ‖w‖ :=
    (Real.rpow_left_inj
      (norm_nonneg v) (norm_nonneg w)
      (sub_ne_zero.mpr hp)).mp hPowerNorm
  have hCoefficient :
      ‖v‖ ^ (p - 2) = ‖w‖ ^ (p - 2) :=
    congrArg (fun r : Real => r ^ (p - 2)) hNorm
  change ‖v‖ ^ (p - 2) • v = ‖w‖ ^ (p - 2) • w at hGradient
  rw [hCoefficient] at hGradient
  rw [← sub_eq_zero]
  apply
    (smul_eq_zero_iff_right
      (Real.rpow_pos_of_pos hwPos (p - 2)).ne').mp
  rw [smul_sub, hGradient, sub_self]

/-- At a fixed source point, the radial gradient core uniquely determines a
distinct target. -/
theorem radialRpowGradientAtSource_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {p : Real} (hp : p ≠ 1) {x y y' : E}
    (hy : y ≠ x) (hy' : y' ≠ x)
    (hGradient :
      ‖x - y‖ ^ (p - 2) • (x - y) =
        ‖x - y'‖ ^ (p - 2) • (x - y')) :
    y = y' := by
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hxy' : x - y' ≠ 0 := sub_ne_zero.mpr (Ne.symm hy')
  have hDifference :
      x - y = x - y' :=
    radialRpowGradientCore_injOn hp hxy hxy' hGradient
  exact sub_right_injective hDifference

/-- A differentiable function cannot be touched from above at one point by
two translated sublinear radial powers with different centers. -/
theorem powerUpperTouches_target_unique_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {v : E → Real} {p c c' : Real} {x y y' : E}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hDifferentiable : DifferentiableAt Real v x)
    (hxy : x ≠ y) (hxy' : x ≠ y')
    (hUpper : ∀ z, v z ≤ dist z y ^ p + c)
    (hTouch : v x = dist x y ^ p + c)
    (hUpper' : ∀ z, v z ≤ dist z y' ^ p + c')
    (hTouch' : v x = dist x y' ^ p + c') :
    y = y' := by
  have hGradient :=
    fderiv_eq_powerUpperTouchGradient
      hDifferentiable hxy hUpper hTouch
  have hGradient' :=
    fderiv_eq_powerUpperTouchGradient
      hDifferentiable hxy' hUpper' hTouch'
  have hLinearGradient :
      (p * dist x y ^ (p - 2)) • innerSL Real (x - y) =
        (p * dist x y' ^ (p - 2)) • innerSL Real (x - y') :=
    hGradient.symm.trans hGradient'
  have hScaledGradient :
      (p * dist x y ^ (p - 2)) • (x - y) =
        (p * dist x y' ^ (p - 2)) • (x - y') := by
    apply (innerSL_inj (𝕜 := Real)).mp
    simpa only [map_smul] using hLinearGradient
  have hScaledGradient' :
      p • (dist x y ^ (p - 2) • (x - y)) =
        p • (dist x y' ^ (p - 2) • (x - y')) := by
    simpa only [mul_smul] using hScaledGradient
  have hGradientCore :
      dist x y ^ (p - 2) • (x - y) =
        dist x y' ^ (p - 2) • (x - y') := by
    rw [← sub_eq_zero]
    apply (smul_eq_zero_iff_right hp0.ne').mp
    rw [smul_sub, hScaledGradient', sub_self]
  apply
    radialRpowGradientAtSource_injective
      (ne_of_lt hp1) hxy.symm hxy'.symm
  simpa only [dist_eq_norm] using hGradientCore

/-- A differentiability point of a snowflake-Lipschitz potential has at most
one non-diagonal contact target. -/
theorem powerContact_target_unique_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {u : E → Real} {p : Real} {x y y' : E}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hPotential :
      ∀ a b, dist (u a) (u b) ≤ dist a b ^ p)
    (hDifferentiable : DifferentiableAt Real u x)
    (hxy : x ≠ y) (hxy' : x ≠ y')
    (hContact : dist x y ^ p = u x - u y)
    (hContact' : dist x y' ^ p = u x - u y') :
    y = y' := by
  apply
    powerUpperTouches_target_unique_of_differentiableAt
      (c := u y) (c' := u y')
      hp0 hp1 hDifferentiable hxy hxy'
  · intro z
    have hDifferenceLeDist :
        u z - u y ≤ dist (u z) (u y) := by
      simpa only [Real.dist_eq] using le_abs_self (u z - u y)
    linarith [hDifferenceLeDist.trans (hPotential z y)]
  · linarith
  · intro z
    have hDifferenceLeDist :
        u z - u y' ≤ dist (u z) (u y') := by
      simpa only [Real.dist_eq] using le_abs_self (u z - u y')
    linarith [hDifferenceLeDist.trans (hPotential z y')]
  · linarith

end ConcaveOTLimit
