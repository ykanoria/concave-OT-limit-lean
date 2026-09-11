import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set

open ConcaveOTLimit

theorem solution
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile) :
    exists C : Real, 0 <= C /\
      forall {d : Real}, 0 <= d ->
        |profile d| <= C * (1 + d) := by
  rcases hProfile with ⟨hConcave, C₀, hC₀, hLower⟩
  let C : Real :=
    3 * C₀ + 2 * |profile 0| + 2 * |profile 1|
  have hC : 0 <= C := by
    dsimp [C]
    nlinarith [abs_nonneg (profile 0), abs_nonneg (profile 1)]
  refine ⟨C, hC, ?_⟩
  intro d hd
  have hOneAdd : 0 <= 1 + d := by
    linarith
  have hC₀le : C₀ <= C := by
    dsimp [C]
    nlinarith [abs_nonneg (profile 0), abs_nonneg (profile 1)]
  have hLowerC : -(C * (1 + d)) <= profile d := by
    have hScale :
        C₀ * (1 + d) <= C * (1 + d) :=
      mul_le_mul_of_nonneg_right hC₀le hOneAdd
    exact
      (neg_le_neg hScale).trans
        (by simpa only [neg_mul] using hLower hd)
  apply (abs_le).2
  refine ⟨hLowerC, ?_⟩
  by_cases hdOne : d <= 1
  · have hReflectedNonnegative : 0 <= 2 - d := by
      linarith
    have hMidpointRaw :=
      hConcave.2
        (show d ∈ Ici (0 : Real) by exact hd)
        (show 2 - d ∈ Ici (0 : Real) by
          exact hReflectedNonnegative)
        (show 0 <= (1 / 2 : Real) by norm_num)
        (show 0 <= (1 / 2 : Real) by norm_num)
        (show (1 / 2 : Real) + 1 / 2 = 1 by norm_num)
    have hPoint :
        (1 / 2 : Real) * d + (1 / 2) * (2 - d) = 1 := by
      ring
    have hMidpoint :
        (1 / 2 : Real) * profile d +
            (1 / 2) * profile (2 - d) <= profile 1 := by
      simpa only [smul_eq_mul, hPoint] using hMidpointRaw
    have hReflectedLower := hLower hReflectedNonnegative
    have hUpperRaw :
        profile d <= 2 * profile 1 + C₀ * (3 - d) := by
      nlinarith [hMidpoint, hReflectedLower]
    have hC₀d : 0 <= C₀ * d :=
      mul_nonneg hC₀ hd
    have hUpperConstant :
        profile d <= 2 * |profile 1| + 3 * C₀ := by
      nlinarith [hUpperRaw, le_abs_self (profile 1), hC₀d]
    have hConstantLe :
        2 * |profile 1| + 3 * C₀ <= C := by
      dsimp [C]
      nlinarith [abs_nonneg (profile 0)]
    have hCGrowth : C <= C * (1 + d) := by
      nlinarith [mul_nonneg hC hd]
    exact hUpperConstant.trans (hConstantLe.trans hCGrowth)
  · have hOneLt : 1 < d :=
      lt_of_not_ge hdOne
    have hSlopeRaw :=
      hConcave.slope_anti_adjacent
        (show (0 : Real) ∈ Ici 0 by simp)
        (show d ∈ Ici (0 : Real) by exact hd)
        (show (0 : Real) < 1 by norm_num)
        hOneLt
    have hSlope :
        (profile d - profile 1) / (d - 1) <=
          profile 1 - profile 0 := by
      simpa using hSlopeRaw
    have hScaled :
        profile d - profile 1 <=
          (profile 1 - profile 0) * (d - 1) :=
      (div_le_iff₀ (sub_pos.mpr hOneLt)).mp hSlope
    have hAffine :
        profile d <=
          profile 1 + (d - 1) * (profile 1 - profile 0) := by
      nlinarith [hScaled]
    have hDifference :
        profile 1 - profile 0 <=
          |profile 1| + |profile 0| := by
      calc
        profile 1 - profile 0
            <= |profile 1 - profile 0| :=
          le_abs_self _
        _ <= |profile 1| + |profile 0| :=
          abs_sub _ _
    have hScaledDifference :
        (d - 1) * (profile 1 - profile 0) <=
          (d - 1) * (|profile 1| + |profile 0|) :=
      mul_le_mul_of_nonneg_left hDifference (sub_nonneg.mpr hOneLt.le)
    have hUpperAbs :
        profile d <=
          |profile 1| +
            (d - 1) * (|profile 1| + |profile 0|) :=
      hAffine.trans
        (add_le_add (le_abs_self (profile 1)) hScaledDifference)
    have hEnvelope :
        |profile 1| +
            (d - 1) * (|profile 1| + |profile 0|)
          <= (|profile 0| + |profile 1|) * (1 + d) := by
      nlinarith [abs_nonneg (profile 0), abs_nonneg (profile 1)]
    have hCoefficient :
        |profile 0| + |profile 1| <= C := by
      dsimp [C]
      nlinarith [hC₀, abs_nonneg (profile 0), abs_nonneg (profile 1)]
    have hScale :
        (|profile 0| + |profile 1|) * (1 + d) <=
          C * (1 + d) :=
      mul_le_mul_of_nonneg_right hCoefficient hOneAdd
    exact hUpperAbs.trans (hEnvelope.trans hScale)
