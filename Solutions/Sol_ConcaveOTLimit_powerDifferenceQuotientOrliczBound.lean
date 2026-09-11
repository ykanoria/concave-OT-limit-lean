import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic

open ConcaveOTLimit

private theorem psi_nonneg {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem quotient_eq_exp {epsilon r : Real} (hr : 0 < r) :
    (powerProfile epsilon r - r) / epsilon =
      r * (Real.exp (-epsilon * Real.log r) - 1) / epsilon := by
  rw [powerProfile, Real.rpow_def_of_pos hr]
  rw [show Real.log r * (1 - epsilon) =
      Real.log r + (-epsilon * Real.log r) by ring,
    Real.exp_add, Real.exp_log hr]
  ring

private theorem power_profile_eq_mul_exp {epsilon r : Real} (hr : 0 < r) :
    powerProfile epsilon r =
      r * Real.exp (-epsilon * Real.log r) := by
  rw [powerProfile, Real.rpow_def_of_pos hr]
  rw [show Real.log r * (1 - epsilon) =
      Real.log r + (-epsilon * Real.log r) by ring,
    Real.exp_add, Real.exp_log hr]

private theorem exp_sub_one_le_self_mul_exp (x : Real) :
    Real.exp x - 1 <= x * Real.exp x := by
  have h :=
    mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x))
      (Real.exp_pos x).le
  rw [Real.exp_neg] at h
  have hExpNe : Not (Real.exp x = 0) := (Real.exp_pos x).ne'
  rw [inv_mul_cancel₀ hExpNe] at h
  linarith

private theorem neg_mul_log_le_quotient
    {epsilon r : Real} (hEpsilonPos : 0 < epsilon) (hr : 0 < r) :
    Real.negMulLog r <=
      (powerProfile epsilon r - r) / epsilon := by
  rw [quotient_eq_exp hr]
  rw [le_div_iff₀ hEpsilonPos]
  have hExp := Real.add_one_le_exp (-epsilon * Real.log r)
  have hInner :
      -epsilon * Real.log r <=
        Real.exp (-epsilon * Real.log r) - 1 := by
    linarith
  have hMul := mul_le_mul_of_nonneg_left hInner hr.le
  unfold Real.negMulLog
  nlinarith

private theorem quotient_nonpos_of_one_le
    {epsilon r : Real} (hEpsilonPos : 0 < epsilon) (hr : 1 <= r) :
    (powerProfile epsilon r - r) / epsilon <= 0 := by
  have hPower : powerProfile epsilon r <= r := by
    unfold powerProfile
    simpa using
      Real.rpow_le_rpow_of_exponent_le hr
        (by linarith : 1 - epsilon <= 1)
  exact
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hPower)
      hEpsilonPos.le

private theorem quotient_nonneg_of_le_one
    {epsilon r : Real} (hEpsilonPos : 0 < epsilon)
    (hrPos : 0 < r) (hrOne : r <= 1) :
    0 <= (powerProfile epsilon r - r) / epsilon := by
  have hPower : r <= powerProfile epsilon r := by
    unfold powerProfile
    simpa using
      Real.rpow_le_rpow_of_exponent_ge hrPos hrOne
        (by linarith : 1 - epsilon <= 1)
  exact div_nonneg (sub_nonneg.mpr hPower) hEpsilonPos.le

private theorem abs_quotient_le_mul_log
    {epsilon r : Real} (hEpsilonPos : 0 < epsilon) (hr : 1 <= r) :
    abs ((powerProfile epsilon r - r) / epsilon) <=
      r * Real.log r := by
  rw [abs_of_nonpos (quotient_nonpos_of_one_le hEpsilonPos hr)]
  calc
    -((powerProfile epsilon r - r) / epsilon)
        <= -Real.negMulLog r :=
      neg_le_neg
        (neg_mul_log_le_quotient hEpsilonPos
          (lt_of_lt_of_le zero_lt_one hr))
    _ = r * Real.log r := by
      simp [Real.negMulLog]

private theorem quotient_le_rpow_mul_neg_log
    {epsilon r : Real} (hEpsilonPos : 0 < epsilon) (hr : 0 < r) :
    (powerProfile epsilon r - r) / epsilon <=
      r ^ (1 - epsilon) * (-Real.log r) := by
  rw [quotient_eq_exp hr, div_le_iff₀ hEpsilonPos]
  rw [show r ^ (1 - epsilon) =
      r * Real.exp (-epsilon * Real.log r) by
        simpa [powerProfile] using power_profile_eq_mul_exp
          (epsilon := epsilon) hr]
  calc
    r * (Real.exp (-epsilon * Real.log r) - 1)
        <= r *
          ((-epsilon * Real.log r) *
            Real.exp (-epsilon * Real.log r)) :=
      mul_le_mul_of_nonneg_left
        (exp_sub_one_le_self_mul_exp _) hr.le
    _ =
        (r * Real.exp (-epsilon * Real.log r)) *
          (-Real.log r) * epsilon := by
      ring

private theorem rpow_half_mul_neg_log_le_two
    {r : Real} (hr : 0 < r) :
    r ^ (1 / 2 : Real) * (-Real.log r) <= 2 := by
  let s : Real := r ^ (1 / 2 : Real)
  have hsNonneg : 0 <= s := Real.rpow_nonneg hr.le _
  have hNegMulLog : Real.negMulLog s <= 1 := by
    linarith [Real.negMulLog_le_one_sub_self hsNonneg]
  have hLog : Real.log s = (1 / 2 : Real) * Real.log r := by
    dsimp [s]
    exact Real.log_rpow hr (1 / 2 : Real)
  have hIdentity :
      r ^ (1 / 2 : Real) * (-Real.log r) =
        2 * Real.negMulLog s := by
    dsimp [s]
    rw [Real.negMulLog, hLog]
    ring
  rw [hIdentity]
  linarith

private theorem quotient_le_two_of_le_one
    {epsilon r : Real}
    (hEpsilonPos : 0 < epsilon) (hEpsilonLeHalf : epsilon <= 1 / 2)
    (hrPos : 0 < r) (hrOne : r <= 1) :
    (powerProfile epsilon r - r) / epsilon <= 2 := by
  have hPower :
      r ^ (1 - epsilon) <= r ^ (1 / 2 : Real) :=
    Real.rpow_le_rpow_of_exponent_ge hrPos hrOne (by linarith)
  have hNegLog : 0 <= -Real.log r :=
    neg_nonneg.mpr (Real.log_nonpos hrPos.le hrOne)
  calc
    (powerProfile epsilon r - r) / epsilon
        <= r ^ (1 - epsilon) * (-Real.log r) :=
      quotient_le_rpow_mul_neg_log hEpsilonPos hrPos
    _ <= r ^ (1 / 2 : Real) * (-Real.log r) :=
      mul_le_mul_of_nonneg_right hPower hNegLog
    _ <= 2 := rpow_half_mul_neg_log_le_two hrPos

private theorem quotient_unit_interval_bounds
    {epsilon r : Real}
    (hEpsilonPos : 0 < epsilon) (hEpsilonLeHalf : epsilon <= 1 / 2)
    (hr : 0 <= r) (hrOne : r <= 1) :
    0 <= (powerProfile epsilon r - r) / epsilon /\
      (powerProfile epsilon r - r) / epsilon <= 2 := by
  rcases hr.eq_or_lt with rfl | hrPos
  · have hEpsilonLtOne : epsilon < 1 :=
      lt_of_le_of_lt hEpsilonLeHalf (by norm_num)
    have hPower : (0 : Real) ^ (1 - epsilon) = 0 :=
      Real.zero_rpow (by linarith)
    simp [powerProfile, hPower]
  · exact
      And.intro
        (quotient_nonneg_of_le_one hEpsilonPos hrPos hrOne)
        (quotient_le_two_of_le_one
          hEpsilonPos hEpsilonLeHalf hrPos hrOne)

private theorem mul_log_le_psi {r : Real} (hr : 1 <= r) :
    r * Real.log r <= Psi r := by
  have hLog : Real.log r <= Real.log (1 + r) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hr) (by linarith)
  exact mul_le_mul_of_nonneg_left hLog (by positivity)

theorem solution
    {epsilon r : Real}
    (hEpsilonPos : 0 < epsilon) (hEpsilonLeHalf : epsilon <= 1 / 2)
    (hr : 0 <= r) :
    abs ((powerProfile epsilon r - r) / epsilon) <= 2 + Psi r := by
  by_cases hrOne : r <= 1
  · have hBounds :=
      quotient_unit_interval_bounds
        hEpsilonPos hEpsilonLeHalf hr hrOne
    rw [abs_of_nonneg hBounds.1]
    linarith [psi_nonneg hr]
  · have hOne : 1 <= r := le_of_not_ge hrOne
    exact
      (abs_quotient_le_mul_log hEpsilonPos hOne).trans <|
        (mul_log_le_psi hOne).trans (by linarith)
