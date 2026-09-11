import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic

namespace ConcaveOTLimit

/-- The logarithmic profile is a lower bound for every admissible positive
power difference quotient. -/
theorem logarithmicProfileLePowerDifferenceQuotient
    {epsilon r : Real}
    (hEpsilonPos : 0 < epsilon) (hEpsilonLtOne : epsilon < 1)
    (hr : 0 <= r) :
    logarithmicProfile r <=
      (powerProfile epsilon r - r) / epsilon := by
  rcases hr.eq_or_lt with rfl | hr
  · have hPower : (0 : Real) ^ (1 - epsilon) = 0 :=
      Real.zero_rpow (by linarith)
    simp [logarithmicProfile, powerProfile, hPower]
  · rw [powerProfile, Real.rpow_def_of_pos hr]
    rw [show Real.log r * (1 - epsilon) =
        Real.log r + (-epsilon * Real.log r) by ring,
      Real.exp_add, Real.exp_log hr]
    rw [le_div_iff₀ hEpsilonPos]
    have hExp := Real.add_one_le_exp (-epsilon * Real.log r)
    have hInner :
        -epsilon * Real.log r <=
          Real.exp (-epsilon * Real.log r) - 1 := by
      linarith
    have hMul := mul_le_mul_of_nonneg_left hInner hr.le
    unfold logarithmicProfile Real.negMulLog
    nlinarith

end ConcaveOTLimit
