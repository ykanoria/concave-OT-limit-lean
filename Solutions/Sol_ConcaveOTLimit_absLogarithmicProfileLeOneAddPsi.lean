import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic.Linarith

open ConcaveOTLimit

private theorem psi_nonneg {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem logarithmic_profile_ge_neg_psi
    {r : Real} (hr : 0 <= r) :
    -Psi r <= logarithmicProfile r := by
  by_cases hrOne : r <= 1
  · have hlogNonneg :
        0 <= logarithmicProfile r := by
      unfold logarithmicProfile
      exact Real.negMulLog_nonneg hr hrOne
    linarith [psi_nonneg hr]
  · have hOne : 1 <= r := le_of_not_ge hrOne
    have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one hOne
    have hlog : Real.log r <= Real.log (1 + r) :=
      Real.log_le_log hrPos (by linarith)
    have hmul : r * Real.log r <= r * Real.log (1 + r) :=
      mul_le_mul_of_nonneg_left hlog hr
    unfold Psi logarithmicProfile Real.negMulLog
    linarith

theorem solution
    {r : Real} (hr : 0 <= r) :
    abs (logarithmicProfile r) <= 1 + Psi r := by
  by_cases hrOne : r <= 1
  · have hnonneg : 0 <= logarithmicProfile r := by
      unfold logarithmicProfile
      exact Real.negMulLog_nonneg hr hrOne
    rw [abs_of_nonneg hnonneg]
    have hupp : logarithmicProfile r <= 1 - r := by
      unfold logarithmicProfile
      exact Real.negMulLog_le_one_sub_self hr
    linarith [psi_nonneg hr]
  · have hOne : 1 <= r := le_of_not_ge hrOne
    have hnonpos : logarithmicProfile r <= 0 := by
      have h := Real.mul_log_nonneg hOne
      simpa [logarithmicProfile, Real.negMulLog] using neg_nonpos.mpr h
    rw [abs_of_nonpos hnonpos]
    linarith [logarithmic_profile_ge_neg_psi hr]
