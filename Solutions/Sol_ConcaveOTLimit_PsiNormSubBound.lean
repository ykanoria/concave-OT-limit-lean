import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open ConcaveOTLimit

private theorem psi_nonneg {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem psi_mono {a b : Real} (ha : 0 <= a) (hab : a <= b) :
    Psi a <= Psi b := by
  have hb : 0 <= b := ha.trans hab
  have hlogNonneg : 0 <= Real.log (1 + a) :=
    Real.log_nonneg (by linarith)
  have hlogLe : Real.log (1 + a) <= Real.log (1 + b) :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul hab hlogLe hlogNonneg hb

private theorem log_two_nonneg : 0 <= Real.log 2 :=
  Real.log_nonneg (by norm_num)

private theorem psi_two_mul_le {t : Real} (ht : 0 <= t) :
    Psi (2 * t) <= 4 * Psi t + 2 * Real.log 2 := by
  have harg : 1 + 2 * t <= 2 * (1 + t) := by
    linarith
  have hlog :
      Real.log (1 + 2 * t) <= Real.log 2 + Real.log (1 + t) := by
    calc
      Real.log (1 + 2 * t) <= Real.log (2 * (1 + t)) :=
        Real.log_le_log (by linarith) harg
      _ = Real.log 2 + Real.log (1 + t) := by
        rw [Real.log_mul] <;> positivity
  have hbase : Psi (2 * t) <= 2 * Psi t + 2 * t * Real.log 2 := by
    unfold Psi
    calc
      (2 * t) * Real.log (1 + 2 * t)
          <= (2 * t) * (Real.log 2 + Real.log (1 + t)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 2 * (t * Real.log (1 + t)) + 2 * t * Real.log 2 := by
        ring
  by_cases htOne : t <= 1
  · have hTwoT : 2 * t <= 2 := by
      linarith
    have htail : 2 * t * Real.log 2 <= 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_right hTwoT log_two_nonneg
    have hpsi : 0 <= Psi t := psi_nonneg ht
    linarith
  · have hOneT : 1 <= t := le_of_not_ge htOne
    have hlogTwo : Real.log 2 <= Real.log (1 + t) :=
      Real.log_le_log (by norm_num) (by linarith)
    have htLog : t * Real.log 2 <= t * Real.log (1 + t) :=
      mul_le_mul_of_nonneg_left hlogTwo ht
    have htail : 2 * t * Real.log 2 <= 2 * Psi t := by
      unfold Psi
      linarith
    linarith [log_two_nonneg]

private theorem psi_add_le {a b : Real} (ha : 0 <= a) (hb : 0 <= b) :
    Psi (a + b) <= 4 * (1 + Psi a + Psi b) := by
  let m := max a b
  have hm : 0 <= m := ha.trans (le_max_left a b)
  have habm : a + b <= 2 * m := by
    dsimp [m]
    linarith [le_max_left a b, le_max_right a b]
  have hmono : Psi (a + b) <= Psi (2 * m) :=
    psi_mono (add_nonneg ha hb) habm
  have hscale := psi_two_mul_le hm
  have hmSum : Psi m <= Psi a + Psi b := by
    rcases max_choice a b with h | h
    · rw [show m = a by exact h]
      linarith [psi_nonneg hb]
    · rw [show m = b by exact h]
      linarith [psi_nonneg ha]
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : Real) < 2 by norm_num)
      (show Not ((2 : Real) = 1) by norm_num)
    norm_num at h
    exact h
  linarith

theorem solution
    {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    Psi ‖x - y‖ <= 4 * (1 + Psi ‖x‖ + Psi ‖y‖) := by
  calc
    Psi ‖x - y‖ <= Psi (‖x‖ + ‖y‖) :=
      psi_mono (norm_nonneg _) (norm_sub_le x y)
    _ <= 4 * (1 + Psi ‖x‖ + Psi ‖y‖) :=
      psi_add_le (norm_nonneg _) (norm_nonneg _)
