import Mathlib.Data.NNReal.Basic

theorem solution (a b : NNReal) :
    ∃ c : NNReal, 0 < c ∧ c * a ≤ 1 ∧ c * b ≤ 1 := by
  let d : NNReal := 1 + a + b
  have hd : 0 < d := by
    dsimp [d]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg zero_lt_one zero_le') zero_le'
  refine ⟨d⁻¹, inv_pos.mpr hd, ?_, ?_⟩
  · apply inv_mul_le_one_of_le₀
    · dsimp [d]
      exact (le_add_of_nonneg_left zero_le_one).trans
        (le_add_of_nonneg_right zero_le')
    · exact hd.le
  · apply inv_mul_le_one_of_le₀
    · dsimp [d]
      exact le_add_of_nonneg_left (add_nonneg zero_le_one zero_le')
    · exact hd.le
