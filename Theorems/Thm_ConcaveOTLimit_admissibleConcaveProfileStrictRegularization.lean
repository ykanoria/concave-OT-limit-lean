import Theorems.Thm_ConcaveOTLimit_powerProfileStrictConcave
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set

namespace ConcaveOTLimit

/-- Adding a positive multiple of the half-power profile turns every
admissible concave profile into an admissible strictly concave profile. -/
theorem admissibleConcaveProfileStrictRegularization
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    {delta : Real} (hDelta : 0 < delta) :
    AdmissibleStrictlyConcaveProfile
      (fun d => profile d + delta * powerProfile (1 / 2) d) := by
  rcases hProfile with ⟨hConcave, C, hC, hLower⟩
  have hHalf : (1 / 2 : Real) ∈ epsilonDomain := by
    change (0 : Real) < 1 / 2 ∧ (1 / 2 : Real) < 1
    norm_num
  have hPowerStrict :
      StrictConcaveOn Real (Ici 0) (powerProfile (1 / 2)) :=
    powerProfileStrictConcave hHalf
  have hScaledStrict :
      StrictConcaveOn Real (Ici 0)
        (fun d => delta * powerProfile (1 / 2) d) := by
    refine ⟨hPowerStrict.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hStrict := hPowerStrict.2 hx hy hxy ha hb hab
    calc
      a • (delta * powerProfile (1 / 2) x) +
            b • (delta * powerProfile (1 / 2) y) =
          delta *
            (a • powerProfile (1 / 2) x +
              b • powerProfile (1 / 2) y) := by
        simp only [smul_eq_mul]
        ring
      _ < delta * powerProfile (1 / 2) (a • x + b • y) :=
        mul_lt_mul_of_pos_left hStrict hDelta
  refine ⟨?_, C, hC, ?_⟩
  · simpa only [Pi.add_apply] using
      hConcave.add_strictConcaveOn hScaledStrict
  · intro d hd
    have hPowerNonnegative : 0 <= powerProfile (1 / 2) d := by
      unfold powerProfile
      exact Real.rpow_nonneg hd _
    exact
      (hLower hd).trans
        (le_add_of_nonneg_right
          (mul_nonneg hDelta.le hPowerNonnegative))

end ConcaveOTLimit
