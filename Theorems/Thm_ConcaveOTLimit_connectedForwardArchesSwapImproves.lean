import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

namespace ConcaveOTLimit

private theorem connected_arch_comparison
    {profile : Real -> Real}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    {a c : Real} (ha : 0 < a) (hc : 0 < c) :
    profile 0 + profile (a + c) <
      profile a + profile c := by
  have hacPos : 0 < a + c := add_pos ha hc
  have hac : a + c ≠ 0 := ne_of_gt hacPos
  have hca : c / (a + c) + a / (a + c) = 1 := by
    field_simp
    ring
  have hac' : a / (a + c) + c / (a + c) = 1 := by
    linarith
  have hzero : (0 : Real) ∈ Ici 0 :=
    show (0 : Real) <= 0 from le_rfl
  have hsum : a + c ∈ Ici (0 : Real) := hacPos.le
  have hne : (0 : Real) ≠ a + c := ne_of_lt hacPos
  have hleft :=
    hProfile.2 hzero hsum hne
      (div_pos hc hacPos) (div_pos ha hacPos) hca
  have hright :=
    hProfile.2 hzero hsum hne
      (div_pos ha hacPos) (div_pos hc hacPos) hac'
  simp only [smul_eq_mul] at hleft hright
  have hweightedLeft :
      c / (a + c) * 0 + a / (a + c) * (a + c) = a := by
    field_simp
    ring
  have hweightedRight :
      a / (a + c) * 0 + c / (a + c) * (a + c) = c := by
    field_simp
    ring
  rw [hweightedLeft] at hleft
  rw [hweightedRight] at hright
  calc
    profile 0 + profile (a + c) =
        1 * profile 0 + 1 * profile (a + c) := by ring
    _ = (c / (a + c) * profile 0 +
          a / (a + c) * profile (a + c)) +
        (a / (a + c) * profile 0 +
          c / (a + c) * profile (a + c)) := by
      rw [← hca]
      ring
    _ < profile a + profile c := add_lt_add hleft hright

/-- Rerouting two connected forward arches preserves distance cost and
strictly lowers every strictly concave secondary cost. -/
theorem connectedForwardArchesSwapImproves
    {profile : Real -> Real}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    {x y z : Real} (hxy : x < y) (hyz : y < z) :
    dist x y + dist y z = dist x z + dist y y /\
      profile (dist x z) + profile (dist y y) <
        profile (dist x y) + profile (dist y z) := by
  have hdist (p q : Real) (hpq : p <= q) :
      dist p q = q - p := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  constructor
  · rw [hdist x y hxy.le, hdist y z hyz.le,
      hdist x z (hxy.trans hyz).le, dist_self]
    ring
  · let a := y - x
    let c := z - y
    have ha : 0 < a := sub_pos.mpr hxy
    have hc : 0 < c := sub_pos.mpr hyz
    have harch := connected_arch_comparison hProfile ha hc
    have hxyDist : dist x y = a := by
      rw [hdist x y hxy.le]
    have hyzDist : dist y z = c := by
      rw [hdist y z hyz.le]
    have hxzDist : dist x z = a + c := by
      rw [hdist x z (hxy.trans hyz).le]
      dsimp [a, c]
      ring
    rw [hxyDist, hyzDist, hxzDist, dist_self]
    simpa [add_comm] using harch

end ConcaveOTLimit
