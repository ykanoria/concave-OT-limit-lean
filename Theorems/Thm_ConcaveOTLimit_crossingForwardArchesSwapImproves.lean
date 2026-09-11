import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

namespace ConcaveOTLimit

private theorem arch_comparison
    {profile : Real -> Real}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    {a b c : Real} (ha : 0 < a) (hb : 0 <= b) (hc : 0 < c) :
    profile b + profile (a + b + c) <
      profile (a + b) + profile (b + c) := by
  have hacPos : 0 < a + c := add_pos ha hc
  have hac : a + c ≠ 0 := ne_of_gt hacPos
  have hca : c / (a + c) + a / (a + c) = 1 := by
    field_simp
    ring
  have hac' : a / (a + c) + c / (a + c) = 1 := by
    linarith
  have hne : b ≠ a + b + c := by
    linarith
  have hsumNonneg : 0 <= a + b + c :=
    add_nonneg (add_nonneg ha.le hb) hc.le
  have hleft :=
    hProfile.2 (show b ∈ Ici (0 : Real) from hb)
      (show a + b + c ∈ Ici (0 : Real) from hsumNonneg)
      hne (div_pos hc hacPos) (div_pos ha hacPos) hca
  have hright :=
    hProfile.2 (show b ∈ Ici (0 : Real) from hb)
      (show a + b + c ∈ Ici (0 : Real) from hsumNonneg)
      hne (div_pos ha hacPos) (div_pos hc hacPos) hac'
  simp only [smul_eq_mul] at hleft hright
  have hweightedLeft :
      c / (a + c) * b +
          a / (a + c) * (a + b + c) = a + b := by
    field_simp
    ring
  have hweightedRight :
      a / (a + c) * b +
          c / (a + c) * (a + b + c) = b + c := by
    field_simp
    ring
  rw [hweightedLeft] at hleft
  rw [hweightedRight] at hright
  calc
    profile b + profile (a + b + c) =
        1 * profile b + 1 * profile (a + b + c) := by ring
    _ = (c / (a + c) * profile b +
          a / (a + c) * profile (a + b + c)) +
        (a / (a + c) * profile b +
          c / (a + c) * profile (a + b + c)) := by
      rw [← hca]
      ring
    _ < profile (a + b) + profile (b + c) :=
      add_lt_add hleft hright

/-- Rerouting two crossing forward arches preserves distance cost and
strictly lowers every strictly concave secondary cost. -/
theorem crossingForwardArchesSwapImproves
    {profile : Real -> Real}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    {x x' y y' : Real}
    (hCross : x < x' /\ x' < y /\ y < y') :
    dist x y + dist x' y' = dist x y' + dist x' y /\
      profile (dist x y') + profile (dist x' y) <
        profile (dist x y) + profile (dist x' y') := by
  have hdist (p q : Real) (hpq : p <= q) :
      dist p q = q - p := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  constructor
  · rw [hdist x y (hCross.1.trans hCross.2.1).le,
      hdist x' y' (hCross.2.1.trans hCross.2.2).le,
      hdist x y'
        (hCross.1.trans (hCross.2.1.trans hCross.2.2)).le,
      hdist x' y hCross.2.1.le]
    ring
  · let a := x' - x
    let b := y - x'
    let c := y' - y
    have ha : 0 < a := sub_pos.mpr hCross.1
    have hb : 0 <= b := (sub_pos.mpr hCross.2.1).le
    have hc : 0 < c := sub_pos.mpr hCross.2.2
    have harch := arch_comparison hProfile ha hb hc
    have hxy : dist x y = a + b := by
      rw [hdist x y (hCross.1.trans hCross.2.1).le]
      dsimp [a, b]
      ring
    have hx'y' : dist x' y' = b + c := by
      rw [hdist x' y' (hCross.2.1.trans hCross.2.2).le]
      dsimp [b, c]
      ring
    have hxy' : dist x y' = a + b + c := by
      rw [hdist x y'
        (hCross.1.trans (hCross.2.1.trans hCross.2.2)).le]
      dsimp [a, b, c]
      ring
    have hx'y : dist x' y = b := by
      rw [hdist x' y hCross.2.1.le]
    rw [hxy, hx'y', hxy', hx'y]
    simpa [add_comm] using harch

end ConcaveOTLimit
