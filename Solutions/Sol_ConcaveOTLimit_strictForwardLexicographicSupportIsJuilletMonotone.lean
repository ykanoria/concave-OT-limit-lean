import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

open ConcaveOTLimit

private theorem strict_arch_comparison
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
  have hsumNonneg : 0 <= a + b + c := by
    linarith
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

private theorem crossing_swap_improves
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
  let a := x' - x
  let b := y - x'
  let c := y' - y
  have ha : 0 < a := sub_pos.mpr hCross.1
  have hb : 0 <= b := (sub_pos.mpr hCross.2.1).le
  have hc : 0 < c := sub_pos.mpr hCross.2.2
  have hArch := strict_arch_comparison hProfile ha hb hc
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
  constructor
  · rw [hxy, hx'y', hxy', hx'y]
    ring
  · rw [hxy, hx'y', hxy', hx'y]
    simpa [add_comm] using hArch

private theorem connected_swap_improves
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
  let a := y - x
  let c := z - y
  have ha : 0 < a := sub_pos.mpr hxy
  have hc : 0 < c := sub_pos.mpr hyz
  have hArch :=
    strict_arch_comparison hProfile ha (show (0 : Real) <= 0 from le_rfl) hc
  have hxyDist : dist x y = a := by
    rw [hdist x y hxy.le]
  have hyzDist : dist y z = c := by
    rw [hdist y z hyz.le]
  have hxzDist : dist x z = a + c := by
    rw [hdist x z (hxy.trans hyz).le]
    dsimp [a, c]
    ring
  constructor
  · rw [hxyDist, hyzDist, hxzDist, dist_self]
    ring
  · rw [hxyDist, hyzDist, hxzDist, dist_self]
    simpa [add_comm] using hArch

theorem solution
    {profile : Real -> Real}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    {support : Set (Real × Real)}
    (hForward :
      forall {x y : Real}, (x, y) ∈ support -> x < y)
    (hLex :
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y))) :
    (forall {x y : Real}, (x, y) ∈ support -> x < y) /\
      (forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          Not ((x < x' /\ x' < y /\ y < y') \/
            (x' < x /\ x < y' /\ y' < y))) /\
      (forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          y ≠ x' /\ y' ≠ x) /\
      (forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          ((x < x' /\ y' < y) \/ (x' < x /\ y < y')) ->
            0 <= (y - x) * (y' - x')) := by
  refine ⟨hForward, ?_, ?_, ?_⟩
  · intro x y x' y' hxy hxy'
    rintro (hCross | hCross)
    · have hImprove := crossing_swap_improves hProfile hCross
      exact
        (not_lt_of_ge ((hLex hxy hxy').2 hImprove.1)) hImprove.2
    · have hImprove := crossing_swap_improves hProfile hCross
      exact
        (not_lt_of_ge ((hLex hxy' hxy).2 hImprove.1)) hImprove.2
  · intro x y x' y' hxy hxy'
    constructor
    · intro hyx'
      subst x'
      have hImprove :=
        connected_swap_improves hProfile (hForward hxy) (hForward hxy')
      exact
        (not_lt_of_ge ((hLex hxy hxy').2 hImprove.1)) hImprove.2
    · intro hy'x
      subst x
      have hImprove :=
        connected_swap_improves hProfile (hForward hxy') (hForward hxy)
      exact
        (not_lt_of_ge ((hLex hxy' hxy).2 hImprove.1)) hImprove.2
  · intro x y x' y' hxy hxy' _
    exact mul_nonneg
      (sub_nonneg.mpr (hForward hxy).le)
      (sub_nonneg.mpr (hForward hxy').le)
