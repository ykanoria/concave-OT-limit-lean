import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

namespace ConcaveOTLimit

/-- The strict-concavity four-point comparison used to rule out connected
transport arches. -/
theorem strictConcaveArchComparison {phi : Real -> Real}
    (hphi : StrictConcaveOn Real (Ici 0) phi) {a b c : Real}
    (ha : 0 < a) (hb : 0 <= b) (hc : 0 < c) :
    phi (a + b) + phi (b + c) >
      phi b + phi (a + b + c) := by
  have hac_pos : 0 < a + c := add_pos ha hc
  have hac : a + c ≠ 0 := ne_of_gt hac_pos
  have hca : c / (a + c) + a / (a + c) = 1 := by
    field_simp
    ring
  have hac' : a / (a + c) + c / (a + c) = 1 := by
    linarith
  have hb_ne_hz : b ≠ a + b + c := by
    linarith
  have hz_nonneg : 0 <= a + b + c :=
    add_nonneg (add_nonneg ha.le hb) hc.le
  have hleft :=
    hphi.2 (show b ∈ Ici (0 : Real) from hb)
      (show a + b + c ∈ Ici (0 : Real) from hz_nonneg)
      hb_ne_hz (div_pos hc hac_pos) (div_pos ha hac_pos) hca
  have hright :=
    hphi.2 (show b ∈ Ici (0 : Real) from hb)
      (show a + b + c ∈ Ici (0 : Real) from hz_nonneg)
      hb_ne_hz (div_pos ha hac_pos) (div_pos hc hac_pos) hac'
  simp only [smul_eq_mul] at hleft hright
  have hweightedLeft :
      c / (a + c) * b + a / (a + c) * (a + b + c) =
        a + b := by
    field_simp
    ring
  have hweightedRight :
      a / (a + c) * b + c / (a + c) * (a + b + c) =
        b + c := by
    field_simp
    ring
  rw [hweightedLeft] at hleft
  rw [hweightedRight] at hright
  calc
    phi b + phi (a + b + c) =
        1 * phi b + 1 * phi (a + b + c) := by ring
    _ = (c / (a + c) * phi b +
          a / (a + c) * phi (a + b + c)) +
        (a / (a + c) * phi b +
          c / (a + c) * phi (a + b + c)) := by
      rw [← hca]
      ring
    _ < phi (a + b) + phi (b + c) := add_lt_add hleft hright

end ConcaveOTLimit
