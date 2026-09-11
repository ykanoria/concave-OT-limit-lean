import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic.Linarith

namespace ConcaveOTLimit

/-- Two distance-contact pairs satisfy the distance two-cycle inequality. -/
theorem distanceContactTwoCycle
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {x y x' y' : E}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hxy' : (x', y') ∈ distanceContactSet u) :
    dist x y + dist x' y' <= dist x y' + dist x' y := by
  have hcrossLeft : u x - u y' <= dist x y' := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul x y'
  have hcrossRight : u x' - u y <= dist x' y := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul x' y
  change dist x y = u x - u y at hxy
  change dist x' y' = u x' - u y' at hxy'
  linarith

end ConcaveOTLimit
