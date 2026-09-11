import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.Linarith

open Set

namespace ConcaveOTLimit

/-- Contact equality propagates to both subsegments through any point of the
closed segment. -/
theorem distanceContactSegmentSaturation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {x y z : E}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hz : z ∈ segment Real x y) :
    (x, z) ∈ distanceContactSet u /\
      (z, y) ∈ distanceContactSet u := by
  have hleft : u x - u z <= dist x z := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul x z
  have hright : u z - u y <= dist z y := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul z y
  have hdist := dist_add_dist_of_mem_segment hz
  change dist x y = u x - u y at hxy
  constructor
  · change dist x z = u x - u z
    linarith
  · change dist z y = u z - u y
    linarith

end ConcaveOTLimit
