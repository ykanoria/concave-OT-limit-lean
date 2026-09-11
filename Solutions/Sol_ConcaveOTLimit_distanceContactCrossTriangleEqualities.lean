import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.Linarith

open ConcaveOTLimit

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {x y x' y' z : E}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hxy' : (x', y') ∈ distanceContactSet u)
    (hzxy : z ∈ segment Real x y)
    (hzxy' : z ∈ segment Real x' y') :
    dist x z + dist z y' = dist x y' /\
      dist x' z + dist z y = dist x' y := by
  have hcrossLeft : u x - u y' <= dist x y' := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul x y'
  have hcrossRight : u x' - u y <= dist x' y := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul x' y
  change dist x y = u x - u y at hxy
  change dist x' y' = u x' - u y' at hxy'
  have hcycle :
      dist x y + dist x' y' <= dist x y' + dist x' y := by
    linarith
  have hseg : dist x z + dist z y = dist x y :=
    dist_add_dist_of_mem_segment hzxy
  have hseg' : dist x' z + dist z y' = dist x' y' :=
    dist_add_dist_of_mem_segment hzxy'
  have htri : dist x y' <= dist x z + dist z y' :=
    dist_triangle x z y'
  have htri' : dist x' y <= dist x' z + dist z y :=
    dist_triangle x' z y
  have hcrossSum :
      dist x y' + dist x' y =
        (dist x z + dist z y') + (dist x' z + dist z y) := by
    linarith
  constructor <;> linarith
