import Definitions.Def_ConcaveOTLimitModel

open scoped BigOperators

namespace ConcaveOTLimit

/-- The distance contact set of a 1-Lipschitz potential is cyclically
monotone for the distance cost. -/
theorem distanceContactSetCyclicallyMonotone
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) (hu : LipschitzWith 1 u) :
    IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  classical
  have hdiff (x y : E) : u x - u y <= dist x y := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul x y
  intro I _ x y hcontact sigma
  calc
    (∑ i, dist (x i) (y i)) =
        ∑ i, (u (x i) - u (y i)) := by
      apply Fintype.sum_congr
      intro i
      exact hcontact i
    _ = (∑ i, u (x i)) - ∑ i, u (y i) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, u (x i)) - ∑ i, u (y (sigma i)) := by
      congr 1
      exact (Equiv.sum_comp sigma fun i => u (y i)).symm
    _ = ∑ i, (u (x i) - u (y (sigma i))) := by
      rw [Finset.sum_sub_distrib]
    _ <= ∑ i, dist (x i) (y (sigma i)) := by
      exact Finset.sum_le_sum fun i _ => hdiff (x i) (y (sigma i))

end ConcaveOTLimit
