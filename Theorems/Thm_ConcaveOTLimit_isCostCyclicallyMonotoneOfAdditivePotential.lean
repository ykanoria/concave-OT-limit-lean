import Definitions.Def_CostCyclicMonotonicity

open scoped BigOperators

namespace ConcaveOTLimit

/-- A set on which an admissible additive potential saturates the cost is
cost-cyclically monotone. -/
theorem isCostCyclicallyMonotoneOfAdditivePotential
    {X Y : Type*}
    (cost : X -> Y -> ENNReal) (S : Set (X × Y))
    (phi : X -> ENNReal) (psi : Y -> ENNReal)
    (hLower : ∀ x y, phi x + psi y <= cost x y)
    (hContact : ∀ ⦃x y⦄, (x, y) ∈ S ->
      cost x y = phi x + psi y) :
    IsCostCyclicallyMonotone cost S := by
  classical
  intro n x y hxy sigma
  calc
    (∑ i, cost (x i) (y i)) =
        ∑ i, (phi (x i) + psi (y i)) := by
      apply Fintype.sum_congr
      intro i
      exact hContact (hxy i)
    _ = (∑ i, phi (x i)) + ∑ i, psi (y i) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, phi (x i)) + ∑ i, psi (y (sigma i)) := by
      congr 1
      exact (Equiv.sum_comp sigma (fun i => psi (y i))).symm
    _ = ∑ i, (phi (x i) + psi (y (sigma i))) := by
      rw [Finset.sum_add_distrib]
    _ <= ∑ i, cost (x i) (y (sigma i)) := by
      exact Finset.sum_le_sum fun i _ => hLower (x i) (y (sigma i))

end ConcaveOTLimit
