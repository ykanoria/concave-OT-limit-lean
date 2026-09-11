import Definitions.Def_ConcaveOTLimitModel

open scoped BigOperators

namespace ConcaveOTLimit

/-- If a permutation of contact pairs ties the total distance cost, then all
rerouted pairs remain in the distance contact set. -/
theorem distanceContactReroutingOfCostTie
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {I : Type*} [Fintype I] (x y : I -> E)
    (hContact : ∀ i, (x i, y i) ∈ distanceContactSet u)
    (sigma : Equiv.Perm I)
    (hTie :
      (∑ i, dist (x i) (y i)) =
        ∑ i, dist (x i) (y (sigma i))) :
    ∀ i, (x i, y (sigma i)) ∈ distanceContactSet u := by
  classical
  have hpotentialSum :
      (∑ i, (u (x i) - u (y (sigma i)))) =
        ∑ i, dist (x i) (y (sigma i)) := by
    calc
      (∑ i, (u (x i) - u (y (sigma i)))) =
          (∑ i, u (x i)) - ∑ i, u (y (sigma i)) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i, u (x i)) - ∑ i, u (y i) := by
        congr 1
        exact Equiv.sum_comp sigma (fun i => u (y i))
      _ = ∑ i, (u (x i) - u (y i)) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i, dist (x i) (y i) := by
        apply Fintype.sum_congr
        intro i
        exact (hContact i).symm
      _ = ∑ i, dist (x i) (y (sigma i)) := hTie
  intro i
  have hle (j : I) :
      u (x j) - u (y (sigma j)) <= dist (x j) (y (sigma j)) := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul (x j) (y (sigma j))
  change dist (x i) (y (sigma i)) =
    u (x i) - u (y (sigma i))
  apply le_antisymm
  · by_contra hnot
    have hstrict :
        u (x i) - u (y (sigma i)) <
          dist (x i) (y (sigma i)) :=
      lt_of_not_ge hnot
    have hsumLt :
        (∑ j, (u (x j) - u (y (sigma j)))) <
          ∑ j, dist (x j) (y (sigma j)) := by
      exact Finset.sum_lt_sum
        (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
    exact (ne_of_lt hsumLt) hpotentialSum
  · exact hle i

end ConcaveOTLimit
