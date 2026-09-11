import Theorems.Thm_ConcaveOTLimit_distanceContactReroutingOfCostTie
import Theorems.Thm_ConcaveOTLimit_distanceContactTwoCycle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace ConcaveOTLimit

/-- Two forward pairs satisfy the primary distance swap inequality, and a
primary-cost tie forces both crossed pairs to remain forward. -/
theorem forwardPairsDistanceTwoCycleAndReroutingOfTie
    {x y x' y' : Real} (hxy : x <= y) (hx'y' : x' <= y') :
    (dist x y + dist x' y' <= dist x y' + dist x' y) /\
      (dist x y + dist x' y' = dist x y' + dist x' y ->
        x <= y' /\ x' <= y) := by
  let u : Real -> Real := fun t => -t
  have hu : LipschitzWith 1 u := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp [u]
  have forwardPairContact {a b : Real} (hab : a <= b) :
      (a, b) ∈ distanceContactSet u := by
    change dist a b = -a - -b
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  have contactPairForward {a b : Real}
      (hab : (a, b) ∈ distanceContactSet u) : a <= b := by
    change dist a b = -a - -b at hab
    have hdist : 0 <= dist a b := dist_nonneg
    linarith
  have hxyContact : (x, y) ∈ distanceContactSet u :=
    forwardPairContact hxy
  have hx'y'Contact : (x', y') ∈ distanceContactSet u :=
    forwardPairContact hx'y'
  refine
    ⟨distanceContactTwoCycle u hu hxyContact hx'y'Contact, ?_⟩
  intro hTie
  let source : Bool -> Real := fun
    | false => x
    | true => x'
  let target : Bool -> Real := fun
    | false => y
    | true => y'
  let sigma : Equiv.Perm Bool := Equiv.swap false true
  have hContact :
      ∀ i, (source i, target i) ∈ distanceContactSet u := by
    intro i
    cases i
    · simpa [source, target] using hxyContact
    · simpa [source, target] using hx'y'Contact
  have hFiniteTie :
      (∑ i, dist (source i) (target i)) =
        ∑ i, dist (source i) (target (sigma i)) := by
    simpa [source, target, sigma, Fintype.sum_bool, add_comm] using hTie
  have hRerouted :=
    distanceContactReroutingOfCostTie
      u hu source target hContact sigma hFiniteTie
  have hxy'Contact : (x, y') ∈ distanceContactSet u := by
    simpa [source, target, sigma] using hRerouted false
  have hx'yContact : (x', y) ∈ distanceContactSet u := by
    simpa [source, target, sigma] using hRerouted true
  exact
    ⟨contactPairForward hxy'Contact,
      contactPairForward hx'yContact⟩

end ConcaveOTLimit
