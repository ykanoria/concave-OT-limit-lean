import Mathlib.Data.ENNReal.BigOperators

open scoped BigOperators

namespace ConcaveOTLimit

/-- A set is cyclically monotone for an `ENNReal`-valued cost when every
finite permutation of the target family weakly increases the total cost. -/
def IsCostCyclicallyMonotone {X Y : Type*}
    (cost : X -> Y -> ENNReal) (S : Set (X × Y)) : Prop :=
  ∀ {n : Nat} (x : Fin n -> X) (y : Fin n -> Y),
    (∀ i, (x i, y i) ∈ S) ->
      ∀ sigma : Equiv.Perm (Fin n),
        (∑ i, cost (x i) (y i)) <=
          ∑ i, cost (x i) (y (sigma i))

end ConcaveOTLimit
