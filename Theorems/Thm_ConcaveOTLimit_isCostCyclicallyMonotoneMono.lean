import Definitions.Def_CostCyclicMonotonicity

namespace ConcaveOTLimit

/-- Cost cyclic monotonicity is inherited by subsets. -/
theorem isCostCyclicallyMonotoneMono
    {X Y : Type*} {cost : X -> Y -> ENNReal}
    {S T : Set (X × Y)}
    (hST : S ⊆ T)
    (hT : IsCostCyclicallyMonotone cost T) :
    IsCostCyclicallyMonotone cost S := by
  intro n x y hxy sigma
  exact hT x y (fun i => hST (hxy i)) sigma

end ConcaveOTLimit
