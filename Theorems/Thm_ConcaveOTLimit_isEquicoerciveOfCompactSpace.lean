import Definitions.Def_ConcaveOTLimitModel

open Set

namespace ConcaveOTLimit

/-- Every family of extended-real functionals on a compact space is
equicoercive. -/
theorem isEquicoerciveOfCompactSpace
    {I X : Type*} [TopologicalSpace X] [CompactSpace X]
    (functional : I -> X -> EReal) :
    IsEquicoercive functional := by
  intro r
  exact ⟨univ, isCompact_univ, fun _ _ _ => mem_univ _⟩

end ConcaveOTLimit
