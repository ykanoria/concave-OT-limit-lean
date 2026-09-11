import Definitions.Def_ConcaveOTLimitModel

open Set

open ConcaveOTLimit

theorem solution
    {I X : Type*} [TopologicalSpace X] [CompactSpace X]
    (functional : I -> X -> EReal) :
    IsEquicoercive functional := by
  intro r
  exact ⟨univ, isCompact_univ, fun _ _ _ => mem_univ _⟩
