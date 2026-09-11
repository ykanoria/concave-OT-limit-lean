import Theorems.Thm_ConcaveOTLimit_finiteCouplingIsCompact
import Theorems.Thm_ConcaveOTLimit_isEquicoerciveOfCompactSpace

open MeasureTheory

namespace ConcaveOTLimit

/-- Every functional family on a fixed-marginal coupling space over a Polish
Borel space is equicoercive. -/
theorem finiteCouplingFunctionalsEquicoercive
    {I E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [BorelSpace E] [PolishSpace E]
    {mu nu : FiniteMeasure E}
    (functional : I -> FiniteCoupling mu nu -> EReal) :
    IsEquicoercive functional := by
  letI : CompactSpace (FiniteCoupling mu nu) :=
    isCompact_univ_iff.mp (finiteCouplingIsCompact mu nu)
  exact isEquicoerciveOfCompactSpace functional

end ConcaveOTLimit
