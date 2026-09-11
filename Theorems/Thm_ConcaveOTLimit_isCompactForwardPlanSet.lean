import Theorems.Thm_ConcaveOTLimit_finiteCouplingIsCompact
import Theorems.Thm_ConcaveOTLimit_isClosedForwardPlanSet

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The forward couplings form a compact subset of the fixed-marginal
finite-coupling space. -/
theorem isCompactForwardPlanSet
    (mu nu : FiniteMeasure Real) :
    IsCompact {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} := by
  simpa only [univ_inter] using
    (finiteCouplingIsCompact mu nu).inter_right isClosedForwardPlanSet

end ConcaveOTLimit
