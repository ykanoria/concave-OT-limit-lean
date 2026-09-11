import Theorems.Thm_ConcaveOTLimit_finiteCouplingIsCompact
import Theorems.Thm_ConcaveOTLimit_isClosedForwardPlanSet

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    (mu nu : FiniteMeasure Real) :
    IsCompact {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} := by
  simpa only [univ_inter] using
    (finiteCouplingIsCompact mu nu).inter_right isClosedForwardPlanSet
