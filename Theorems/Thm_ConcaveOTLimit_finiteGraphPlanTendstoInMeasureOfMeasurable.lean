import Theorems.Thm_ConcaveOTLimit_finiteGraphPlanTendstoInMeasure
import Theorems.Thm_ConcaveOTLimit_finiteMeasureHasLusinApproximation

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Weak convergence of finite graph plans of measurable maps implies
convergence in measure, with the Lusin hypothesis discharged automatically. -/
theorem finiteGraphPlanTendstoInMeasureOfMeasurable
    {X Y I : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {L : Filter I} (mu : FiniteMeasure X)
    (S : I -> X -> Y) (T : X -> Y)
    (hS : forall i, Measurable (S i)) (hT : Measurable T)
    (hgraph :
      Tendsto (fun i => finiteGraphPlan mu (S i) (hS i)) L
        (nhds (finiteGraphPlan mu T hT))) :
    TendstoInMeasure (mu : Measure X) S L T := by
  exact finiteGraphPlanTendstoInMeasure mu S T hS hT
    (finiteMeasureHasLusinApproximation mu hT) hgraph

end ConcaveOTLimit
