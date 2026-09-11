import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory

namespace ConcaveOTLimit

/-- Two maps inducing the same finite graph coupling agree source-almost
everywhere. -/
theorem isGraphPlan_map_unique_ae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableEq Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    {gamma : FiniteCoupling mu nu} {T S : X -> Y}
    (hTGraph : IsGraphPlan gamma T)
    (hSGraph : IsGraphPlan gamma S) :
    S =ᵐ[(mu : Measure X)] T := by
  obtain ⟨hT, hPlanT⟩ := hTGraph
  obtain ⟨hS, hPlanS⟩ := hSGraph
  have hMap :
      Measure.map (fun x => (x, T x)) (mu : Measure X) =
        Measure.map (fun x => (x, S x)) (mu : Measure X) := by
    simpa [finiteGraphPlan] using congrArg
      (fun rho : FiniteMeasure (X × Y) => (rho : Measure (X × Y)))
      (hPlanT.symm.trans hPlanS)
  have hOnT :
      ∀ᵐ z ∂Measure.map (fun x => (x, T x)) (mu : Measure X),
        z.2 = T z.1 := by
    apply (ae_map_iff (measurable_id.prodMk hT).aemeasurable
      (measurableSet_eq_fun measurable_snd
        (hT.comp measurable_fst))).2
    exact Filter.Eventually.of_forall fun _ => rfl
  rw [hMap] at hOnT
  exact ae_of_ae_map (measurable_id.prodMk hS).aemeasurable hOnT

end ConcaveOTLimit
