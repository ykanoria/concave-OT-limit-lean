import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A graph plan supported on the canonical Juillet routes follows those
routes at almost every source point. -/
theorem canonicalRouteGraphSourceAe
    {mu nu : FiniteMeasure Real}
    (gammaEC : FiniteCoupling mu nu)
    {T : Real -> Real}
    (hGraph : IsGraphPlan gammaEC T)
    (hSupport :
      IsSupported gammaEC (juilletCanonicalRouteSet mu nu)) :
    ∀ᵐ x ∂(mu : Measure Real),
      (x, T x) ∈ juilletCanonicalRouteSet mu nu := by
  obtain ⟨hT, hPlan⟩ := hGraph
  have hPair : Measurable (fun x : Real => (x, T x)) :=
    measurable_id.prodMk hT
  change
    ∀ᵐ z ∂(gammaEC.plan : Measure (Real × Real)),
      z ∈ juilletCanonicalRouteSet mu nu at hSupport
  rw [hPlan] at hSupport
  apply ae_of_ae_map hPair.aemeasurable
  simpa [finiteGraphPlan] using hSupport

end ConcaveOTLimit
