import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Two couplings carried by a common support with injective first projection
coincide when one of them is a graph plan. -/
theorem finiteCouplingEqOfGraphOfCommonInjectiveSupport
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    {gamma eta : FiniteCoupling mu nu}
    {Gamma : Set (X × Y)} {T : X -> Y}
    (hGamma : Set.InjOn Prod.fst Gamma)
    (hgamma : IsSupported gamma Gamma)
    (heta : IsSupported eta Gamma)
    (hgraph : IsGraphPlan gamma T) :
    gamma = eta := by
  obtain ⟨hT, hgraph⟩ := hgraph
  have hPair : Measurable (fun x : X => (x, T x)) :=
    measurable_id.prodMk hT
  have hGraphMemMu :
      ∀ᵐ x ∂(mu : Measure X), (x, T x) ∈ Gamma := by
    change ∀ᵐ z ∂(gamma.plan : Measure (X × Y)), z ∈ Gamma at hgamma
    rw [hgraph] at hgamma
    apply ae_of_ae_map hPair.aemeasurable
    simpa [finiteGraphPlan] using hgamma
  have hEtaFirst :
      Measure.map Prod.fst (eta.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X)) eta.property.1
  have hGraphMemEta :
      ∀ᵐ z ∂(eta.plan : Measure (X × Y)),
        (z.1, T z.1) ∈ Gamma := by
    have hGraphMemMap :
        ∀ᵐ x ∂Measure.map Prod.fst
          (eta.plan : Measure (X × Y)), (x, T x) ∈ Gamma := by
      rw [hEtaFirst]
      exact hGraphMemMu
    simpa only using
      (ae_of_ae_map measurable_fst.aemeasurable hGraphMemMap)
  have hGraphId :
      (fun z : X × Y => (z.1, T z.1)) =ᵐ[
        (eta.plan : Measure (X × Y))] id := by
    filter_upwards [heta, hGraphMemEta] with z hz hTz
    exact hGamma hTz hz rfl
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  change (gamma.plan : Measure (X × Y)) =
    (eta.plan : Measure (X × Y))
  rw [hgraph]
  simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
  calc
    Measure.map (fun x : X => (x, T x)) (mu : Measure X) =
        Measure.map (fun x : X => (x, T x))
          (Measure.map Prod.fst (eta.plan : Measure (X × Y))) := by
      rw [hEtaFirst]
    _ = Measure.map
          ((fun x : X => (x, T x)) ∘ Prod.fst)
          (eta.plan : Measure (X × Y)) :=
      Measure.map_map hPair measurable_fst
    _ = Measure.map id (eta.plan : Measure (X × Y)) := by
      apply Measure.map_congr
      simpa [Function.comp_def] using hGraphId
    _ = (eta.plan : Measure (X × Y)) := Measure.map_id

end ConcaveOTLimit
