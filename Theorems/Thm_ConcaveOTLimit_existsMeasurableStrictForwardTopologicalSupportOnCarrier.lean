import Theorems.Thm_ConcaveOTLimit_existsMeasurableStrictForwardTopologicalSupport
import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A forward coupling whose marginals are carried by complementary measurable
sets has a measurable full-mass, strictly forward topological support on that
product carrier. -/
theorem existsMeasurableStrictForwardTopologicalSupportOnCarrier
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {A : Set Real}
    (hA : MeasurableSet A)
    (hMu : (mu : Measure Real) Aᶜ = 0)
    (hNu : (nu : Measure Real) A = 0)
    (hForward : IsForwardPlan gamma) :
    exists S : Set (Real × Real),
      MeasurableSet S /\
      IsSupported gamma S /\
      (forall {x y : Real}, (x, y) ∈ S -> x < y) /\
      S ⊆ Measure.support
        (gamma.plan : Measure (Real × Real)) ∩ (A ×ˢ Aᶜ) := by
  have hSingular : FiniteMutuallySingular mu nu :=
    ⟨A, hA, hMu, hNu⟩
  obtain ⟨T, hTMeasurable, hTFull, hTStrict, hTSupport⟩ :=
    existsMeasurableStrictForwardTopologicalSupport hSingular hForward
  have hMuCarrier :
      ∀ᵐ x ∂(mu : Measure Real), x ∈ A := by
    apply ae_iff.mpr
    change (mu : Measure Real) Aᶜ = 0
    exact hMu
  have hNuCarrier :
      ∀ᵐ y ∂(nu : Measure Real), y ∈ Aᶜ := by
    apply ae_iff.mpr
    change (nu : Measure Real) (Aᶜ)ᶜ = 0
    simpa only [compl_compl] using hNu
  obtain ⟨hSourceCarrier, hTargetCarrier⟩ :=
    finiteCouplingMarginalAeTransfer gamma hMuCarrier hNuCarrier
  let S : Set (Real × Real) := T ∩ (A ×ˢ Aᶜ)
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact hTMeasurable.inter (hA.prod hA.compl)
  · filter_upwards [hTFull, hSourceCarrier, hTargetCarrier] with z
      hzT hzSource hzTarget
    exact ⟨hzT, hzSource, hzTarget⟩
  · intro x y hxy
    exact hTStrict hxy.1
  · intro z hz
    exact ⟨hTSupport hz.1, hz.2⟩

end ConcaveOTLimit
