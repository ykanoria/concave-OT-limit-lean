import Theorems.Thm_ConcaveOTLimit_existsMeasurableStrictForwardTopologicalSupport
import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
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
  obtain ⟨base, hBaseMeasurable, hBaseFull, hBaseStrict, hBaseSupport⟩ :=
    existsMeasurableStrictForwardTopologicalSupport
      (show FiniteMutuallySingular mu nu from
        ⟨A, hA, hMu, hNu⟩)
      hForward
  have hSource : ∀ᵐ x ∂(mu : Measure Real), x ∈ A := by
    rw [ae_iff]
    exact hMu
  have hTarget : ∀ᵐ y ∂(nu : Measure Real), y ∈ Aᶜ := by
    apply ae_iff.mpr
    have hBad : {y : Real | ¬y ∈ Aᶜ} = A := by
      ext y
      simp only [mem_setOf_eq, mem_compl_iff, not_not]
    rw [hBad]
    exact hNu
  have hPlanCarrier :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        z ∈ A ×ˢ Aᶜ := by
    obtain ⟨hFst, hSnd⟩ :=
      finiteCouplingMarginalAeTransfer gamma hSource hTarget
    filter_upwards [hFst, hSnd] with z hzFst hzSnd
    exact ⟨hzFst, hzSnd⟩
  refine ⟨base ∩ (A ×ˢ Aᶜ), ?_, ?_, ?_, ?_⟩
  · exact hBaseMeasurable.inter (hA.prod hA.compl)
  · filter_upwards [hBaseFull, hPlanCarrier] with z hzBase hzCarrier
    exact ⟨hzBase, hzCarrier⟩
  · intro x y hxy
    exact hBaseStrict hxy.1
  · rintro z ⟨hzBase, hzCarrier⟩
    exact ⟨hBaseSupport hzBase, hzCarrier⟩
