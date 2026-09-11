import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {X : Type*} [MeasurableSpace X]
    {mu nu : FiniteMeasure X}
    (gamma : FiniteCoupling mu nu)
    (hSingular : FiniteMutuallySingular mu nu) :
    ∀ᵐ z ∂(gamma.plan : Measure (X × X)), z.1 ≠ z.2 := by
  obtain ⟨s, _hs, hMu, hNu⟩ := hSingular
  have hSourceMarginal :
      ∀ᵐ x ∂(mu : Measure X), x ∈ s := by
    apply ae_iff.mpr
    change (mu : Measure X) sᶜ = 0
    exact hMu
  have hTargetMarginal :
      ∀ᵐ y ∂(nu : Measure X), y ∉ s := by
    apply ae_iff.mpr
    have hSet : {y : X | ¬y ∉ s} = s := by
      ext y
      simp only [mem_setOf_eq, not_not]
    rw [hSet]
    exact hNu
  obtain ⟨hSource, hTarget⟩ :=
    finiteCouplingMarginalAeTransfer gamma
      hSourceMarginal hTargetMarginal
  filter_upwards [hSource, hTarget] with z hzSource hzTarget
  intro hEq
  exact hzTarget (hEq ▸ hzSource)
