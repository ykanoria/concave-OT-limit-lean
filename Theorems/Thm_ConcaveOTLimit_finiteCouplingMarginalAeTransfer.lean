import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open MeasureTheory

namespace ConcaveOTLimit

/-- Almost-everywhere properties of both marginals pull back to a finite
coupling plan along the corresponding coordinate projections. -/
theorem finiteCouplingMarginalAeTransfer
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    {p : X -> Prop} {q : Y -> Prop}
    (hp : ∀ᵐ x ∂(mu : Measure X), p x)
    (hq : ∀ᵐ y ∂(nu : Measure Y), q y) :
    (∀ᵐ z ∂(gamma.plan : Measure (X × Y)), p z.1) ∧
      (∀ᵐ z ∂(gamma.plan : Measure (X × Y)), q z.2) := by
  have hFst :
      MeasurePreserving (Prod.fst : X × Y -> X)
        (gamma.plan : Measure (X × Y)) (mu : Measure X) := by
    refine ⟨measurable_fst, ?_⟩
    simpa [firstMarginal] using congrArg
      (fun eta : FiniteMeasure X => (eta : Measure X)) gamma.property.1
  have hSnd :
      MeasurePreserving (Prod.snd : X × Y -> Y)
        (gamma.plan : Measure (X × Y)) (nu : Measure Y) := by
    refine ⟨measurable_snd, ?_⟩
    simpa [secondMarginal] using congrArg
      (fun eta : FiniteMeasure Y => (eta : Measure Y)) gamma.property.2
  exact ⟨hFst.quasiMeasurePreserving.ae hp,
    hSnd.quasiMeasurePreserving.ae hq⟩

end ConcaveOTLimit
