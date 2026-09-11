import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    {p : X -> Prop} {q : Y -> Prop}
    (hp : ∀ᵐ x ∂(mu : Measure X), p x)
    (hq : ∀ᵐ y ∂(nu : Measure Y), q y) :
    (∀ᵐ z ∂(gamma.plan : Measure (X × Y)), p z.1) ∧
      (∀ᵐ z ∂(gamma.plan : Measure (X × Y)), q z.2) := by
  have hSourceProjection :
      MeasurePreserving (Prod.fst : X × Y -> X)
        (gamma.plan : Measure (X × Y)) (mu : Measure X) := by
    refine ⟨measurable_fst, ?_⟩
    simpa [firstMarginal] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X)) gamma.property.1
  have hTargetProjection :
      MeasurePreserving (Prod.snd : X × Y -> Y)
        (gamma.plan : Measure (X × Y)) (nu : Measure Y) := by
    refine ⟨measurable_snd, ?_⟩
    simpa [secondMarginal] using congrArg
      (fun rho : FiniteMeasure Y => (rho : Measure Y)) gamma.property.2
  constructor
  · exact hSourceProjection.quasiMeasurePreserving.ae hp
  · exact hTargetProjection.quasiMeasurePreserving.ae hq
