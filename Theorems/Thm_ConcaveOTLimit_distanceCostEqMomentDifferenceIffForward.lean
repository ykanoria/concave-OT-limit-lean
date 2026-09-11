import Theorems.Thm_ConcaveOTLimit_distanceCostEqMomentDifferenceAddBackward
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.1

private theorem measurePreservingSnd
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (Real × Real)) (nu : Measure Real) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.2

private theorem integrableFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real)) :
    Integrable (fun z : Real × Real => z.1)
      (gamma.plan : Measure (Real × Real)) := by
  simpa [Function.comp_def] using
    (measurePreservingFst gamma).integrable_comp_of_integrable hMu

private theorem integrableSnd
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu)
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real)) :
    Integrable (fun z : Real × Real => z.2)
      (gamma.plan : Measure (Real × Real)) := by
  simpa [Function.comp_def] using
    (measurePreservingSnd gamma).integrable_comp_of_integrable hNu

/-- A real-line coupling attains the marginal first-moment lower bound exactly
when it moves mass forward almost everywhere. -/
theorem distanceCostEqMomentDifferenceIffForward
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real)) :
    distanceCost gamma =
        (integral (nu : Measure Real) fun y => y) -
          (integral (mu : Measure Real) fun x => x) <->
      IsForwardPlan gamma := by
  let backward : Real × Real -> Real :=
    fun z => max (z.1 - z.2) 0
  have hSub :
      Integrable (fun z : Real × Real => z.1 - z.2)
        (gamma.plan : Measure (Real × Real)) :=
    (integrableFst gamma hMu).sub' (integrableSnd gamma hNu)
  have hBackward :
      Integrable backward (gamma.plan : Measure (Real × Real)) := by
    refine (hSub.sup (integrable_const 0)).congr (ae_of_all _ fun z => ?_)
    change (z.1 - z.2) ⊔ 0 = max (z.1 - z.2) 0
    apply le_antisymm
    · exact sup_le (le_max_left _ _) (le_max_right _ _)
    · exact max_le le_sup_left le_sup_right
  have hNonnegative :
      0 ≤ᵐ[(gamma.plan : Measure (Real × Real))] backward :=
    ae_of_all _ fun z => le_max_right _ _
  rw [distanceCostEqMomentDifferenceAddBackward gamma hMu hNu]
  constructor
  · intro hEquality
    have hIntegralZero :
        ∫ z, backward z ∂(gamma.plan : Measure (Real × Real)) = 0 := by
      change
        ∫ z, max (z.1 - z.2) 0
          ∂(gamma.plan : Measure (Real × Real)) = 0
      linarith
    have hZero :
        backward =ᵐ[(gamma.plan : Measure (Real × Real))] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hNonnegative hBackward).mp
        hIntegralZero
    filter_upwards [hZero] with z hz
    have hLe : z.1 - z.2 <= 0 := by
      calc
        z.1 - z.2 <= backward z := le_max_left _ _
        _ = 0 := hz
    exact sub_nonpos.mp hLe
  · intro hForward
    have hZero :
        backward =ᵐ[(gamma.plan : Measure (Real × Real))] 0 := by
      filter_upwards [hForward] with z hz
      exact max_eq_right (sub_nonpos.mpr hz)
    have hIntegralZero :
        ∫ z, backward z ∂(gamma.plan : Measure (Real × Real)) = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hNonnegative hBackward).mpr hZero
    change
      (integral (nu : Measure Real) fun y => y) -
          (integral (mu : Measure Real) fun x => x) +
          2 * integral (gamma.plan : Measure (Real × Real))
            (fun z => max (z.1 - z.2) 0) =
        (integral (nu : Measure Real) fun y => y) -
          (integral (mu : Measure Real) fun x => x)
    change
      (integral (nu : Measure Real) fun y => y) -
          (integral (mu : Measure Real) fun x => x) +
          2 * integral (gamma.plan : Measure (Real × Real)) backward =
        (integral (nu : Measure Real) fun y => y) -
          (integral (mu : Measure Real) fun x => x)
    rw [hIntegralZero]
    ring

end ConcaveOTLimit
