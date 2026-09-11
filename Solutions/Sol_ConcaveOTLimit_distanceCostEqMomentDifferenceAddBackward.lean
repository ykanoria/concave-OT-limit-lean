import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic.Ring

open MeasureTheory

open ConcaveOTLimit

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

private theorem integralCompMeasurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {m : Measure A} {n : Measure B} {f : A -> B}
    (hf : MeasurePreserving f m n) {g : B -> Real}
    (hg : AEStronglyMeasurable g n) :
    (∫ x, g (f x) ∂m) = ∫ y, g y ∂n := by
  calc
    (∫ x, g (f x) ∂m) = ∫ y, g y ∂Measure.map f m :=
      (integral_map hf.measurable.aemeasurable (hf.map_eq ▸ hg)).symm
    _ = ∫ y, g y ∂n := by rw [hf.map_eq]

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

private theorem realNormSubEqSignedAddBackward (x y : Real) :
    ‖x - y‖ = (y - x) + 2 * max (x - y) 0 := by
  rw [Real.norm_eq_abs]
  by_cases hxy : x <= y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      max_eq_right (sub_nonpos.mpr hxy)]
    ring
  · have hyx : y <= x := (le_of_not_ge hxy)
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      max_eq_left (sub_nonneg.mpr hyx)]
    ring

theorem solution
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real)) :
    distanceCost gamma =
      (integral (nu : Measure Real) fun y => y) -
        (integral (mu : Measure Real) fun x => x) +
      2 * integral (gamma.plan : Measure (Real × Real))
        (fun z => max (z.1 - z.2) 0) := by
  have hFst := integrableFst gamma hMu
  have hSnd := integrableSnd gamma hNu
  have hSigned :
      Integrable (fun z : Real × Real => z.2 - z.1)
        (gamma.plan : Measure (Real × Real)) :=
    hSnd.sub' hFst
  have hBackward :
      Integrable (fun z : Real × Real => max (z.1 - z.2) 0)
        (gamma.plan : Measure (Real × Real)) := by
    have hSub := hFst.sub' hSnd
    refine (hSub.sup (integrable_const 0)).congr (ae_of_all _ fun z => ?_)
    change (z.1 - z.2) ⊔ 0 = max (z.1 - z.2) 0
    apply le_antisymm
    · exact sup_le (le_max_left _ _) (le_max_right _ _)
    · exact max_le le_sup_left le_sup_right
  have hIntegralFst :
      (∫ z, z.1 ∂(gamma.plan : Measure (Real × Real))) =
        ∫ x, x ∂(mu : Measure Real) :=
    integralCompMeasurePreserving (measurePreservingFst gamma)
      hMu.aestronglyMeasurable
  have hIntegralSnd :
      (∫ z, z.2 ∂(gamma.plan : Measure (Real × Real))) =
        ∫ y, y ∂(nu : Measure Real) :=
    integralCompMeasurePreserving (measurePreservingSnd gamma)
      hNu.aestronglyMeasurable
  unfold distanceCost profileCost
  simp only [id_eq]
  calc
    (∫ z, ‖z.1 - z.2‖ ∂(gamma.plan : Measure (Real × Real))) =
        ∫ z, ((z.2 - z.1) + 2 * max (z.1 - z.2) 0)
          ∂(gamma.plan : Measure (Real × Real)) :=
      integral_congr_ae
        (ae_of_all _ fun z => realNormSubEqSignedAddBackward z.1 z.2)
    _ = (∫ z, z.2 - z.1 ∂(gamma.plan : Measure (Real × Real))) +
        ∫ z, 2 * max (z.1 - z.2) 0
          ∂(gamma.plan : Measure (Real × Real)) :=
      integral_add hSigned (hBackward.const_mul 2)
    _ = ((∫ z, z.2 ∂(gamma.plan : Measure (Real × Real))) -
          ∫ z, z.1 ∂(gamma.plan : Measure (Real × Real))) +
        2 * ∫ z, max (z.1 - z.2) 0
          ∂(gamma.plan : Measure (Real × Real)) := by
      rw [integral_sub hSnd hFst, integral_const_mul]
    _ = (∫ y, y ∂(nu : Measure Real)) -
          (∫ x, x ∂(mu : Measure Real)) +
        2 * ∫ z, max (z.1 - z.2) 0
          ∂(gamma.plan : Measure (Real × Real)) := by
      rw [hIntegralSnd, hIntegralFst]
