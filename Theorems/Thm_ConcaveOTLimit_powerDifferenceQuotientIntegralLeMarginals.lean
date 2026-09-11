import Theorems.Thm_ConcaveOTLimit_PsiNormSubBound
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientOrliczBound
import Theorems.Thm_ConcaveOTLimit_powerQuotientCostIntegrableOfMarginalLogMoments

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem measurePreservingFst
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (E × E)) (mu : Measure E) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.1

private theorem measurePreservingSnd
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (E × E)) (nu : Measure E) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.2

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

private theorem measurablePsi : Measurable Psi := by
  exact measurable_id.mul
    (Real.measurable_log.comp (measurable_const.add measurable_id))

private theorem psiNonnegative {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem psiMonotone {a b : Real} (ha : 0 <= a) (hab : a <= b) :
    Psi a <= Psi b := by
  have hb : 0 <= b := ha.trans hab
  have hLogNonnegative : 0 <= Real.log (1 + a) :=
    Real.log_nonneg (by linarith)
  have hLogLe : Real.log (1 + a) <= Real.log (1 + b) :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul hab hLogLe hLogNonnegative hb

private theorem psiNormSubLeTwoMarginals
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    Psi ‖x - y‖ <= Psi (2 * ‖x‖) + Psi (2 * ‖y‖) := by
  calc
    Psi ‖x - y‖ <= Psi (‖x‖ + ‖y‖) :=
      psiMonotone (norm_nonneg _) (norm_sub_le x y)
    _ <= Psi (2 * ‖x‖) + Psi (2 * ‖y‖) := by
      rcases le_total ‖x‖ ‖y‖ with hxy | hyx
      · have hSum : ‖x‖ + ‖y‖ <= 2 * ‖y‖ := by linarith
        exact
          (psiMonotone
            (add_nonneg (norm_nonneg _) (norm_nonneg _)) hSum).trans
            (le_add_of_nonneg_left
              (psiNonnegative
                (mul_nonneg (by norm_num) (norm_nonneg x))))
      · have hSum : ‖x‖ + ‖y‖ <= 2 * ‖x‖ := by linarith
        exact
          (psiMonotone
            (add_nonneg (norm_nonneg _) (norm_nonneg _)) hSum).trans
            (le_add_of_nonneg_right
              (psiNonnegative
                (mul_nonneg (by norm_num) (norm_nonneg y))))

private theorem integrablePsiTwoNorm
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E] {m : Measure E} [IsFiniteMeasure m]
    (h : Integrable (fun x : E => Psi ‖x‖) m) :
    Integrable (fun x : E => Psi (2 * ‖x‖)) m := by
  have hBound : Integrable
      (fun x : E => 4 * (1 + Psi ‖x‖ + Psi ‖x‖)) m :=
    (((integrable_const 1).add h).add h).const_mul 4
  refine hBound.mono'
    (measurablePsi.comp
      (measurable_const.mul continuous_norm.measurable)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (psiNonnegative (mul_nonneg (by norm_num) (norm_nonneg x)))]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
    abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg x)),
    two_mul] using
    (PsiNormSubBound (‖x‖ : Real) (-‖x‖))

/-- The integrated power difference quotient has a coupling-independent
bound determined explicitly by the two marginal logarithmic moments. -/
theorem powerDifferenceQuotientIntegralLeMarginals
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) {epsilon : Real}
    (hEpsilonPos : 0 < epsilon)
    (hEpsilonLeHalf : epsilon <= 1 / 2) :
    abs
      (integral (gamma.plan : Measure (E × E))
        (fun z =>
          (powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) / epsilon) :
        Real) <=
      2 * (mu : Measure E).real univ +
        (integral (mu : Measure E) (fun x => Psi (2 * ‖x‖)) : Real) +
        (integral (nu : Measure E) (fun y => Psi (2 * ‖y‖)) : Real) := by
  have hMuTwo := integrablePsiTwoNorm hMu
  have hNuTwo := integrablePsiTwoNorm hNu
  have hQuotient :=
    powerQuotientCostIntegrableOfMarginalLogMoments
      hMu hNu gamma hEpsilonPos hEpsilonLeHalf
  have hFirst : Integrable (fun z : E × E => Psi (2 * ‖z.1‖))
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingFst gamma).integrable_comp_of_integrable hMuTwo
  have hSecond : Integrable (fun z : E × E => Psi (2 * ‖z.2‖))
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingSnd gamma).integrable_comp_of_integrable hNuTwo
  have hPsiDifference : Integrable
      (fun z : E × E => Psi ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
    refine (hFirst.add hSecond).mono'
      (measurablePsi.comp
        ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (psiNonnegative (norm_nonneg _))]
    simpa only [Pi.add_apply] using
      psiNormSubLeTwoMarginals z.1 z.2
  have hPsiBound :
      (∫ z, Psi ‖z.1 - z.2‖ ∂(gamma.plan : Measure (E × E))) <=
        (∫ x, Psi (2 * ‖x‖) ∂(mu : Measure E)) +
          ∫ y, Psi (2 * ‖y‖) ∂(nu : Measure E) := by
    calc
      (∫ z, Psi ‖z.1 - z.2‖ ∂(gamma.plan : Measure (E × E))) <=
          ∫ z, Psi (2 * ‖z.1‖) + Psi (2 * ‖z.2‖)
            ∂(gamma.plan : Measure (E × E)) :=
        integral_mono hPsiDifference (hFirst.add hSecond)
          (fun z => psiNormSubLeTwoMarginals z.1 z.2)
      _ = (∫ z, Psi (2 * ‖z.1‖) ∂(gamma.plan : Measure (E × E))) +
            ∫ z, Psi (2 * ‖z.2‖) ∂(gamma.plan : Measure (E × E)) := by
        rw [integral_add hFirst hSecond]
      _ = _ := by
        rw [integralCompMeasurePreserving
              (measurePreservingFst gamma) hMuTwo.aestronglyMeasurable,
          integralCompMeasurePreserving
              (measurePreservingSnd gamma) hNuTwo.aestronglyMeasurable]
  have hDominating : Integrable
      (fun z : E × E => 2 + Psi ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) :=
    (integrable_const 2).add hPsiDifference
  have hMass :
      (gamma.plan : Measure (E × E)).real univ =
        (mu : Measure E).real univ := by
    rw [← (measurePreservingFst gamma).map_eq,
      map_measureReal_apply measurable_fst MeasurableSet.univ, preimage_univ]
  calc
    abs
        (∫ z,
          (powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) / epsilon
          ∂(gamma.plan : Measure (E × E))) <=
        ∫ z,
          abs
            ((powerProfile epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) /
              epsilon)
          ∂(gamma.plan : Measure (E × E)) :=
      abs_integral_le_integral_abs
    _ <= ∫ z, 2 + Psi ‖z.1 - z.2‖
          ∂(gamma.plan : Measure (E × E)) :=
      integral_mono hQuotient.abs hDominating fun z =>
        powerDifferenceQuotientOrliczBound
          hEpsilonPos hEpsilonLeHalf (norm_nonneg _)
    _ = 2 * (gamma.plan : Measure (E × E)).real univ +
          ∫ z, Psi ‖z.1 - z.2‖
            ∂(gamma.plan : Measure (E × E)) := by
      rw [integral_add (integrable_const 2) hPsiDifference, integral_const]
      ring
    _ <= _ := by
      rw [hMass]
      linarith

end ConcaveOTLimit
