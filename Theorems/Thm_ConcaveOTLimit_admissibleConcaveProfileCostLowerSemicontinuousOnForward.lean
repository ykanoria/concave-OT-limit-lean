import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileHasNonnegativeLscDistanceShift
import Theorems.Thm_ConcaveOTLimit_fixedMassPlanNormalization
import Theorems.Thm_ConcaveOTLimit_forwardPlanAffineDistanceShiftIntegralEq
import Theorems.Thm_ConcaveOTLimit_probabilityLintegralLowerSemicontinuous

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- On real forward couplings, the cost of an admissible concave profile is
lower semicontinuous for the weak topology. -/
theorem admissibleConcaveProfileCostLowerSemicontinuousOnForward
    {mu nu : FiniteMeasure Real}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real)) :
    LowerSemicontinuousOn
      (profileCost profile)
      {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} := by
  let forwardSet : Set (FiniteCoupling mu nu) :=
    {gamma | IsForwardPlan gamma}
  by_cases hMassZero : mu.mass = 0
  · intro gamma _hGammaForward r hr
    filter_upwards [self_mem_nhdsWithin] with eta _hEtaForward
    have hGammaPlan :=
      (zeroMassFiniteCouplingPlan gamma hMassZero).2.2
    have hEtaPlan :=
      (zeroMassFiniteCouplingPlan eta hMassZero).2.2
    simpa [profileCost, hGammaPlan, hEtaPlan] using hr

  have hMassPositive : 0 < mu.mass :=
    pos_of_ne_zero hMassZero
  have hMuNorm :
      Integrable (fun x : Real => ‖x‖) (mu : Measure Real) := by
    simpa using hMu.norm
  have hNuNorm :
      Integrable (fun y : Real => ‖y‖) (nu : Measure Real) := by
    simpa using hNu.norm
  obtain ⟨C, _hC, hShiftNonnegative, hShiftLower⟩ :=
    admissibleConcaveProfileHasNonnegativeLscDistanceShift
      (E := Real) hProfile
  let shifted : Real × Real -> Real :=
    fun z => profile ‖z.1 - z.2‖ + C * (1 + ‖z.1 - z.2‖)

  have hShiftedNonnegative : 0 <= shifted := by
    intro z
    simpa [shifted] using hShiftNonnegative z.1 z.2
  have hShiftedLower : LowerSemicontinuous shifted := by
    simpa [shifted] using hShiftLower
  have hProfileIntegrable :
      forall eta : FiniteCoupling mu nu,
        Integrable (fun z : Real × Real => profile ‖z.1 - z.2‖)
          (eta.plan : Measure (Real × Real)) := by
    intro eta
    exact admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
      hProfile hMuNorm hNuNorm eta
  have hControlIntegrable :
      forall eta : FiniteCoupling mu nu,
        Integrable (fun z : Real × Real =>
          C * (1 + ‖z.1 - z.2‖))
          (eta.plan : Measure (Real × Real)) := by
    intro eta
    exact ((integrable_const 1).add
      (distanceIntegrableOfMarginalFirstMoments
        hMuNorm hNuNorm eta)).const_mul C
  have hShiftedIntegrable :
      forall eta : FiniteCoupling mu nu,
        Integrable shifted (eta.plan : Measure (Real × Real)) := by
    intro eta
    simpa [shifted] using
      (hProfileIntegrable eta).add (hControlIntegrable eta)

  intro gamma hGammaForward
  obtain ⟨_hCommonMass, hPlanMass, _hGammaMass, hPlanNormalize,
      _hGammaNormalize, hNormalizeTendsto⟩ :=
    fixedMassPlanNormalization
      (I := FiniteCoupling mu nu)
      (L := nhds gamma)
      (gammaNet := fun eta => eta)
      hMassPositive tendsto_id

  let normalizedIntegral : FiniteCoupling mu nu -> Real :=
    fun eta =>
      ∫ z, shifted z
        ∂(eta.plan.normalize : Measure (Real × Real))
  have hNormalizeIntegrable :
      forall eta : FiniteCoupling mu nu,
        Integrable shifted
          (eta.plan.normalize : Measure (Real × Real)) := by
    intro eta
    have hPlanNonzero : eta.plan ≠ 0 := by
      apply eta.plan.mass_nonzero_iff.mp
      rw [hPlanMass eta]
      exact ne_of_gt hMassPositive
    rw [eta.plan.toMeasure_normalize_eq_of_nonzero hPlanNonzero]
    exact (hShiftedIntegrable eta).smul_measure_nnreal

  have hProbabilityLower :
      LowerSemicontinuous
        (fun P : ProbabilityMeasure (Real × Real) =>
          ∫⁻ z, ENNReal.ofReal (shifted z)
            ∂(P : Measure (Real × Real))) :=
    probabilityLintegralLowerSemicontinuous
      hShiftedLower hShiftedNonnegative
  have hNormalizedLintegralLower :
      LowerSemicontinuousAt
        (fun eta : FiniteCoupling mu nu =>
          ∫⁻ z, ENNReal.ofReal (shifted z)
            ∂(eta.plan.normalize : Measure (Real × Real)))
        gamma := by
    have hNormalizeContinuous :
        ContinuousAt
          (fun eta : FiniteCoupling mu nu => eta.plan.normalize)
          gamma :=
      hNormalizeTendsto
    simpa [Function.comp_def] using
      LowerSemicontinuousAt.comp
        (g := fun eta : FiniteCoupling mu nu => eta.plan.normalize)
        (x := gamma)
        (hProbabilityLower gamma.plan.normalize) hNormalizeContinuous
  have hNormalizedIntegralLower :
      LowerSemicontinuousAt normalizedIntegral gamma := by
    intro r hr
    by_cases hrNegative : r < 0
    · exact Filter.Eventually.of_forall fun eta =>
        hrNegative.trans_le
          (integral_nonneg hShiftedNonnegative)
    · have hrNonnegative : 0 <= r := le_of_not_gt hrNegative
      have hENNRealStrict :
          ENNReal.ofReal r <
            ∫⁻ z, ENNReal.ofReal (shifted z)
              ∂(gamma.plan.normalize : Measure (Real × Real)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          (hNormalizeIntegrable gamma)
          (ae_of_all _ hShiftedNonnegative)]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrNonnegative).2 hr
      filter_upwards [hNormalizedLintegralLower
          (ENNReal.ofReal r) hENNRealStrict] with eta hEta
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hNormalizeIntegrable eta)
        (ae_of_all _ hShiftedNonnegative)] at hEta
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrNonnegative).1 hEta

  let K : Real :=
    ∫ z, C * (1 + ‖z.1 - z.2‖)
      ∂(gamma.plan : Measure (Real × Real))
  have hControlIntegral :
      forall (eta : FiniteCoupling mu nu), IsForwardPlan eta ->
        (∫ z, C * (1 + ‖z.1 - z.2‖)
            ∂(eta.plan : Measure (Real × Real))) = K := by
    intro eta hEtaForward
    exact forwardPlanAffineDistanceShiftIntegralEq
      hMu hNu eta gamma hEtaForward hGammaForward C
  have hShiftedIntegral :
      forall (eta : FiniteCoupling mu nu), IsForwardPlan eta ->
        (∫ z, shifted z ∂(eta.plan : Measure (Real × Real))) =
          profileCost profile eta + K := by
    intro eta hEtaForward
    calc
      (∫ z, shifted z ∂(eta.plan : Measure (Real × Real))) =
          (∫ z, profile ‖z.1 - z.2‖
            ∂(eta.plan : Measure (Real × Real))) +
          ∫ z, C * (1 + ‖z.1 - z.2‖)
            ∂(eta.plan : Measure (Real × Real)) :=
        integral_add (hProfileIntegrable eta) (hControlIntegrable eta)
      _ = profileCost profile eta + K := by
        rw [hControlIntegral eta hEtaForward]
        simp only [profileCost]
  have hNormalizeIntegral :
      forall eta : FiniteCoupling mu nu,
        (∫ z, shifted z ∂(eta.plan : Measure (Real × Real))) =
          (mu.mass : Real) * normalizedIntegral eta := by
    intro eta
    rw [hPlanNormalize eta]
    simp [normalizedIntegral, FiniteMeasure.toMeasure_smul, NNReal.smul_def]
  have hCostEq :
      forall (eta : FiniteCoupling mu nu), IsForwardPlan eta ->
        (mu.mass : Real) * normalizedIntegral eta - K =
          profileCost profile eta := by
    intro eta hEtaForward
    linarith [hNormalizeIntegral eta, hShiftedIntegral eta hEtaForward]

  have hAffineContinuous :
      ContinuousAt (fun x : Real => (mu.mass : Real) * x - K)
        (normalizedIntegral gamma) := by
    fun_prop
  have hAffineMonotone :
      Monotone (fun x : Real => (mu.mass : Real) * x - K) := by
    intro a b hab
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_left hab (NNReal.coe_nonneg mu.mass)) K
  have hAffineLower :
      LowerSemicontinuousAt
        (fun eta : FiniteCoupling mu nu =>
          (mu.mass : Real) * normalizedIntegral eta - K)
        gamma := by
    simpa [Function.comp_def] using
      hAffineContinuous.comp_lowerSemicontinuousAt
        hNormalizedIntegralLower hAffineMonotone
  exact
    (hAffineLower.lowerSemicontinuousWithinAt forwardSet).congr_of_eventuallyEq
      hGammaForward
      (by
        filter_upwards [self_mem_nhdsWithin] with eta hEtaForward
        exact hCostEq eta hEtaForward)

end ConcaveOTLimit
