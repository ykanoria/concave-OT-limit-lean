import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileHasNonnegativeLscDistanceShift
import Theorems.Thm_ConcaveOTLimit_distanceCostSequentiallyContinuousOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_fixedMassPlanNormalization
import Theorems.Thm_ConcaveOTLimit_probabilityLintegralLowerSemicontinuous
import Mathlib.Tactic.Linarith

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- An admissible concave profile cost is sequentially lower
semicontinuous on a positive-mass fixed-marginal coupling space when both
marginal norms are integrable. -/
theorem admissibleConcaveProfileCostSequentiallyLowerSemicontinuousOfMarginalFirstMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (hPositive : 0 < mu.mass)
    {gammaSeq : Nat -> FiniteCoupling mu nu}
    {gamma : FiniteCoupling mu nu}
    (hTendsto : Tendsto gammaSeq atTop (nhds gamma)) :
    ∀ r < profileCost profile gamma,
      ∀ᶠ k in atTop, r <= profileCost profile (gammaSeq k) := by
  obtain ⟨C, _hC, hShiftNonnegative, hShiftLower⟩ :=
    admissibleConcaveProfileHasNonnegativeLscDistanceShift
      (E := E) hProfile
  let D : E × E -> Real := fun z => ‖z.1 - z.2‖
  let shifted : E × E -> Real :=
    fun z => profile (D z) + C * (1 + D z)
  let shiftedIntegral : FiniteCoupling mu nu -> Real :=
    fun eta => ∫ z, shifted z ∂(eta.plan : Measure (E × E))
  let normalizedIntegral : FiniteCoupling mu nu -> Real :=
    fun eta =>
      ∫ z, shifted z
        ∂(eta.plan.normalize : Measure (E × E))
  let control : FiniteCoupling mu nu -> Real :=
    fun eta => C * ((mu.mass : Real) + distanceCost eta)

  have hShiftedNonnegative : 0 <= shifted := by
    intro z
    simpa [shifted, D] using hShiftNonnegative z.1 z.2
  have hShiftedLower : LowerSemicontinuous shifted := by
    simpa [shifted, D] using hShiftLower
  have hDistanceIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable D (eta.plan : Measure (E × E)) := by
    intro eta
    exact distanceIntegrableOfMarginalFirstMoments hMu hNu eta
  have hProfileIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable (fun z : E × E => profile (D z))
          (eta.plan : Measure (E × E)) := by
    intro eta
    exact admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
      hProfile hMu hNu eta
  have hControlIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable (fun z : E × E => C * (1 + D z))
          (eta.plan : Measure (E × E)) := by
    intro eta
    exact ((integrable_const 1).add (hDistanceIntegrable eta)).const_mul C
  have hShiftedIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable shifted (eta.plan : Measure (E × E)) := by
    intro eta
    simpa [shifted] using
      (hProfileIntegrable eta).add (hControlIntegrable eta)

  obtain ⟨_hCommonMass, hPlanMass, _hGammaMass, hPlanNormalize,
      _hGammaNormalize, hNormalizeTendsto⟩ :=
    fixedMassPlanNormalization
      (I := FiniteCoupling mu nu)
      (L := nhds gamma)
      (gammaNet := fun eta => eta)
      hPositive tendsto_id
  have hNormalizeIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable shifted
          (eta.plan.normalize : Measure (E × E)) := by
    intro eta
    have hPlanNonzero : eta.plan ≠ 0 := by
      apply eta.plan.mass_nonzero_iff.mp
      rw [hPlanMass eta]
      exact ne_of_gt hPositive
    rw [eta.plan.toMeasure_normalize_eq_of_nonzero hPlanNonzero]
    exact (hShiftedIntegrable eta).smul_measure_nnreal
  have hProbabilityLower :
      LowerSemicontinuous
        (fun P : ProbabilityMeasure (E × E) =>
          ∫⁻ z, ENNReal.ofReal (shifted z)
            ∂(P : Measure (E × E))) :=
    probabilityLintegralLowerSemicontinuous
      hShiftedLower hShiftedNonnegative
  have hNormalizedLintegralLower :
      LowerSemicontinuousAt
        (fun eta : FiniteCoupling mu nu =>
          ∫⁻ z, ENNReal.ofReal (shifted z)
            ∂(eta.plan.normalize : Measure (E × E)))
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
        hrNegative.trans_le (integral_nonneg hShiftedNonnegative)
    · have hrNonnegative : 0 <= r := le_of_not_gt hrNegative
      have hENNRealStrict :
          ENNReal.ofReal r <
            ∫⁻ z, ENNReal.ofReal (shifted z)
              ∂(gamma.plan.normalize : Measure (E × E)) := by
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
  have hNormalizeIntegral :
      ∀ eta : FiniteCoupling mu nu,
        shiftedIntegral eta =
          (mu.mass : Real) * normalizedIntegral eta := by
    intro eta
    change
      (∫ z, shifted z ∂(eta.plan : Measure (E × E))) =
        (mu.mass : Real) * normalizedIntegral eta
    rw [hPlanNormalize eta]
    simp [normalizedIntegral,
      FiniteMeasure.toMeasure_smul, NNReal.smul_def]
  have hPlanRealMass :
      ∀ eta : FiniteCoupling mu nu,
        (eta.plan : Measure (E × E)).real univ = (mu.mass : Real) := by
    intro eta
    calc
      (eta.plan : Measure (E × E)).real univ =
          ((eta.plan : Measure (E × E)) univ).toReal := rfl
      _ = (eta.plan.mass : ENNReal).toReal := by
        rw [FiniteMeasure.ennreal_mass]
      _ = (mu.mass : ENNReal).toReal := by rw [hPlanMass eta]
      _ = (mu.mass : Real) := ENNReal.coe_toReal mu.mass
  have hShiftedIntegral :
      ∀ eta : FiniteCoupling mu nu,
        shiftedIntegral eta =
          profileCost profile eta + control eta := by
    intro eta
    calc
      shiftedIntegral eta =
          (∫ z, profile (D z) ∂(eta.plan : Measure (E × E))) +
          ∫ z, C * (1 + D z)
            ∂(eta.plan : Measure (E × E)) := by
        simpa [shiftedIntegral, shifted] using
          integral_add (hProfileIntegrable eta) (hControlIntegrable eta)
      _ = profileCost profile eta + control eta := by
        rw [integral_const_mul,
          integral_add (integrable_const 1) (hDistanceIntegrable eta),
          integral_const, hPlanRealMass eta]
        simp [profileCost, distanceCost, control, D]
  have hControlTendsto :
      Tendsto (fun k => control (gammaSeq k)) atTop
        (nhds (control gamma)) := by
    have hDistanceTendsto :=
      distanceCostSequentiallyContinuousOfMarginalFirstMoments
        hMu hNu hTendsto
    simpa [control] using
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.add hDistanceTendsto))

  intro r hr
  let gap : Real := (profileCost profile gamma - r) / 3
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hShiftedEventually :
      ∀ᶠ k in atTop,
        shiftedIntegral gamma - gap <= shiftedIntegral (gammaSeq k) := by
    let threshold : Real :=
      (shiftedIntegral gamma - gap) / (mu.mass : Real)
    have hMassReal : 0 < (mu.mass : Real) := by
      exact_mod_cast hPositive
    have hThreshold :
        threshold < normalizedIntegral gamma := by
      dsimp [threshold]
      rw [hNormalizeIntegral gamma]
      exact (div_lt_iff₀ hMassReal).2 (by linarith)
    have hEventuallyNormalized :=
      hTendsto.eventually (hNormalizedIntegralLower threshold hThreshold)
    filter_upwards [hEventuallyNormalized] with k hk
    dsimp [threshold] at hk
    have hScaled :=
      (div_lt_iff₀ hMassReal).1 hk
    calc
      shiftedIntegral gamma - gap <=
          normalizedIntegral (gammaSeq k) * (mu.mass : Real) :=
        hScaled.le
      _ = shiftedIntegral (gammaSeq k) := by
        rw [hNormalizeIntegral (gammaSeq k)]
        ring
  have hControlEventually :
      ∀ᶠ k in atTop, control (gammaSeq k) < control gamma + gap :=
    hControlTendsto.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hShiftedEventually, hControlEventually] with k hkShift hkControl
  rw [hShiftedIntegral gamma, hShiftedIntegral (gammaSeq k)] at hkShift
  dsimp [gap] at hkShift hkControl
  linarith

end ConcaveOTLimit
