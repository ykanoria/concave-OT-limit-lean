import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileStrictRegularization
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Minimality for every admissible strictly concave profile implies the
comparison for every admissible concave profile by adding a vanishing
positive multiple of the half-power profile. -/
theorem concaveComparison_of_strictPowerHalfIdentification
    {mu nu : FiniteMeasure Real}
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (gammaEC : FiniteCoupling mu nu)
    (hStrictMinimality :
      forall strictProfile : Real -> Real,
        AdmissibleStrictlyConcaveProfile strictProfile ->
          IsMinimizerOn
            {eta : FiniteCoupling mu nu | IsForwardPlan eta}
            (profileCost strictProfile) gammaEC) :
    forall profile : Real -> Real,
      AdmissibleConcaveProfile profile ->
        forall gamma : FiniteCoupling mu nu,
          IsForwardPlan gamma ->
            profileCost profile gammaEC <= profileCost profile gamma := by
  intro profile hProfile gamma hForward
  apply le_of_forall_pos_le_add
  intro epsilon hEpsilon
  let denominator :=
    |profileCost (powerProfile (1 / 2)) gamma -
      profileCost (powerProfile (1 / 2)) gammaEC| + 1
  let delta := epsilon / denominator
  have hDenominatorPositive : 0 < denominator := by
    dsimp [denominator]
    exact add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
  have hDelta : 0 < delta := by
    exact div_pos hEpsilon hDenominatorPositive
  let regularizedProfile :=
    fun d => profile d + delta * powerProfile (1 / 2) d
  have hRegularizedStrict :
      AdmissibleStrictlyConcaveProfile regularizedProfile := by
    dsimp [regularizedProfile]
    exact admissibleConcaveProfileStrictRegularization hProfile hDelta
  have hRegularizedConcave :
      AdmissibleConcaveProfile regularizedProfile :=
    ⟨hRegularizedStrict.1.concaveOn, hRegularizedStrict.2⟩
  have hCostSplit (eta : FiniteCoupling mu nu) :
      profileCost regularizedProfile eta =
        profileCost profile eta +
          delta * profileCost (powerProfile (1 / 2)) eta := by
    have hProfileIntegrable :=
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hProfile hFirstMu hFirstNu eta
    have hRegularizedIntegrable :=
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hRegularizedConcave hFirstMu hFirstNu eta
    have hPerturbationIntegrable :
        Integrable
          (fun z : Real × Real =>
            delta * powerProfile (1 / 2) ‖z.1 - z.2‖)
          (eta.plan : Measure (Real × Real)) := by
      have hDifference :=
        hRegularizedIntegrable.sub hProfileIntegrable
      change
        Integrable
          (fun z : Real × Real =>
            (profile ‖z.1 - z.2‖ +
              delta * powerProfile (1 / 2) ‖z.1 - z.2‖) -
                profile ‖z.1 - z.2‖)
          (eta.plan : Measure (Real × Real)) at hDifference
      simpa only [add_sub_cancel_left] using hDifference
    change
      (∫ z, profile ‖z.1 - z.2‖ +
          delta * powerProfile (1 / 2) ‖z.1 - z.2‖
        ∂(eta.plan : Measure (Real × Real))) =
        (∫ z, profile ‖z.1 - z.2‖
          ∂(eta.plan : Measure (Real × Real))) +
          delta *
            ∫ z, powerProfile (1 / 2) ‖z.1 - z.2‖
              ∂(eta.plan : Measure (Real × Real))
    rw [integral_add hProfileIntegrable hPerturbationIntegrable,
      integral_const_mul]
  have hRegularizedComparison :
      profileCost regularizedProfile gammaEC <=
        profileCost regularizedProfile gamma :=
    (hStrictMinimality regularizedProfile hRegularizedStrict).2 gamma hForward
  rw [hCostSplit gammaEC, hCostSplit gamma] at hRegularizedComparison
  have hGapLe :
      profileCost (powerProfile (1 / 2)) gamma -
          profileCost (powerProfile (1 / 2)) gammaEC <=
        denominator := by
    calc
      profileCost (powerProfile (1 / 2)) gamma -
          profileCost (powerProfile (1 / 2)) gammaEC <=
          |profileCost (powerProfile (1 / 2)) gamma -
            profileCost (powerProfile (1 / 2)) gammaEC| :=
        le_abs_self _
      _ <= denominator := by
        dsimp [denominator]
        exact le_add_of_nonneg_right zero_le_one
  have hScaledGapLe :
      delta *
          (profileCost (powerProfile (1 / 2)) gamma -
            profileCost (powerProfile (1 / 2)) gammaEC) <=
        epsilon := by
    calc
      delta *
          (profileCost (powerProfile (1 / 2)) gamma -
            profileCost (powerProfile (1 / 2)) gammaEC) <=
          delta * denominator :=
        mul_le_mul_of_nonneg_left hGapLe hDelta.le
      _ = epsilon := by
        exact div_mul_cancel₀ epsilon hDenominatorPositive.ne'
  linarith

end ConcaveOTLimit
