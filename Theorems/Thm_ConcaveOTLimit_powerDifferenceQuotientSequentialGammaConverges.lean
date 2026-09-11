import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

private theorem logarithmic_profile_le_power_quotient
    {epsilon r : Real}
    (hEpsilonPos : 0 < epsilon) (hEpsilonLtOne : epsilon < 1)
    (hr : 0 <= r) :
    logarithmicProfile r <=
      (powerProfile epsilon r - r) / epsilon := by
  rcases hr.eq_or_lt with rfl | hr
  · have hPower : (0 : Real) ^ (1 - epsilon) = 0 :=
      Real.zero_rpow (by linarith)
    simp [logarithmicProfile, powerProfile, hPower]
  · rw [powerProfile, Real.rpow_def_of_pos hr]
    rw [show Real.log r * (1 - epsilon) =
        Real.log r + (-epsilon * Real.log r) by ring,
      Real.exp_add, Real.exp_log hr]
    rw [le_div_iff₀ hEpsilonPos]
    have hExp := Real.add_one_le_exp (-epsilon * Real.log r)
    have hInner :
        -epsilon * Real.log r <=
          Real.exp (-epsilon * Real.log r) - 1 := by
      linarith
    have hMul := mul_le_mul_of_nonneg_left hInner hr.le
    unfold logarithmicProfile Real.negMulLog
    nlinarith

private theorem power_quotient_tendsto_logarithmic
    {r : Real} (hr : 0 <= r) :
    Tendsto
      (fun epsilon => (powerProfile epsilon r - r) / epsilon)
      (nhdsWithin 0 (Ioi 0))
      (nhds (logarithmicProfile r)) := by
  rcases hr.eq_or_lt with rfl | hr
  · have hEventually :
        ∀ᶠ epsilon : Real in nhdsWithin 0 (Ioi 0), epsilon < 1 :=
      (eventually_lt_nhds zero_lt_one).filter_mono inf_le_left
    have hConstant :
        Tendsto (fun _ : Real => (0 : Real))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_const_nhds
    simpa [logarithmicProfile] using hConstant.congr' (by
      filter_upwards [hEventually] with epsilon hEpsilon
      have hPower : (0 : Real) ^ (1 - epsilon) = 0 :=
        Real.zero_rpow (by linarith)
      simp [powerProfile, hPower])
  · have hIdentity : HasDerivAt (fun epsilon : Real => epsilon) 1 0 :=
      hasDerivAt_id 0
    have hInner : HasDerivAt (fun epsilon : Real => 1 - epsilon) (-1) 0 :=
      hIdentity.const_sub 1
    have hDerivative :
        HasDerivAt
          (fun epsilon : Real => r ^ (1 - epsilon))
          (logarithmicProfile r) 0 := by
      have h := hInner.const_rpow hr
      convert h using 1
      simp [logarithmicProfile, Real.negMulLog]
      ring
    simpa [powerProfile, div_eq_inv_mul, mul_comm] using
      hDerivative.tendsto_slope_zero_right

/-- Weak lower semicontinuity of the logarithmic functional and the
integrable Orlicz domination imply sequential Gamma convergence of the power
difference-quotient functionals. -/
theorem powerDifferenceQuotientSequentialGammaConverges
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonLeHalf : ∀ n, epsilon n <= 1 / 2)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0))
    (hOrliczBound :
      ∀ {eps r : Real}, 0 < eps -> eps <= 1 / 2 -> 0 <= r ->
        abs ((powerProfile eps r - r) / eps) <= 2 + Psi r)
    (hLogarithmicIntegrable :
      ∀ gamma : FiniteCoupling mu nu,
        Integrable
          (fun z : E × E => logarithmicProfile ‖z.1 - z.2‖)
          (gamma.plan : Measure (E × E)))
    (hQuotientIntegrable :
      ∀ n (gamma : FiniteCoupling mu nu),
        Integrable
          (fun z : E × E =>
            (powerProfile (epsilon n) ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon n)
          (gamma.plan : Measure (E × E)))
    (hRecoveryBoundIntegrable :
      ∀ gamma : FiniteCoupling mu nu,
        Integrable
          (fun z : E × E => 2 + Psi ‖z.1 - z.2‖)
          (gamma.plan : Measure (E × E)))
    (hLogarithmicLowerSemicontinuous :
      ∀ {gammaSeq : Nat -> FiniteCoupling mu nu}
        {gamma : FiniteCoupling mu nu},
        Tendsto gammaSeq atTop (nhds gamma) ->
          ∀ r : Real, r < profileCost logarithmicProfile gamma ->
            ∀ᶠ k in atTop,
              r <= profileCost logarithmicProfile (gammaSeq k)) :
    SequentialGammaConverges
      (fun n (gamma : FiniteCoupling mu nu) =>
        ((integral (gamma.plan : Measure (E × E))
          (fun z =>
            (powerProfile (epsilon n) ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon n) : Real) : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        (profileCost logarithmicProfile gamma : EReal)) where
  liminf := by
    intro gammaSeq gamma subseq _ hGamma _ r hr
    have hrReal :
        r < profileCost logarithmicProfile gamma :=
      EReal.coe_lt_coe_iff.mp hr
    filter_upwards
      [hLogarithmicLowerSemicontinuous hGamma r hrReal] with k hk
    apply EReal.coe_le_coe_iff.mpr
    refine hk.trans ?_
    unfold profileCost
    exact integral_mono
      (hLogarithmicIntegrable (gammaSeq k))
      (hQuotientIntegrable (subseq k) (gammaSeq k))
      (fun z =>
        logarithmic_profile_le_power_quotient
          (hEpsilonPos (subseq k))
          (lt_of_le_of_lt (hEpsilonLeHalf (subseq k)) (by norm_num))
          (norm_nonneg _))
  recovery := by
    intro gamma _
    refine ⟨fun _ => gamma, tendsto_const_nhds, ?_⟩
    apply EReal.tendsto_coe.mpr
    change Tendsto
      (fun n =>
        integral (gamma.plan : Measure (E × E))
          (fun z =>
            (powerProfile (epsilon n) ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon n))
      atTop
      (nhds
        (integral (gamma.plan : Measure (E × E))
          (fun z => logarithmicProfile ‖z.1 - z.2‖)))
    have hEpsilonRight :
        Tendsto epsilon atTop (nhdsWithin 0 (Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hEpsilonTendsto,
          Eventually.of_forall fun n => hEpsilonPos n⟩
    apply tendsto_integral_of_dominated_convergence
      (fun z : E × E => 2 + Psi ‖z.1 - z.2‖)
    · intro n
      have hContinuous :
          Continuous
            (fun r : Real =>
              (powerProfile (epsilon n) r - r) / epsilon n) := by
        unfold powerProfile
        exact
          ((Real.continuous_rpow_const
              (by linarith [hEpsilonLeHalf n])).sub continuous_id).div_const _
      exact
        (hContinuous.measurable.comp
          ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
    · exact hRecoveryBoundIntegrable gamma
    · intro n
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        exact hOrliczBound
          (hEpsilonPos n) (hEpsilonLeHalf n) (norm_nonneg _)
    · filter_upwards [] with z
      simpa [Function.comp_def] using
        (power_quotient_tendsto_logarithmic
          (norm_nonneg (z.1 - z.2))).comp hEpsilonRight

end ConcaveOTLimit
