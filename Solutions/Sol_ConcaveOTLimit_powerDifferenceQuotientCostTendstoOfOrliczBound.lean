import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

open Filter MeasureTheory Set Topology

open ConcaveOTLimit

private theorem scalar_power_difference_quotient_tendsto
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

theorem solution
    {X : Type*} [MeasurableSpace X]
    (measure : Measure X) (cost : X -> Real)
    (hCostMeasurable : Measurable cost)
    (hCostNonnegative : ∀ x, 0 <= cost x)
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonLeHalf : ∀ n, epsilon n <= 1 / 2)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0))
    (hOrliczBound :
      ∀ {eps r : Real}, 0 < eps -> eps <= 1 / 2 -> 0 <= r ->
        abs ((powerProfile eps r - r) / eps) <= 2 + Psi r)
    (hBoundIntegrable :
      Integrable (fun x => 2 + Psi (cost x)) measure) :
    Tendsto
      (fun n =>
        integral measure
          (fun x =>
            (powerProfile (epsilon n) (cost x) - cost x) / epsilon n))
      atTop
      (nhds (integral measure (fun x => logarithmicProfile (cost x)))) := by
  have hEpsilonRight :
      Tendsto epsilon atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hEpsilonTendsto,
        Eventually.of_forall fun n => hEpsilonPos n⟩
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2 + Psi (cost x))
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
      (hContinuous.measurable.comp hCostMeasurable).aestronglyMeasurable
  · exact hBoundIntegrable
  · intro n
    exact ae_of_all measure fun x => by
      rw [Real.norm_eq_abs]
      exact hOrliczBound
        (hEpsilonPos n) (hEpsilonLeHalf n) (hCostNonnegative x)
  · filter_upwards [] with x
    simpa [Function.comp_def] using
      (scalar_power_difference_quotient_tendsto
        (hCostNonnegative x)).comp hEpsilonRight
