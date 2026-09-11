import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileHasNonnegativeLscDistanceShift
import Theorems.Thm_ConcaveOTLimit_finiteMeasureLeLiminfMeasureOpenOfTendstoOfMassEq
import Theorems.Thm_ConcaveOTLimit_forwardPlanAffineDistanceShiftIntegralEq
import Theorems.Thm_ConcaveOTLimit_lowerSemicontinuousLintegralLeLiminf

open Filter MeasureTheory Set Topology

open ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun measure : FiniteMeasure Real => (measure : Measure Real))
    gamma.property.1

theorem solution
    {I : Type*} {L : Filter I} [L.IsCountablyGenerated]
    {mu nu : FiniteMeasure Real}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real))
    {gammaNet : I -> FiniteCoupling mu nu}
    {gamma : FiniteCoupling mu nu}
    (hTendsto : Tendsto gammaNet L (nhds gamma))
    (hGammaForward : IsForwardPlan gamma)
    (hNetForward : forall i, IsForwardPlan (gammaNet i))
    (r : Real) (hr : r < profileCost profile gamma) :
    ∀ᶠ i in L, r <= profileCost profile (gammaNet i) := by
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
  let K : Real :=
    ∫ z, C * (1 + ‖z.1 - z.2‖)
      ∂(gamma.plan : Measure (Real × Real))

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

  have hPlan :
      Tendsto (fun i => (gammaNet i).plan) L (nhds gamma.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val.tendsto gamma).comp hTendsto
  have hMass :
      forall i, (gammaNet i).plan.mass = gamma.plan.mass := by
    intro i
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
    have hFirstI := (measurePreservingFst (gammaNet i)).map_eq
    have hFirst := (measurePreservingFst gamma).map_eq
    simpa only [
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using
      congrArg (fun measure : Measure Real => measure univ)
        (hFirstI.trans hFirst.symm)
  have hOpen :
      forall G : Set (Real × Real), IsOpen G ->
        (gamma.plan : Measure (Real × Real)) G <=
          L.liminf
            (fun i => ((gammaNet i).plan : Measure (Real × Real)) G) := by
    intro G hG
    exact finiteMeasureLeLiminfMeasureOpenOfTendstoOfMassEq
      hPlan hMass hG
  have hPortmanteau :
      (∫⁻ z, ENNReal.ofReal (shifted z)
          ∂(gamma.plan : Measure (Real × Real))) <=
        L.liminf
          (fun i =>
            ∫⁻ z, ENNReal.ofReal (shifted z)
              ∂((gammaNet i).plan : Measure (Real × Real))) :=
    lowerSemicontinuousLintegralLeLiminf
      hShiftedLower hShiftedNonnegative hOpen

  by_cases hNegative : r + K < 0
  · filter_upwards [] with i
    have hIntegralNonnegative :
        0 <= ∫ z, shifted z
          ∂((gammaNet i).plan : Measure (Real × Real)) :=
      integral_nonneg hShiftedNonnegative
    rw [hShiftedIntegral (gammaNet i) (hNetForward i)] at hIntegralNonnegative
    linarith

  have hStrict :
      ENNReal.ofReal (r + K) <
        ∫⁻ z, ENNReal.ofReal (shifted z)
          ∂(gamma.plan : Measure (Real × Real)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hShiftedIntegrable gamma)
      (ae_of_all _ hShiftedNonnegative),
      hShiftedIntegral gamma hGammaForward]
    have hIntegralPositive :
        0 < profileCost profile gamma + K := by
      have hIntegralNonnegative :
          0 <= ∫ z, shifted z
            ∂(gamma.plan : Measure (Real × Real)) :=
        integral_nonneg hShiftedNonnegative
      rw [hShiftedIntegral gamma hGammaForward] at hIntegralNonnegative
      linarith [le_of_not_gt hNegative]
    exact (ENNReal.ofReal_lt_ofReal_iff hIntegralPositive).2 (by linarith)
  have hEventually :=
    eventually_lt_of_lt_liminf (hStrict.trans_le hPortmanteau)
  filter_upwards [hEventually] with i hi
  rw [← ofReal_integral_eq_lintegral_ofReal
      (hShiftedIntegrable (gammaNet i))
      (ae_of_all _ hShiftedNonnegative),
    hShiftedIntegral (gammaNet i) (hNetForward i)] at hi
  have hiReal :
      r + K <= profileCost profile (gammaNet i) + K := by
    have hNonnegativeRight :
        0 <= profileCost profile (gammaNet i) + K := by
      have hIntegralNonnegative :
          0 <= ∫ z, shifted z
            ∂((gammaNet i).plan : Measure (Real × Real)) :=
        integral_nonneg hShiftedNonnegative
      rwa [hShiftedIntegral (gammaNet i) (hNetForward i)] at hIntegralNonnegative
    exact (ENNReal.ofReal_le_ofReal_iff hNonnegativeRight).mp hi.le
  linarith
