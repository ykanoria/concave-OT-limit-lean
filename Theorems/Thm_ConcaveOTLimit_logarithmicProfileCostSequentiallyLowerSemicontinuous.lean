import Theorems.Thm_ConcaveOTLimit_PsiNormSubBound
import Theorems.Thm_ConcaveOTLimit_absLogarithmicProfileLeOneAddPsi
import Theorems.Thm_ConcaveOTLimit_logarithmicCostIntegrableOfMarginalLogMoments
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory Set Topology

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

private theorem leMeasureComplLiminfOfLimsupMeasureLeOfUnivEq
    {Omega I : Type*} [MeasurableSpace Omega]
    {L : Filter I} {m : Measure Omega} {ms : I -> Measure Omega}
    [IsFiniteMeasure m] [∀ i, IsFiniteMeasure (ms i)]
    {s : Set Omega} (hs : MeasurableSet s)
    (huniv : ∀ i, ms i univ = m univ)
    (h : L.limsup (fun i => ms i s) <= m s) :
    m sᶜ <= L.liminf (fun i => ms i sᶜ) := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have hm : m sᶜ = m univ - m s :=
    measure_compl hs (measure_lt_top m s).ne
  have hms : ∀ i, ms i sᶜ = m univ - ms i s := by
    intro i
    rw [measure_compl hs (measure_lt_top (ms i) s).ne, huniv i]
  simp_rw [hm, hms]
  rw [show (L.liminf fun i : I => m univ - ms i s) =
      L.liminf ((fun x => m univ - x) ∘ fun i : I => ms i s) from rfl]
  have hkey := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => ms i s)
    (ENNReal.continuous_sub_left (measure_ne_top m univ)).continuousAt
  simpa [← hkey] using antitone_const_tsub h

private theorem finiteMeasureLeLiminfMeasureOpen
    {Omega : Type*} [MeasurableSpace Omega] [TopologicalSpace Omega]
    [OpensMeasurableSpace Omega] [HasOuterApproxClosed Omega]
    {m : FiniteMeasure Omega} {ms : Nat -> FiniteMeasure Omega}
    (hms : Tendsto ms atTop (nhds m))
    (hmass : ∀ i, (ms i).mass = m.mass)
    {s : Set Omega} (hs : IsOpen s) :
    (m : Measure Omega) s <=
      atTop.liminf (fun i => (ms i : Measure Omega) s) := by
  have huniv : ∀ i, (ms i : Measure Omega) univ =
      (m : Measure Omega) univ := by
    intro i
    rw [← FiniteMeasure.ennreal_mass, ← FiniteMeasure.ennreal_mass, hmass i]
  have hclosed :
      atTop.limsup (fun i => (ms i : Measure Omega) sᶜ) <=
        (m : Measure Omega) sᶜ :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto hms
      (isClosed_compl_iff.mpr hs)
  simpa only [compl_compl] using
    leMeasureComplLiminfOfLimsupMeasureLeOfUnivEq
      hs.measurableSet.compl huniv hclosed

private theorem continuousPsiNorm
    {E : Type*} [NormedAddCommGroup E] :
    Continuous (fun x : E => Psi ‖x‖) := by
  unfold Psi
  exact continuous_norm.mul
    ((continuous_const.add continuous_norm).log (fun x => by
      change 1 + ‖x‖ ≠ 0
      positivity))

private theorem logarithmicLowerControl
    {E : Type*} [NormedAddCommGroup E] (z : E × E) :
    0 <= logarithmicProfile ‖z.1 - z.2‖ +
      5 * (1 + Psi ‖z.1‖ + Psi ‖z.2‖) := by
  have hAbs :=
    absLogarithmicProfileLeOneAddPsi (norm_nonneg (z.1 - z.2))
  have hPsi := PsiNormSubBound z.1 z.2
  have hPsiFst : 0 <= Psi ‖z.1‖ := by
    exact mul_nonneg (norm_nonneg _)
      (Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg _)))
  have hPsiSnd : 0 <= Psi ‖z.2‖ := by
    exact mul_nonneg (norm_nonneg _)
      (Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg _)))
  have hLower : -(1 + Psi ‖z.1 - z.2‖) <=
      logarithmicProfile ‖z.1 - z.2‖ :=
    neg_le_of_abs_le hAbs
  linarith

/-- Marginal logarithmic moments imply sequential lower semicontinuity of
the logarithmic transport cost on the fixed-marginal coupling space. -/
theorem logarithmicProfileCostSequentiallyLowerSemicontinuous
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    {gammaSeq : Nat -> FiniteCoupling mu nu}
    {gamma : FiniteCoupling mu nu}
    (hGamma : Tendsto gammaSeq atTop (nhds gamma))
    (r : Real) (hr : r < profileCost logarithmicProfile gamma) :
    ∀ᶠ k in atTop,
      r <= profileCost logarithmicProfile (gammaSeq k) := by
  let G : E -> Real := fun x => Psi ‖x‖
  let control : E × E -> Real :=
    fun z => 5 * (1 + G z.1 + G z.2)
  let shifted : E × E -> Real :=
    fun z => logarithmicProfile ‖z.1 - z.2‖ + control z
  let K : Real :=
    5 * ((mu : Measure E).real univ +
      ∫ x, G x ∂(mu : Measure E) +
      ∫ y, G y ∂(nu : Measure E))

  have hGContinuous : Continuous G := by
    simpa [G] using (continuousPsiNorm (E := E))
  have hShiftedContinuous : Continuous shifted := by
    dsimp [shifted, control]
    exact
      (Real.continuous_negMulLog.comp
        ((continuous_fst.sub continuous_snd).norm)).add
        (continuous_const.mul
          ((continuous_const.add (hGContinuous.comp continuous_fst)).add
            (hGContinuous.comp continuous_snd)))
  have hShiftedNonnegative : 0 <= shifted := by
    intro z
    simpa [shifted, control, G] using
      (logarithmicLowerControl z)

  have hGMeasurable : AEStronglyMeasurable G (mu : Measure E) :=
    hGContinuous.measurable.aestronglyMeasurable
  have hGMeasurableNu : AEStronglyMeasurable G (nu : Measure E) :=
    hGContinuous.measurable.aestronglyMeasurable

  have hControlIntegral :
      ∀ eta : FiniteCoupling mu nu,
        (∫ z, control z ∂(eta.plan : Measure (E × E))) = K := by
    intro eta
    have hFirst : Integrable (fun z : E × E => G z.1)
        (eta.plan : Measure (E × E)) :=
      (measurePreservingFst eta).integrable_comp_of_integrable hMu
    have hSecond : Integrable (fun z : E × E => G z.2)
        (eta.plan : Measure (E × E)) :=
      (measurePreservingSnd eta).integrable_comp_of_integrable hNu
    have hOne : Integrable (fun _ : E × E => (1 : Real))
        (eta.plan : Measure (E × E)) := integrable_const 1
    have hMass :
        (eta.plan : Measure (E × E)).real univ =
          (mu : Measure E).real univ := by
      rw [← (measurePreservingFst eta).map_eq,
        map_measureReal_apply measurable_fst MeasurableSet.univ,
        preimage_univ]
    dsimp [control, K]
    rw [integral_const_mul]
    congr 1
    calc
      (∫ z, 1 + G z.1 + G z.2 ∂(eta.plan : Measure (E × E))) =
          (∫ z, 1 + G z.1 ∂(eta.plan : Measure (E × E))) +
            ∫ z, G z.2 ∂(eta.plan : Measure (E × E)) :=
        integral_add (hOne.add hFirst) hSecond
      _ = ((∫ _z, (1 : Real) ∂(eta.plan : Measure (E × E))) +
            ∫ z, G z.1 ∂(eta.plan : Measure (E × E))) +
            ∫ z, G z.2 ∂(eta.plan : Measure (E × E)) := by
        rw [integral_add hOne hFirst]
      _ = (mu : Measure E).real univ +
            (∫ x, G x ∂(mu : Measure E)) +
            ∫ y, G y ∂(nu : Measure E) := by
        rw [integral_const, hMass,
          integralCompMeasurePreserving
            (measurePreservingFst eta) hGMeasurable,
          integralCompMeasurePreserving
            (measurePreservingSnd eta) hGMeasurableNu]
        simp

  have hShiftedIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable shifted (eta.plan : Measure (E × E)) := by
    intro eta
    have hLog :=
      logarithmicCostIntegrableOfMarginalLogMoments hMu hNu eta
    have hFirst : Integrable (fun z : E × E => G z.1)
        (eta.plan : Measure (E × E)) :=
      (measurePreservingFst eta).integrable_comp_of_integrable hMu
    have hSecond : Integrable (fun z : E × E => G z.2)
        (eta.plan : Measure (E × E)) :=
      (measurePreservingSnd eta).integrable_comp_of_integrable hNu
    have hControl : Integrable control
        (eta.plan : Measure (E × E)) := by
      dsimp [control]
      exact (((integrable_const 1).add hFirst).add hSecond).const_mul 5
    exact hLog.add hControl

  have hShiftedIntegral :
      ∀ eta : FiniteCoupling mu nu,
        (∫ z, shifted z ∂(eta.plan : Measure (E × E))) =
          profileCost logarithmicProfile eta + K := by
    intro eta
    have hLog :=
      logarithmicCostIntegrableOfMarginalLogMoments hMu hNu eta
    have hFirst : Integrable (fun z : E × E => G z.1)
        (eta.plan : Measure (E × E)) :=
      (measurePreservingFst eta).integrable_comp_of_integrable hMu
    have hSecond : Integrable (fun z : E × E => G z.2)
        (eta.plan : Measure (E × E)) :=
      (measurePreservingSnd eta).integrable_comp_of_integrable hNu
    have hControl : Integrable control
        (eta.plan : Measure (E × E)) := by
      dsimp [control]
      exact (((integrable_const 1).add hFirst).add hSecond).const_mul 5
    dsimp [shifted]
    rw [integral_add hLog hControl, hControlIntegral eta]
    rfl

  have hPlan :
      Tendsto (fun k => (gammaSeq k).plan) atTop (nhds gamma.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val.tendsto gamma).comp hGamma
  have hMass :
      ∀ k, (gammaSeq k).plan.mass = gamma.plan.mass := by
    intro k
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
    have hFirstK := (measurePreservingFst (gammaSeq k)).map_eq
    have hFirst := (measurePreservingFst gamma).map_eq
    simpa only [
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using
      congrArg (fun m : Measure E => m univ) (hFirstK.trans hFirst.symm)
  have hOpen :
      ∀ s : Set (E × E), IsOpen s ->
        (gamma.plan : Measure (E × E)) s <=
          atTop.liminf
            (fun k => ((gammaSeq k).plan : Measure (E × E)) s) := by
    intro s hs
    exact finiteMeasureLeLiminfMeasureOpen hPlan hMass hs
  have hPortmanteau :
      (∫⁻ z, ENNReal.ofReal (shifted z)
          ∂(gamma.plan : Measure (E × E))) <=
        atTop.liminf
          (fun k =>
            ∫⁻ z, ENNReal.ofReal (shifted z)
              ∂((gammaSeq k).plan : Measure (E × E))) :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      hShiftedContinuous hShiftedNonnegative hOpen

  by_cases hNegative : r + K < 0
  · filter_upwards [] with k
    have hIntegralNonnegative :
        0 <= ∫ z, shifted z
          ∂((gammaSeq k).plan : Measure (E × E)) :=
      integral_nonneg hShiftedNonnegative
    rw [hShiftedIntegral (gammaSeq k)] at hIntegralNonnegative
    linarith

  have hStrict :
      ENNReal.ofReal (r + K) <
        ∫⁻ z, ENNReal.ofReal (shifted z)
          ∂(gamma.plan : Measure (E × E)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hShiftedIntegrable gamma)
      (ae_of_all _ hShiftedNonnegative),
      hShiftedIntegral gamma]
    have hIntegralPositive :
        0 < profileCost logarithmicProfile gamma + K := by
      have hIntegralNonnegative :
          0 <= ∫ z, shifted z ∂(gamma.plan : Measure (E × E)) :=
        integral_nonneg hShiftedNonnegative
      rw [hShiftedIntegral gamma] at hIntegralNonnegative
      linarith [le_of_not_gt hNegative]
    exact (ENNReal.ofReal_lt_ofReal_iff hIntegralPositive).2 (by linarith)
  have hEventually :=
    eventually_lt_of_lt_liminf (hStrict.trans_le hPortmanteau)
  filter_upwards [hEventually] with k hk
  rw [← ofReal_integral_eq_lintegral_ofReal
      (hShiftedIntegrable (gammaSeq k))
      (ae_of_all _ hShiftedNonnegative),
    hShiftedIntegral (gammaSeq k)] at hk
  have hkReal : r + K <=
      profileCost logarithmicProfile (gammaSeq k) + K := by
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have hIntegralNonnegative :
          0 <= ∫ z, shifted z
            ∂((gammaSeq k).plan : Measure (E × E)) :=
        integral_nonneg hShiftedNonnegative
      rwa [hShiftedIntegral (gammaSeq k)] at hIntegralNonnegative)).mp hk.le
  linarith

end ConcaveOTLimit
