import Theorems.Thm_ConcaveOTLimit_positiveCrossingOccupationMeasure
import Theorems.Thm_ConcaveOTLimit_positiveCrossingOccupationUpperBound
import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrixMutuallySingular
import Theorems.Thm_ConcaveOTLimit_measureLeOfIoc
import Theorems.Thm_ConcaveOTLimit_existsFiniteMeasureRemainderOfLe

open MeasureTheory Set
open scoped ENNReal

namespace ConcaveOTLimit

noncomputable section

private theorem signedCumulative_increment'
    (mu nu : FiniteMeasure Real) {a b : Real} (hab : a ≤ b) :
    signedCumulative mu nu b - signedCumulative mu nu a =
      (mu : Measure Real).real (Ioc a b) -
        (nu : Measure Real).real (Ioc a b) := by
  calc
    signedCumulative mu nu b - signedCumulative mu nu a =
        (signedCumulativeBoundedVariation mu nu).vectorMeasure
          (Ioc a b) := by
      rw [(signedCumulativeBoundedVariation mu nu).vectorMeasure_Ioc hab,
        ((signedCumulativeRightContinuousAndLeftLim mu nu).1 b).rightLim_eq,
        ((signedCumulativeRightContinuousAndLeftLim mu nu).1 a).rightLim_eq]
    _ = juilletSignedMeasure mu nu (Ioc a b) := by
      rw [signedCumulativeVectorMeasure_eq_juilletSignedMeasure]
    _ = _ := by
      rw [juilletSignedMeasure,
        Measure.toSignedMeasure_sub_apply measurableSet_Ioc]

private theorem mutuallySingular_left_le_of_balance'
    {mu nu p q : Measure Real}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    [IsFiniteMeasure p] [IsFiniteMeasure q]
    (hSingular : mu ⟂ₘ nu)
    (hBalance : p + nu = q + mu) :
    mu ≤ p := by
  rcases hSingular with ⟨A, hA, hMu, hNu⟩
  refine Measure.le_intro fun s hs _ => ?_
  calc
    mu s = mu (s ∩ Aᶜ) := by
      rw [← measure_diff_null (s := s) hMu, diff_eq]
    _ ≤ (q + mu) (s ∩ Aᶜ) := by
      rw [Measure.add_apply]
      exact le_add_left le_rfl
    _ = (p + nu) (s ∩ Aᶜ) := by rw [hBalance]
    _ = p (s ∩ Aᶜ) := by
      rw [Measure.add_apply,
        measure_mono_null inter_subset_right hNu, add_zero]
    _ ≤ p s := measure_mono inter_subset_left

theorem positiveCrossingIndicatrixIdentity_of_atomless_mutuallySingular
    {mu nu : FiniteMeasure Real}
    (hAtomless : IsAtomlessFinite mu)
    (hSingular : FiniteMutuallySingular mu nu) :
    PositiveCrossingIndicatrixIdentity mu nu := by
  let rho : Measure Real :=
    positiveCrossingOccupationMeasure mu nu
  letI : IsFiniteMeasure rho := by
    dsimp only [rho]
    infer_instance
  have hMuLeRhoAddNu :
      (mu : Measure Real) ≤ rho + (nu : Measure Real) := by
    apply measure_le_of_Ioc
    intro a b hab
    rw [Measure.add_apply]
    apply tsub_le_iff_right.mp
    have hOccupation :=
      positiveIncrement_le_positiveCrossingOccupation_Ioc
        mu nu hAtomless hab
    rw [signedCumulative_increment' mu nu hab.le,
      ENNReal.ofReal_sub _ measureReal_nonneg,
      ofReal_measureReal, ofReal_measureReal] at hOccupation
    simpa only [rho,
      positiveCrossingOccupationMeasure_apply mu nu measurableSet_Ioc]
      using hOccupation
  let total : FiniteMeasure Real :=
    ⟨rho + (nu : Measure Real), inferInstance⟩
  obtain ⟨q, _hqDef, _hqLe, hQBalance⟩ :=
    existsFiniteMeasureRemainderOfLe total mu hMuLeRhoAddNu
  have hBalance :
      rho + (nu : Measure Real) =
        (q : Measure Real) + (mu : Measure Real) := by
    have hCoerced :=
      congrArg (fun eta : FiniteMeasure Real => (eta : Measure Real))
        hQBalance.symm
    simpa only [total, FiniteMeasure.toMeasure_mk,
      FiniteMeasure.toMeasure_add] using hCoerced
  have hMeasureSingular :
      (mu : Measure Real) ⟂ₘ (nu : Measure Real) := by
    rcases hSingular with ⟨A, hA, hMu, hNu⟩
    exact
      ⟨Aᶜ, hA.compl, hMu,
        by simpa only [compl_compl] using hNu⟩
  have hMuLeRho : (mu : Measure Real) ≤ rho :=
    mutuallySingular_left_le_of_balance'
      hMeasureSingular hBalance
  have hRhoLeMu : rho ≤ (mu : Measure Real) := by
    apply measure_le_of_Ioc
    intro a b hab
    calc
      rho (Ioc a b) =
          ∫⁻ h,
            ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ENNReal)
              ∂(volume : Measure Real) := by
        simpa only [rho] using
          positiveCrossingOccupationMeasure_apply
            mu nu measurableSet_Ioc
      _ ≤
          (SignedMeasure.toJordanDecomposition
            (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
              (Ioc a b) :=
        positiveCrossingOccupation_Ioc_le_positivePart
          mu nu hAtomless hab
      _ = (mu : Measure Real) (Ioc a b) := by
        rw [signedCumulativeVectorMeasure_positivePart_eq_source hSingular]
  have hRho : rho = (mu : Measure Real) :=
    le_antisymm hRhoLeMu hMuLeRho
  intro s hs
  calc
    (∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)
          ∂(volume : Measure Real)) =
        rho s := by
      simpa only [rho] using
        (positiveCrossingOccupationMeasure_apply mu nu hs).symm
    _ = (mu : Measure Real) s := by rw [hRho]
    _ = juilletPositiveVariationMeasure mu nu s := by
      rw [juilletPositiveVariationMeasureEqSource hSingular]

end

end ConcaveOTLimit
