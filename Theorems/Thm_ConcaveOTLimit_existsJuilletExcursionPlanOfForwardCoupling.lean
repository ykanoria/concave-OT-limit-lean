import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileStrictRegularization
import Theorems.Thm_ConcaveOTLimit_existsAdmissibleConcaveForwardMinimizer
import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
import Theorems.Thm_ConcaveOTLimit_forwardPlansEqDistanceOptimalFaceOfAbsMoments
import Theorems.Thm_ConcaveOTLimit_isJuilletExcursionPlanOfLexicographicSupport
import Mathlib.Tactic.NormNum

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A supplied forward coupling makes the variational construction of a
Juillet excursion plan nonempty. -/
theorem existsJuilletExcursionPlanOfForwardCoupling
    {mu nu : FiniteMeasure Real}
    (hMu : Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (gammaForward : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gammaForward) :
    exists gamma : FiniteCoupling mu nu,
      IsForwardPlan gamma /\
        IsJuilletExcursionPlan mu nu gamma.plan := by
  let profile : Real -> Real := powerProfile (1 / 2)
  have hZero : AdmissibleConcaveProfile (fun _ : Real => 0) := by
    refine ⟨concaveOn_const 0 (convex_Ici 0), 0, le_rfl, ?_⟩
    intro d hd
    norm_num
  have hProfile :
      AdmissibleStrictlyConcaveProfile profile := by
    dsimp [profile]
    simpa using
      (admissibleConcaveProfileStrictRegularization
        hZero (delta := (1 : Real)) zero_lt_one)
  have hProfileConcave : AdmissibleConcaveProfile profile :=
    ⟨hProfile.1.concaveOn, hProfile.2⟩
  have hMuId :
      Integrable (fun x : Real => x) (mu : Measure Real) := by
    apply (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hMu
  have hNuId :
      Integrable (fun y : Real => y) (nu : Measure Real) := by
    apply (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hNu
  obtain ⟨gamma, hMinForward⟩ :=
    existsAdmissibleConcaveForwardMinimizer
      hProfileConcave hMuId hNuId gammaForward hForward
  have hGammaForward : IsForwardPlan gamma := hMinForward.1
  have hForwardFace :
      {eta : FiniteCoupling mu nu | IsForwardPlan eta} =
        distanceOptimalFace mu nu :=
    forwardPlansEqDistanceOptimalFaceOfAbsMoments
      hMu hNu gammaForward hForward
  have hMinSecondary : IsSecondaryMinimizer profile gamma := by
    change
      IsMinimizerOn (distanceOptimalFace mu nu)
        (profileCost profile) gamma
    rw [← hForwardFace]
    exact hMinForward
  obtain ⟨support, hMeasurable, hFull, hLex⟩ :=
    existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
      hProfile hMu hNu hSingular hMinSecondary hGammaForward
  refine ⟨gamma, hGammaForward, ?_⟩
  exact
    isJuilletExcursionPlanOfLexicographicSupport
      hProfile.1 hSingular hGammaForward hMeasurable hFull hLex

end ConcaveOTLimit
