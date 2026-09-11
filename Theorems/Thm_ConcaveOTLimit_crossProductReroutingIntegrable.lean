import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace ConcaveOTLimit

/-- Two finite block measures dominated by a coupling with finite marginal
first moments have integrable direct costs, crossed costs, and swap gap for
every admissible concave profile. -/
theorem crossProductReroutingIntegrable
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (rho sigma : FiniteMeasure (Real × Real))
    (hRhoLe :
      (rho : Measure (Real × Real)) <=
        (gamma.plan : Measure (Real × Real)))
    (hSigmaLe :
      (sigma : Measure (Real × Real)) <=
        (gamma.plan : Measure (Real × Real))) :
    Measurable
        (fun z : Real × Real => profile (dist z.1 z.2)) /\
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (rho : Measure (Real × Real)) /\
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (sigma : Measure (Real × Real)) /\
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.2.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) /\
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.1.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) /\
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.1.2) +
              profile (dist rs.2.1 rs.2.2) -
            profile (dist rs.1.1 rs.2.2) -
            profile (dist rs.2.1 rs.1.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
  let eta : Measure ((Real × Real) × (Real × Real)) :=
    ((rho.prod sigma : FiniteMeasure
      ((Real × Real) × (Real × Real))) :
      Measure ((Real × Real) × (Real × Real)))
  have hCostMeasurable :
      Measurable
        (fun z : Real × Real => profile (dist z.1 z.2)) := by
    simpa only [dist_eq_norm] using
      (concaveProfileDistanceLowerSemicontinuous
        hProfile.1).measurable
  have hGammaCost :
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (gamma.plan : Measure (Real × Real)) := by
    simpa only [dist_eq_norm] using
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hProfile
        (by simpa only [Real.norm_eq_abs] using hMu)
        (by simpa only [Real.norm_eq_abs] using hNu)
        gamma
  have hRhoCost :
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (rho : Measure (Real × Real)) :=
    hGammaCost.mono_measure hRhoLe
  have hSigmaCost :
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (sigma : Measure (Real × Real)) :=
    hGammaCost.mono_measure hSigmaLe
  have hFirstPreserving :
      MeasurePreserving Prod.fst
        (gamma.plan : Measure (Real × Real))
        (mu : Measure Real) := by
    refine ⟨measurable_fst, ?_⟩
    simpa [firstMarginal] using congrArg
      (fun tau : FiniteMeasure Real => (tau : Measure Real))
      gamma.property.1
  have hSecondPreserving :
      MeasurePreserving Prod.snd
        (gamma.plan : Measure (Real × Real))
        (nu : Measure Real) := by
    refine ⟨measurable_snd, ?_⟩
    simpa [secondMarginal] using congrArg
      (fun tau : FiniteMeasure Real => (tau : Measure Real))
      gamma.property.2
  have hGammaFirst :
      Integrable (fun z : Real × Real => |z.1|)
        (gamma.plan : Measure (Real × Real)) := by
    simpa only [Function.comp_apply] using
      hFirstPreserving.integrable_comp_of_integrable hMu
  have hGammaSecond :
      Integrable (fun z : Real × Real => |z.2|)
        (gamma.plan : Measure (Real × Real)) := by
    simpa only [Function.comp_apply] using
      hSecondPreserving.integrable_comp_of_integrable hNu
  have hRhoFirst :
      Integrable (fun z : Real × Real => |z.1|)
        (rho : Measure (Real × Real)) :=
    hGammaFirst.mono_measure hRhoLe
  have hRhoSecond :
      Integrable (fun z : Real × Real => |z.2|)
        (rho : Measure (Real × Real)) :=
    hGammaSecond.mono_measure hRhoLe
  have hSigmaFirst :
      Integrable (fun z : Real × Real => |z.1|)
        (sigma : Measure (Real × Real)) :=
    hGammaFirst.mono_measure hSigmaLe
  have hSigmaSecond :
      Integrable (fun z : Real × Real => |z.2|)
        (sigma : Measure (Real × Real)) :=
    hGammaSecond.mono_measure hSigmaLe
  have hRhoFirstProduct :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          |rs.1.1|) eta := by
    dsimp only [eta]
    simpa only [FiniteMeasure.toMeasure_prod] using
      hRhoFirst.comp_fst (sigma : Measure (Real × Real))
  have hRhoSecondProduct :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          |rs.1.2|) eta := by
    dsimp only [eta]
    simpa only [FiniteMeasure.toMeasure_prod] using
      hRhoSecond.comp_fst (sigma : Measure (Real × Real))
  have hSigmaFirstProduct :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          |rs.2.1|) eta := by
    dsimp only [eta]
    simpa only [FiniteMeasure.toMeasure_prod] using
      hSigmaFirst.comp_snd (rho : Measure (Real × Real))
  have hSigmaSecondProduct :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          |rs.2.2|) eta := by
    dsimp only [eta]
    simpa only [FiniteMeasure.toMeasure_prod] using
      hSigmaSecond.comp_snd (rho : Measure (Real × Real))
  have hFirstSum :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          |rs.1.1| + |rs.2.2|) eta :=
    hRhoFirstProduct.add hSigmaSecondProduct
  have hSecondSum :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          |rs.2.1| + |rs.1.2|) eta :=
    hSigmaFirstProduct.add hRhoSecondProduct
  have hFirstDistance :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          dist rs.1.1 rs.2.2) eta := by
    refine hFirstSum.mono_nonneg
      (by fun_prop)
      (ae_of_all _ fun _ => dist_nonneg)
      (ae_of_all _ fun rs => ?_)
    simpa only [Real.dist_eq] using abs_sub rs.1.1 rs.2.2
  have hSecondDistance :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          dist rs.2.1 rs.1.2) eta := by
    refine hSecondSum.mono_nonneg
      (by fun_prop)
      (ae_of_all _ fun _ => dist_nonneg)
      (ae_of_all _ fun rs => ?_)
    simpa only [Real.dist_eq] using abs_sub rs.2.1 rs.1.2
  obtain ⟨C, _hC, hGrowth⟩ :=
    admissibleConcaveProfileLinearGrowth hProfile
  have hFirstCrossMap :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          (rs.1.1, rs.2.2)) := by
    fun_prop
  have hSecondCrossMap :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          (rs.2.1, rs.1.2)) := by
    fun_prop
  have hFirstCrossedMeasurable :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.2.2)) :=
    hCostMeasurable.comp hFirstCrossMap
  have hSecondCrossedMeasurable :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.1.2)) :=
    hCostMeasurable.comp hSecondCrossMap
  have hFirstEnvelope :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          C * (1 + dist rs.1.1 rs.2.2)) eta :=
    ((integrable_const 1).add hFirstDistance).const_mul C
  have hSecondEnvelope :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          C * (1 + dist rs.2.1 rs.1.2)) eta :=
    ((integrable_const 1).add hSecondDistance).const_mul C
  have hFirstCrossed :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.2.2)) eta := by
    refine hFirstEnvelope.mono'
      hFirstCrossedMeasurable.aestronglyMeasurable
      (ae_of_all _ fun rs => ?_)
    simpa only [Real.norm_eq_abs] using
      hGrowth (dist_nonneg : 0 <= dist rs.1.1 rs.2.2)
  have hSecondCrossed :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.1.2)) eta := by
    refine hSecondEnvelope.mono'
      hSecondCrossedMeasurable.aestronglyMeasurable
      (ae_of_all _ fun rs => ?_)
    simpa only [Real.norm_eq_abs] using
      hGrowth (dist_nonneg : 0 <= dist rs.2.1 rs.1.2)
  have hFirstDirect :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.1.2)) eta := by
    dsimp only [eta]
    simpa only [FiniteMeasure.toMeasure_prod] using
      hRhoCost.comp_fst (sigma : Measure (Real × Real))
  have hSecondDirect :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.2.2)) eta := by
    dsimp only [eta]
    simpa only [FiniteMeasure.toMeasure_prod] using
      hSigmaCost.comp_snd (rho : Measure (Real × Real))
  have hGap :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.1.2) +
              profile (dist rs.2.1 rs.2.2) -
            profile (dist rs.1.1 rs.2.2) -
            profile (dist rs.2.1 rs.1.2)) eta :=
    ((hFirstDirect.add hSecondDirect).sub'
      hFirstCrossed).sub' hSecondCrossed
  exact
    ⟨hCostMeasurable, hRhoCost, hSigmaCost,
      hFirstCrossed, hSecondCrossed, hGap⟩

end ConcaveOTLimit
