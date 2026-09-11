import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMeasureSubsetOfAe
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (Gamma : Set (Real × Real))
    (hGamma : Set.InjOn Prod.fst Gamma)
    (hSupported : IsSupported gamma Gamma) :
    ∃ T : Real → Real, IsGraphPlan gamma T := by
  obtain ⟨S, hSMeasurable, hSFull, hSGamma⟩ :=
    existsMeasurableFullMeasureSubsetOfAe
      (gamma.plan : Measure (Real × Real)) hSupported
  have hSInjective : Set.InjOn Prod.fst S :=
    hGamma.mono hSGamma
  have hFstEmbedding : MeasurableEmbedding (S.restrict Prod.fst) :=
    continuous_fst.continuousOn.measurableEmbedding
      hSMeasurable hSInjective
  obtain ⟨T, hTMeasurable, hTExtends⟩ :=
    hFstEmbedding.exists_measurable_extend
      (measurable_snd.comp measurable_subtype_coe)
      (fun _ => ⟨0⟩)
  have hGraphId :
      (fun z : Real × Real => (z.1, T z.1)) =ᵐ[
        (gamma.plan : Measure (Real × Real))] id := by
    filter_upwards [mem_ae_iff.mpr hSFull] with z hz
    have hzExtends := congrFun hTExtends ⟨z, hz⟩
    simp only [Function.comp_apply, Set.restrict_apply] at hzExtends
    exact Prod.ext rfl hzExtends
  have hFirstMarginal :
      Measure.map Prod.fst (gamma.plan : Measure (Real × Real)) =
        (mu : Measure Real) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure Real => (rho : Measure Real))
      gamma.property.1
  refine ⟨T, hTMeasurable, ?_⟩
  apply FiniteMeasure.toMeasure_injective
  change (gamma.plan : Measure (Real × Real)) =
    ((finiteGraphPlan mu T hTMeasurable :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))
  simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
  symm
  have hPairMeasurable : Measurable (fun x : Real => (x, T x)) :=
    measurable_id.prodMk hTMeasurable
  calc
    Measure.map (fun x : Real => (x, T x)) (mu : Measure Real) =
        Measure.map (fun x : Real => (x, T x))
          (Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real))) := by
      rw [hFirstMarginal]
    _ = Measure.map
          ((fun x : Real => (x, T x)) ∘ Prod.fst)
          (gamma.plan : Measure (Real × Real)) :=
      Measure.map_map hPairMeasurable measurable_fst
    _ = Measure.map id (gamma.plan : Measure (Real × Real)) := by
      apply Measure.map_congr
      simpa [Function.comp_def] using hGraphId
    _ = (gamma.plan : Measure (Real × Real)) := Measure.map_id
