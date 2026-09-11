import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMeasureSubsetOfAe
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A coupling of measures on Polish spaces carried by a set with injective
first projection is a graph plan. -/
theorem existsGraphPlanOfSupportedFstInjOn_polish
    {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (Gamma : Set (X × Y))
    (hGamma : Set.InjOn Prod.fst Gamma)
    (hSupported : IsSupported gamma Gamma) :
    ∃ T : X → Y, IsGraphPlan gamma T := by
  obtain ⟨S, hSMeasurable, hSFull, hSGamma⟩ :=
    existsMeasurableFullMeasureSubsetOfAe
      (gamma.plan : Measure (X × Y)) hSupported
  have hSInjective : Set.InjOn Prod.fst S :=
    hGamma.mono hSGamma
  have hFstEmbedding : MeasurableEmbedding (S.restrict Prod.fst) :=
    continuous_fst.continuousOn.measurableEmbedding
      hSMeasurable hSInjective
  obtain ⟨T, hTMeasurable, hTExtends⟩ :=
    hFstEmbedding.exists_measurable_extend
      (measurable_snd.comp measurable_subtype_coe)
      (fun _ => ‹Nonempty Y›)
  have hGraphId :
      (fun z : X × Y => (z.1, T z.1)) =ᵐ[
        (gamma.plan : Measure (X × Y))] id := by
    filter_upwards [mem_ae_iff.mpr hSFull] with z hz
    have hzExtends := congrFun hTExtends ⟨z, hz⟩
    simp only [Function.comp_apply, Set.restrict_apply] at hzExtends
    exact Prod.ext rfl hzExtends
  have hFirstMarginal :
      Measure.map Prod.fst (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X))
      gamma.property.1
  refine ⟨T, hTMeasurable, ?_⟩
  apply FiniteMeasure.toMeasure_injective
  change (gamma.plan : Measure (X × Y)) =
    ((finiteGraphPlan mu T hTMeasurable :
      FiniteMeasure (X × Y)) : Measure (X × Y))
  simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
  symm
  have hPairMeasurable : Measurable (fun x : X => (x, T x)) :=
    measurable_id.prodMk hTMeasurable
  calc
    Measure.map (fun x : X => (x, T x)) (mu : Measure X) =
        Measure.map (fun x : X => (x, T x))
          (Measure.map Prod.fst
            (gamma.plan : Measure (X × Y))) := by
      rw [hFirstMarginal]
    _ = Measure.map
          ((fun x : X => (x, T x)) ∘ Prod.fst)
          (gamma.plan : Measure (X × Y)) :=
      Measure.map_map hPairMeasurable measurable_fst
    _ = Measure.map id (gamma.plan : Measure (X × Y)) := by
      apply Measure.map_congr
      simpa [Function.comp_def] using hGraphId
    _ = (gamma.plan : Measure (X × Y)) := Measure.map_id

/-- Almost-everywhere uniqueness of the target fiber on a supporting set is
enough to turn a coupling on Polish spaces into a graph plan. -/
theorem existsGraphPlanOfSupportedAeUniqueFiber_polish
    {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (Gamma : Set (X × Y))
    (hSupported : IsSupported gamma Gamma)
    (hUnique :
      ∀ᵐ z ∂(gamma.plan : Measure (X × Y)),
        ∀ z' ∈ Gamma, z'.1 = z.1 → z'.2 = z.2) :
    ∃ T : X → Y, IsGraphPlan gamma T := by
  let S : Set (X × Y) :=
    {z | z ∈ Gamma ∧
      ∀ z' ∈ Gamma, z'.1 = z.1 → z'.2 = z.2}
  have hSupportedS : IsSupported gamma S := by
    filter_upwards [hSupported, hUnique] with z hzGamma hzUnique
    exact ⟨hzGamma, hzUnique⟩
  have hSInjective : Set.InjOn Prod.fst S := by
    intro z hz z' hz' hFst
    exact Prod.ext hFst (hz.2 z' hz'.1 hFst.symm).symm
  exact
    existsGraphPlanOfSupportedFstInjOn_polish
      gamma S hSInjective hSupportedS

/-- Source-almost-everywhere uniqueness of target fibers on a supporting set
is enough to turn a coupling on Polish spaces into a graph plan. -/
theorem existsGraphPlanOfSupportedSourceAeUniqueFiber_polish
    {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (Gamma : Set (X × Y))
    (hSupported : IsSupported gamma Gamma)
    (hUnique :
      ∀ᵐ x ∂(mu : Measure X),
        ∀ y y', (x, y) ∈ Gamma → (x, y') ∈ Gamma → y = y') :
    ∃ T : X → Y, IsGraphPlan gamma T := by
  have hFirstMarginal :
      Measure.map Prod.fst (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X))
      gamma.property.1
  let P : X → Prop :=
    fun x =>
      ∀ y y', (x, y) ∈ Gamma → (x, y') ∈ Gamma → y = y'
  have hUniqueMap :
      ∀ᵐ x ∂Measure.map Prod.fst
        (gamma.plan : Measure (X × Y)), P x := by
    rw [hFirstMarginal]
    exact hUnique
  have hUniquePlan :
      ∀ᵐ z ∂(gamma.plan : Measure (X × Y)),
        ∀ y y', (z.1, y) ∈ Gamma → (z.1, y') ∈ Gamma → y = y' := by
    simpa only [P] using
      (ae_of_ae_map measurable_fst.aemeasurable hUniqueMap)
  apply
    existsGraphPlanOfSupportedAeUniqueFiber_polish
      gamma Gamma hSupported
  filter_upwards [hSupported, hUniquePlan] with z hzGamma hzUnique
  intro z' hz' hFst
  rcases z' with ⟨x', y'⟩
  change x' = z.1 at hFst
  subst x'
  exact hzUnique y' z.2 hz' hzGamma

/-- A coupling carried by a set with injective first projection is a graph
plan. -/
theorem existsGraphPlanOfSupportedFstInjOn
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

end ConcaveOTLimit
