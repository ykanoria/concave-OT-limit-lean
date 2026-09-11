import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Deterministic

open Filter MeasureTheory ProbabilityTheory

open scoped MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y]

/-- If the conditional law of the second coordinate given the first agrees
almost everywhere with a deterministic kernel, the joint measure is the
graph-map pushforward of its first marginal. -/
theorem measure_eq_graphMap_of_condDistrib_ae_eq_deterministic
    (rho : Measure (X × Y)) [IsFiniteMeasure rho]
    (T : X -> Y) (hT : Measurable T)
    (hcond :
      condDistrib Prod.snd Prod.fst rho
        =ᵐ[rho.map Prod.fst] Kernel.deterministic T hT) :
    rho = (rho.map Prod.fst).map (fun x => (x, T x)) := by
  calc
    rho =
        rho.map Prod.fst ⊗ₘ
          condDistrib Prod.snd Prod.fst rho := by
      symm
      calc
        rho.map Prod.fst ⊗ₘ
              condDistrib Prod.snd Prod.fst rho =
            rho.map (fun p : X × Y => (p.1, p.2)) :=
          compProd_map_condDistrib
            (μ := rho)
            (X := (Prod.fst : X × Y -> X))
            (Y := (Prod.snd : X × Y -> Y))
            measurable_snd.aemeasurable
        _ = rho.map id := by
          congr 1
        _ = rho := Measure.map_id
    _ = rho.map Prod.fst ⊗ₘ Kernel.deterministic T hT :=
      Measure.compProd_congr hcond
    _ = (rho.map Prod.fst).map (fun x => (x, T x)) :=
      Measure.compProd_deterministic hT

/-- Finite-measure form of
`measure_eq_graphMap_of_condDistrib_ae_eq_deterministic`. -/
theorem finiteMeasure_eq_graphMap_of_condDistrib_ae_eq_deterministic
    (rho : FiniteMeasure (X × Y))
    (T : X -> Y) (hT : Measurable T)
    (hcond :
      condDistrib Prod.snd Prod.fst (rho : Measure (X × Y))
        =ᵐ[(rho : Measure (X × Y)).map Prod.fst]
          Kernel.deterministic T hT) :
    rho = (rho.map Prod.fst).map (fun x => (x, T x)) := by
  apply FiniteMeasure.toMeasure_injective
  simpa only [FiniteMeasure.toMeasure_map] using
    measure_eq_graphMap_of_condDistrib_ae_eq_deterministic
      (rho : Measure (X × Y)) T hT hcond

/-- A deterministic conditional law of the second coordinate given the
first supplies a globally measurable graph map and reconstructs the finite
joint measure exactly from its first marginal. -/
theorem graphPlan_of_isDeterministic_condDistrib
    (rho : FiniteMeasure (X × Y))
    (hdet :
      IsDeterministic
        (condDistrib Prod.snd Prod.fst
          (rho : Measure (X × Y)))) :
    ∃ T : X -> Y, ∃ _hT : Measurable T,
      rho = (rho.map Prod.fst).map (fun x => (x, T x)) := by
  letI :
      IsDeterministic
        (condDistrib Prod.snd Prod.fst
          (rho : Measure (X × Y))) :=
    hdet
  obtain ⟨T, hT, hkernel⟩ :=
    Kernel.IsDeterministic.exists_eq_deterministic
      (condDistrib Prod.snd Prod.fst
        (rho : Measure (X × Y)))
  refine ⟨T, hT, ?_⟩
  apply finiteMeasure_eq_graphMap_of_condDistrib_ae_eq_deterministic
  exact Eventually.of_forall fun x => DFunLike.congr_fun hkernel x

/-- The a.e.-deterministic reconstruction equality packages directly as
`IsGraphPlan` when the joint finite measure is a coupling. -/
theorem isGraphPlan_of_condDistrib_ae_eq_deterministic
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (T : X -> Y) (hT : Measurable T)
    (hcond :
      condDistrib Prod.snd Prod.fst
          (gamma.plan : Measure (X × Y))
        =ᵐ[(gamma.plan : Measure (X × Y)).map Prod.fst]
          Kernel.deterministic T hT) :
    IsGraphPlan gamma T := by
  refine ⟨hT, ?_⟩
  have hfst : gamma.plan.map Prod.fst = mu := by
    simpa [firstMarginal] using gamma.property.1
  calc
    gamma.plan =
        (gamma.plan.map Prod.fst).map (fun x => (x, T x)) :=
      finiteMeasure_eq_graphMap_of_condDistrib_ae_eq_deterministic
        gamma.plan T hT hcond
    _ = mu.map (fun x => (x, T x)) := by rw [hfst]
    _ = finiteGraphPlan mu T hT := rfl

/-- A deterministic source-conditional kernel turns a finite coupling into
a graph plan for a measurable map. -/
theorem existsGraphPlan_of_isDeterministic_condDistrib
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (hdet :
      IsDeterministic
        (condDistrib Prod.snd Prod.fst
          (gamma.plan : Measure (X × Y)))) :
    ∃ T : X -> Y, IsGraphPlan gamma T := by
  obtain ⟨T, hT, hgraph⟩ :=
    graphPlan_of_isDeterministic_condDistrib gamma.plan hdet
  refine ⟨T, hT, ?_⟩
  have hfst : gamma.plan.map Prod.fst = mu := by
    simpa [firstMarginal] using gamma.property.1
  calc
    gamma.plan =
        (gamma.plan.map Prod.fst).map (fun x => (x, T x)) :=
      hgraph
    _ = mu.map (fun x => (x, T x)) := by rw [hfst]
    _ = finiteGraphPlan mu T hT := rfl

end ConcaveOTLimit
