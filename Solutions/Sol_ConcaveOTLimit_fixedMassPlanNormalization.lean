import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Filter MeasureTheory Topology

noncomputable section

open ConcaveOTLimit

private theorem firstMarginalMass
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (firstMarginal rho).mass = rho.mass := by
  simp [firstMarginal, FiniteMeasure.mass,
    FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ]

private theorem secondMarginalMass
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (secondMarginal rho).mass = rho.mass := by
  simp [secondMarginal, FiniteMeasure.mass,
    FiniteMeasure.map_apply _ measurable_snd MeasurableSet.univ]

private theorem finiteCouplingPlanMassEqFirst
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) :
    gamma.plan.mass = mu.mass := by
  calc
    gamma.plan.mass = (firstMarginal gamma.plan).mass :=
      (firstMarginalMass gamma.plan).symm
    _ = mu.mass :=
      congrArg (fun rho : FiniteMeasure X => rho.mass) gamma.property.1

private theorem finiteCouplingMarginalMassEq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) :
    mu.mass = nu.mass := by
  calc
    mu.mass = gamma.plan.mass :=
      (finiteCouplingPlanMassEqFirst gamma).symm
    _ = (secondMarginal gamma.plan).mass :=
      (secondMarginalMass gamma.plan).symm
    _ = nu.mass :=
      congrArg (fun rho : FiniteMeasure Y => rho.mass) gamma.property.2

theorem solution
    {X Y I : Type*} [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    {L : Filter I} {gammaNet : I -> FiniteCoupling mu nu}
    {gamma : FiniteCoupling mu nu}
    (hPositive : 0 < mu.mass)
    (hTendsto : Tendsto gammaNet L (nhds gamma)) :
    mu.mass = nu.mass ∧
      (forall i, (gammaNet i).plan.mass = mu.mass) ∧
      gamma.plan.mass = mu.mass ∧
      (forall i, (gammaNet i).plan =
        mu.mass • (gammaNet i).plan.normalize.toFiniteMeasure) ∧
      gamma.plan =
        mu.mass • gamma.plan.normalize.toFiniteMeasure ∧
      Tendsto (fun i => (gammaNet i).plan.normalize)
        L (nhds gamma.plan.normalize) := by
  have hCommon := finiteCouplingMarginalMassEq gamma
  have hNetMass : forall i, (gammaNet i).plan.mass = mu.mass :=
    fun i => finiteCouplingPlanMassEqFirst (gammaNet i)
  have hLimitMass : gamma.plan.mass = mu.mass :=
    finiteCouplingPlanMassEqFirst gamma
  have hPlanTendsto :
      Tendsto (fun i => (gammaNet i).plan) L (nhds gamma.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val.tendsto gamma).comp hTendsto
  have hLimitMassNonzero : gamma.plan.mass ≠ 0 := by
    rw [hLimitMass]
    exact ne_of_gt hPositive
  have hLimitNonzero : gamma.plan ≠ 0 :=
    gamma.plan.mass_nonzero_iff.mp hLimitMassNonzero
  have hNormalize :
      Tendsto (fun i => (gammaNet i).plan.normalize)
        L (nhds gamma.plan.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto
      hPlanTendsto hLimitNonzero
  refine ⟨hCommon, hNetMass, hLimitMass, ?_, ?_, hNormalize⟩
  · intro i
    calc
      (gammaNet i).plan =
          (gammaNet i).plan.mass •
            (gammaNet i).plan.normalize.toFiniteMeasure :=
        (gammaNet i).plan.self_eq_mass_smul_normalize
      _ = mu.mass • (gammaNet i).plan.normalize.toFiniteMeasure := by
        rw [hNetMass i]
  · calc
      gamma.plan =
          gamma.plan.mass • gamma.plan.normalize.toFiniteMeasure :=
        gamma.plan.self_eq_mass_smul_normalize
      _ = mu.mass • gamma.plan.normalize.toFiniteMeasure := by
        rw [hLimitMass]
