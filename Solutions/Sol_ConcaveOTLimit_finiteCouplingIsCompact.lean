import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.MetricSpace.Polish

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

open ConcaveOTLimit

private theorem mass_firstMarginal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (gamma : FiniteMeasure (X × Y)) :
    (firstMarginal gamma).mass = gamma.mass := by
  simp [firstMarginal, FiniteMeasure.mass,
    FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ]

private theorem mass_eq_source_of_isFiniteCoupling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    {gamma : FiniteMeasure (X × Y)}
    (hgamma : IsFiniteCoupling mu nu gamma) :
    gamma.mass = mu.mass := by
  rw [← mass_firstMarginal gamma, hgamma.1]

private theorem continuous_firstMarginal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [OpensMeasurableSpace (X × Y)] [BorelSpace X] :
    Continuous
      (firstMarginal :
        FiniteMeasure (X × Y) -> FiniteMeasure X) := by
  change Continuous
    (fun gamma : FiniteMeasure (X × Y) => gamma.map Prod.fst)
  exact FiniteMeasure.continuous_map continuous_fst

private theorem continuous_secondMarginal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [OpensMeasurableSpace (X × Y)] [BorelSpace Y] :
    Continuous
      (secondMarginal :
        FiniteMeasure (X × Y) -> FiniteMeasure Y) := by
  change Continuous
    (fun gamma : FiniteMeasure (X × Y) => gamma.map Prod.snd)
  exact FiniteMeasure.continuous_map continuous_snd

private theorem isClosed_isFiniteCoupling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [OpensMeasurableSpace (X × Y)]
    [BorelSpace X] [BorelSpace Y]
    [HasOuterApproxClosed X] [HasOuterApproxClosed Y]
    (mu : FiniteMeasure X) (nu : FiniteMeasure Y) :
    IsClosed
      {gamma : FiniteMeasure (X × Y) |
        IsFiniteCoupling mu nu gamma} := by
  simpa only [IsFiniteCoupling, setOf_and] using
    (isClosed_eq continuous_firstMarginal continuous_const).inter
      (isClosed_eq continuous_secondMarginal continuous_const)

private theorem isCompact_of_isClosed_of_mass_eq_of_isTightMeasureSet
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [BorelSpace E]
    {S : Set (FiniteMeasure E)} {C : NNReal}
    (hSClosed : IsClosed S)
    (hSMass : ∀ mu ∈ S, mu.mass = C)
    (hSTight :
      IsTightMeasureSet
        ((fun mu : FiniteMeasure E => (mu : Measure E)) '' S)) :
    IsCompact S := by
  obtain ⟨u, -, huPos, huLim⟩ :
      ∃ u : Nat -> NNReal,
        StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (nhds 0) :=
    exists_seq_strictAnti_tendsto 0
  have hCompactBound (n : Nat) :
      ∃ K : Set E, IsCompact K ∧
        ∀ mu ∈ S, mu Kᶜ ≤ u n := by
    obtain ⟨K, hK, hKS⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hSTight
        (u n : ENNReal) (by simpa using huPos n)
    refine ⟨K, hK, fun mu hmu => ?_⟩
    have h := hKS (mu : Measure E) ⟨mu, hmu, rfl⟩
    exact ENNReal.coe_le_coe.mp (by simpa using h)
  choose K hK hKS using hCompactBound
  let K' : Nat -> Set E := fun n => ⋃ i ∈ Iic n, K i
  have hKCompact (n : Nat) : IsCompact (K' n) := by
    exact (finite_Iic n).isCompact_biUnion fun i _ => hK i
  have hKMono : Monotone K' := by
    intro a b hab x hx
    simp only [K', mem_iUnion, mem_Iic] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hi.trans hab, hxi⟩
  have hAmbient :
      IsCompact
        {mu : FiniteMeasure E |
          mu.mass = C ∧ ∀ n, mu (K' n)ᶜ ≤ u n} :=
    isCompact_setOf_finiteMeasure_mass_eq_compl_isCompact_le
      C huLim hKCompact (Or.inr hKMono)
  apply hAmbient.of_isClosed_subset hSClosed
  intro mu hmu
  refine ⟨hSMass mu hmu, fun n => ?_⟩
  calc
    mu (K' n)ᶜ ≤ mu (K n)ᶜ :=
      mu.apply_mono (compl_subset_compl.mpr <| by
        change K n ⊆ ⋃ i ∈ Iic n, K i
        exact subset_biUnion_of_mem (by simp : n ∈ Iic n))
    _ ≤ u n := hKS n mu hmu

private theorem isTightMeasureSet_isFiniteCoupling
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [BorelSpace E]
    (mu nu : FiniteMeasure E)
    (hmu : IsTightMeasureSet {(mu : Measure E)})
    (hnu : IsTightMeasureSet {(nu : Measure E)}) :
    IsTightMeasureSet
      ((fun gamma : FiniteMeasure (E × E) =>
          (gamma : Measure (E × E))) ''
        {gamma | IsFiniteCoupling mu nu gamma}) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  have hepsilonHalf : 0 < epsilon / 2 := by
    exact ENNReal.div_pos hepsilon.ne' (by norm_num)
  obtain ⟨K, hK, hmuK⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hmu
      (epsilon / 2) hepsilonHalf
  obtain ⟨L, hL, hnuL⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hnu
      (epsilon / 2) hepsilonHalf
  refine ⟨K ×ˢ L, hK.prod hL, ?_⟩
  intro rho hrho
  obtain ⟨gamma, hgamma, rfl⟩ := hrho
  change IsFiniteCoupling mu nu gamma at hgamma
  have hmuBound : (mu : Measure E) Kᶜ ≤ epsilon / 2 :=
    hmuK (mu : Measure E) (mem_singleton (mu : Measure E))
  have hnuBound : (nu : Measure E) Lᶜ ≤ epsilon / 2 :=
    hnuL (nu : Measure E) (mem_singleton (nu : Measure E))
  rw [compl_prod_eq_union, prod_univ, univ_prod]
  calc
    (gamma : Measure (E × E))
        (Prod.fst ⁻¹' Kᶜ ∪ Prod.snd ⁻¹' Lᶜ) ≤
        (gamma : Measure (E × E)) (Prod.fst ⁻¹' Kᶜ) +
          (gamma : Measure (E × E)) (Prod.snd ⁻¹' Lᶜ) :=
      measure_union_le _ _
    _ = (firstMarginal gamma : Measure E) Kᶜ +
          (secondMarginal gamma : Measure E) Lᶜ := by
      simp only [firstMarginal, secondMarginal,
        FiniteMeasure.toMeasure_map]
      rw [Measure.map_apply measurable_fst hK.measurableSet.compl,
        Measure.map_apply measurable_snd hL.measurableSet.compl]
    _ = (mu : Measure E) Kᶜ + (nu : Measure E) Lᶜ := by
      rw [hgamma.1, hgamma.2]
    _ ≤ epsilon / 2 + epsilon / 2 :=
      add_le_add hmuBound hnuBound
    _ = epsilon := ENNReal.add_halves epsilon

private theorem isCompact_isFiniteCoupling
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [BorelSpace E] [PolishSpace E]
    (mu nu : FiniteMeasure E) :
    IsCompact
      {gamma : FiniteMeasure (E × E) |
        IsFiniteCoupling mu nu gamma} := by
  apply isCompact_of_isClosed_of_mass_eq_of_isTightMeasureSet
    (isClosed_isFiniteCoupling mu nu)
  · exact fun _ hgamma =>
      mass_eq_source_of_isFiniteCoupling hgamma
  · apply isTightMeasureSet_isFiniteCoupling mu nu
    · exact isTightMeasureSet_singleton
    · exact isTightMeasureSet_singleton

theorem solution
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [BorelSpace E] [PolishSpace E]
    (mu nu : FiniteMeasure E) :
    IsCompact (Set.univ : Set (FiniteCoupling mu nu)) := by
  letI : CompactSpace (FiniteCoupling mu nu) :=
    isCompact_iff_compactSpace.mp
      (isCompact_isFiniteCoupling mu nu)
  exact isCompact_univ
