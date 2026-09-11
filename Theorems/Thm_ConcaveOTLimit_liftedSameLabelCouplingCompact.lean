import Theorems.Thm_ConcaveOTLimit_finiteCouplingIsCompact
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Semicontinuity.Basic

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace ConcaveOTLimit

private theorem mass_firstMarginal_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (gamma : FiniteMeasure (A × B)) :
    (firstMarginal gamma).mass = gamma.mass := by
  simp [firstMarginal, FiniteMeasure.mass,
    FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ]

private theorem mass_eq_source_of_isFiniteCoupling_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : FiniteMeasure A} {nu : FiniteMeasure B}
    {gamma : FiniteMeasure (A × B)}
    (hgamma : IsFiniteCoupling mu nu gamma) :
    gamma.mass = mu.mass := by
  rw [← mass_firstMarginal_heterogeneous gamma, hgamma.1]

private theorem continuous_firstMarginal_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [OpensMeasurableSpace (A × B)] [BorelSpace A] :
    Continuous
      (firstMarginal :
        FiniteMeasure (A × B) -> FiniteMeasure A) := by
  change Continuous
    (fun gamma : FiniteMeasure (A × B) => gamma.map Prod.fst)
  exact FiniteMeasure.continuous_map continuous_fst

private theorem continuous_secondMarginal_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [OpensMeasurableSpace (A × B)] [BorelSpace B] :
    Continuous
      (secondMarginal :
        FiniteMeasure (A × B) -> FiniteMeasure B) := by
  change Continuous
    (fun gamma : FiniteMeasure (A × B) => gamma.map Prod.snd)
  exact FiniteMeasure.continuous_map continuous_snd

private theorem isClosed_isFiniteCoupling_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [OpensMeasurableSpace (A × B)]
    [BorelSpace A] [BorelSpace B]
    [HasOuterApproxClosed A] [HasOuterApproxClosed B]
    (mu : FiniteMeasure A) (nu : FiniteMeasure B) :
    IsClosed
      {gamma : FiniteMeasure (A × B) |
        IsFiniteCoupling mu nu gamma} := by
  simpa only [IsFiniteCoupling, setOf_and] using
    (isClosed_eq continuous_firstMarginal_heterogeneous continuous_const).inter
      (isClosed_eq continuous_secondMarginal_heterogeneous continuous_const)

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

private theorem isTightMeasureSet_isFiniteCoupling_heterogeneous
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [T2Space A] [T2Space B] [BorelSpace A] [BorelSpace B]
    (mu : FiniteMeasure A) (nu : FiniteMeasure B)
    (hmu : IsTightMeasureSet {(mu : Measure A)})
    (hnu : IsTightMeasureSet {(nu : Measure B)}) :
    IsTightMeasureSet
      ((fun gamma : FiniteMeasure (A × B) =>
          (gamma : Measure (A × B))) ''
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
  have hmuBound : (mu : Measure A) Kᶜ ≤ epsilon / 2 :=
    hmuK (mu : Measure A) (mem_singleton (mu : Measure A))
  have hnuBound : (nu : Measure B) Lᶜ ≤ epsilon / 2 :=
    hnuL (nu : Measure B) (mem_singleton (nu : Measure B))
  rw [compl_prod_eq_union, prod_univ, univ_prod]
  calc
    (gamma : Measure (A × B))
        (Prod.fst ⁻¹' Kᶜ ∪ Prod.snd ⁻¹' Lᶜ) ≤
        (gamma : Measure (A × B)) (Prod.fst ⁻¹' Kᶜ) +
          (gamma : Measure (A × B)) (Prod.snd ⁻¹' Lᶜ) :=
      measure_union_le _ _
    _ = (firstMarginal gamma : Measure A) Kᶜ +
          (secondMarginal gamma : Measure B) Lᶜ := by
      simp only [firstMarginal, secondMarginal,
        FiniteMeasure.toMeasure_map]
      rw [Measure.map_apply measurable_fst hK.measurableSet.compl,
        Measure.map_apply measurable_snd hL.measurableSet.compl]
    _ = (mu : Measure A) Kᶜ + (nu : Measure B) Lᶜ := by
      rw [hgamma.1, hgamma.2]
    _ ≤ epsilon / 2 + epsilon / 2 :=
      add_le_add hmuBound hnuBound
    _ = epsilon := ENNReal.add_halves epsilon

private theorem isCompact_isFiniteCoupling_heterogeneous
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [BorelSpace A] [BorelSpace B] [PolishSpace A] [PolishSpace B]
    (mu : FiniteMeasure A) (nu : FiniteMeasure B) :
    IsCompact
      {gamma : FiniteMeasure (A × B) |
        IsFiniteCoupling mu nu gamma} := by
  apply isCompact_of_isClosed_of_mass_eq_of_isTightMeasureSet
    (isClosed_isFiniteCoupling_heterogeneous mu nu)
  · exact fun _ hgamma =>
      mass_eq_source_of_isFiniteCoupling_heterogeneous hgamma
  · apply isTightMeasureSet_isFiniteCoupling_heterogeneous mu nu
    · exact isTightMeasureSet_singleton
    · exact isTightMeasureSet_singleton

/-- Finite couplings between fixed finite measures on two possibly different
Polish Borel spaces form a compact space for the inherited weak topology. -/
theorem finiteCouplingIsCompactHeterogeneous
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [BorelSpace A] [BorelSpace B] [PolishSpace A] [PolishSpace B]
    (mu : FiniteMeasure A) (nu : FiniteMeasure B) :
    IsCompact (Set.univ : Set (FiniteCoupling mu nu)) := by
  letI : CompactSpace (FiniteCoupling mu nu) :=
    isCompact_iff_compactSpace.mp
      (isCompact_isFiniteCoupling_heterogeneous mu nu)
  exact isCompact_univ

private theorem measurePreservingFst_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : FiniteMeasure A} {nu : FiniteMeasure B}
    (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (A × B)) (mu : Measure A) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure A => (eta : Measure A)) gamma.property.1

private theorem planUnivEqSourceUniv_heterogeneous
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : FiniteMeasure A} {nu : FiniteMeasure B}
    (gamma : FiniteCoupling mu nu) :
    (gamma.plan : Measure (A × B)) univ =
      (mu : Measure A) univ := by
  calc
    (gamma.plan : Measure (A × B)) univ =
        Measure.map Prod.fst
          (gamma.plan : Measure (A × B)) univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = (mu : Measure A) univ := by
      rw [(measurePreservingFst_heterogeneous gamma).map_eq]

/-- Requiring a fixed-marginal finite coupling to be carried by a closed set
is a weakly closed condition. -/
theorem isClosed_finiteCouplingSupportedOnClosed
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [BorelSpace A] [BorelSpace B] [PolishSpace A] [PolishSpace B]
    {mu : FiniteMeasure A} {nu : FiniteMeasure B}
    {carrier : Set (A × B)} (hcarrier : IsClosed carrier) :
    IsClosed
      {gamma : FiniteCoupling mu nu | IsSupported gamma carrier} := by
  rw [isClosed_iff_forall_filter]
  intro gamma L hLNontrivial hLSupported hLGamma
  letI : NeBot L := hLNontrivial
  have hEventuallySupported :
      ∀ᶠ eta in L, IsSupported eta carrier := by
    apply hLSupported
    simp
  have hPlanTendsto :
      Tendsto (fun eta : FiniteCoupling mu nu => eta.plan)
        L (nhds gamma.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val.tendsto gamma).mono_left hLGamma
  have hPortmanteau :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto
      hPlanTendsto hcarrier
  have hEventuallyMass :
      ∀ᶠ eta in L,
        (eta.plan : Measure (A × B)) carrier =
          (mu : Measure A) univ := by
    filter_upwards [hEventuallySupported] with eta hEta
    calc
      (eta.plan : Measure (A × B)) carrier =
          (eta.plan : Measure (A × B)) univ :=
        (ae_mem_iff_measure_eq
          hcarrier.measurableSet.nullMeasurableSet).mp hEta
      _ = (mu : Measure A) univ :=
        planUnivEqSourceUniv_heterogeneous eta
  have hMassLe :
      (mu : Measure A) univ <=
        (gamma.plan : Measure (A × B)) carrier := by
    calc
      (mu : Measure A) univ =
          L.limsup
            (fun _eta : FiniteCoupling mu nu =>
              (mu : Measure A) univ) := by
        simp only [limsup_const]
      _ = L.limsup
            (fun eta : FiniteCoupling mu nu =>
              (eta.plan : Measure (A × B)) carrier) :=
        (limsup_congr hEventuallyMass).symm
      _ <= (gamma.plan : Measure (A × B)) carrier :=
        hPortmanteau
  apply
    (ae_mem_iff_measure_eq
      hcarrier.measurableSet.nullMeasurableSet).mpr
  apply le_antisymm (measure_mono (subset_univ carrier))
  calc
    (gamma.plan : Measure (A × B)) univ =
        (mu : Measure A) univ :=
      planUnivEqSourceUniv_heterogeneous gamma
    _ <= (gamma.plan : Measure (A × B)) carrier := hMassLe

/-- Fixed-marginal finite couplings carried by a closed set form a compact
subset of the coupling space. -/
theorem isCompact_finiteCouplingSupportedOnClosed
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [TopologicalSpace A] [TopologicalSpace B]
    [BorelSpace A] [BorelSpace B] [PolishSpace A] [PolishSpace B]
    (mu : FiniteMeasure A) (nu : FiniteMeasure B)
    {carrier : Set (A × B)} (hcarrier : IsClosed carrier) :
    IsCompact
      {gamma : FiniteCoupling mu nu | IsSupported gamma carrier} := by
  simpa only [univ_inter] using
    (finiteCouplingIsCompactHeterogeneous mu nu).inter_right
      (isClosed_finiteCouplingSupportedOnClosed hcarrier)

/-- Pairs of lifted source and target points whose explicit labels agree. -/
def liftedSameLabelRelation (R X Y : Type*) :
    Set ((R × X) × (R × Y)) :=
  {z | z.1.1 = z.2.1}

/-- The lifted same-label relation is closed when the label space is
Hausdorff. -/
theorem isClosed_liftedSameLabelRelation
    {R X Y : Type*}
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space R] :
    IsClosed (liftedSameLabelRelation R X Y) := by
  simpa only [liftedSameLabelRelation] using
    isClosed_eq
      (continuous_fst.comp continuous_fst)
      (continuous_fst.comp continuous_snd)

/-- Finite lifted couplings with prescribed marginals that are carried by
pairs having the same explicit label. -/
def liftedSameLabelCouplingSet
    {R X Y : Type*}
    [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
    (alpha : FiniteMeasure (R × X)) (beta : FiniteMeasure (R × Y)) :
    Set (FiniteCoupling alpha beta) :=
  {gamma | IsSupported gamma (liftedSameLabelRelation R X Y)}

/-- The lifted same-label coupling subset is weakly closed. -/
theorem isClosed_liftedSameLabelCouplingSet
    {R X Y : Type*}
    [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [BorelSpace R] [BorelSpace X] [BorelSpace Y]
    [PolishSpace R] [PolishSpace X] [PolishSpace Y]
    (alpha : FiniteMeasure (R × X)) (beta : FiniteMeasure (R × Y)) :
    IsClosed (liftedSameLabelCouplingSet alpha beta) := by
  exact isClosed_finiteCouplingSupportedOnClosed
    (isClosed_liftedSameLabelRelation (R := R) (X := X) (Y := Y))

/-- The lifted same-label coupling subset is compact. -/
theorem isCompact_liftedSameLabelCouplingSet
    {R X Y : Type*}
    [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [BorelSpace R] [BorelSpace X] [BorelSpace Y]
    [PolishSpace R] [PolishSpace X] [PolishSpace Y]
    (alpha : FiniteMeasure (R × X)) (beta : FiniteMeasure (R × Y)) :
    IsCompact (liftedSameLabelCouplingSet alpha beta) := by
  exact isCompact_finiteCouplingSupportedOnClosed alpha beta
    (isClosed_liftedSameLabelRelation (R := R) (X := X) (Y := Y))

/-- A supplied lifted same-label coupling witnesses that the compact
constraint set is nonempty. -/
theorem liftedSameLabelCouplingSet_nonempty
    {R X Y : Type*}
    [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
    {alpha : FiniteMeasure (R × X)} {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta)
    (hgamma :
      IsSupported gamma (liftedSameLabelRelation R X Y)) :
    (liftedSameLabelCouplingSet alpha beta).Nonempty := by
  exact ⟨gamma, hgamma⟩

/-- A real-valued lower-semicontinuous cost attains its minimum on the
nonempty compact set of lifted same-label couplings. -/
theorem existsLiftedSameLabelCouplingMinimizerOfLowerSemicontinuous
    {R X Y : Type*}
    [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [BorelSpace R] [BorelSpace X] [BorelSpace Y]
    [PolishSpace R] [PolishSpace X] [PolishSpace Y]
    {alpha : FiniteMeasure (R × X)} {beta : FiniteMeasure (R × Y)}
    (gammaSameLabel : FiniteCoupling alpha beta)
    (hSameLabel :
      IsSupported gammaSameLabel (liftedSameLabelRelation R X Y))
    (cost : FiniteCoupling alpha beta -> Real)
    (hCost :
      LowerSemicontinuousOn cost
        (liftedSameLabelCouplingSet alpha beta)) :
    ∃ gamma : FiniteCoupling alpha beta,
      IsMinimizerOn
        (liftedSameLabelCouplingSet alpha beta) cost gamma := by
  have hNonempty :
      (liftedSameLabelCouplingSet alpha beta).Nonempty :=
    liftedSameLabelCouplingSet_nonempty gammaSameLabel hSameLabel
  obtain ⟨gamma, hgamma, hgammaMin⟩ :=
    hCost.exists_isMinOn hNonempty
      (isCompact_liftedSameLabelCouplingSet alpha beta)
  exact ⟨gamma, hgamma, hgammaMin⟩

end ConcaveOTLimit
