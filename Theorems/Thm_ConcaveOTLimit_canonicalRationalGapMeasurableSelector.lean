import Theorems.Thm_ConcaveOTLimit_fiberwiseImprovementSelection
import Theorems.Thm_ConcaveOTLimit_compactSectionMeasurableSelection

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped BoundedContinuousFunction ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-!
# Canonical rational-gap measurable selectors

The downstream localization argument uses one selector on one measurable,
non-null subset of one rational-gap bad set.  This file first records that
minimal interface.  It then packages the actual compact rational-gap fibers
in the common space of probability measures and isolates the missing
compact-section measurable-selection theorem.
-/

section OneGap

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]

/-- Exactly one selector on one measurable, non-null active set. -/
structure FiberwiseOneGapSelectionData
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (component : Kernel R (X × Y)) where
  gapIndex : Nat
  active : Set R
  activeMeasurable : MeasurableSet active
  activeFrequently :
    ∃ᶠ r in ae (sigma : Measure R), r ∈ active
  selector : R -> Measure (X × Y)
  selectorMeasurable : Measurable selector
  selectorSpec :
    ∀ r ∈ active,
      selector r ∈ fiberCouplingSet source target carrier r ∧
        fiberMeasureCost cost r (selector r) +
            fiberRationalImprovementGap gapIndex ≤
          fiberKernelCost cost component r

/-- Minimal measurable-selection input used by localization.  It is only
asked for components to which localization is actually applied. -/
def FiberwiseOneGapMeasurableSelectionPremise
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real) : Prop :=
  ∀ (component : Kernel R (X × Y)),
    IsMarkovKernel component ->
    (∀ᵐ r ∂(sigma : Measure R),
      component r ∈ fiberCouplingSet source target carrier r) ->
    (¬ ∀ᵐ r ∂(sigma : Measure R),
      IsMinimizerOn
        (fiberCouplingSet source target carrier r)
        (fiberMeasureCost cost r) (component r)) ->
    Nonempty
      (FiberwiseOneGapSelectionData
        sigma source target carrier cost component)

namespace FiberwiseOneGapSelectionData

variable
    {sigma : FiniteMeasure R}
    {source : Kernel R X} {target : Kernel R Y}
    {carrier : Set (R × (X × Y))}
    {cost : R × (X × Y) -> Real}
    {component : Kernel R (X × Y)}

def selectorKernel
    (data :
      FiberwiseOneGapSelectionData
        sigma source target carrier cost component) :
    Kernel R (X × Y) where
  toFun := data.selector
  measurable' := data.selectorMeasurable

@[simp]
theorem selectorKernel_apply
    (data :
      FiberwiseOneGapSelectionData
        sigma source target carrier cost component)
    (r : R) :
    data.selectorKernel r = data.selector r :=
  rfl

def replacement
    (data :
      FiberwiseOneGapSelectionData
        sigma source target carrier cost component) :
    Kernel R (X × Y) := by
  classical
  exact Kernel.piecewise
    data.activeMeasurable data.selectorKernel component

theorem replacement_apply_of_mem
    (data :
      FiberwiseOneGapSelectionData
        sigma source target carrier cost component)
    {r : R} (hr : r ∈ data.active) :
    data.replacement r = data.selector r := by
  classical
  rw [replacement, Kernel.piecewise_apply, if_pos hr]
  rfl

theorem replacement_apply_of_notMem
    (data :
      FiberwiseOneGapSelectionData
        sigma source target carrier cost component)
    {r : R} (hr : r ∉ data.active) :
    data.replacement r = component r := by
  classical
  rw [replacement, Kernel.piecewise_apply, if_neg hr]

theorem replacement_isMarkovKernel
    (data :
      FiberwiseOneGapSelectionData
        sigma source target carrier cost component)
    (hsource : IsMarkovKernel source)
    (hcomponent : IsMarkovKernel component) :
    IsMarkovKernel data.replacement := by
  constructor
  intro r
  by_cases hr : r ∈ data.active
  · rw [data.replacement_apply_of_mem hr]
    have hmap := (data.selectorSpec r hr).1.1
    constructor
    calc
      data.selector r univ =
          (data.selector r).map Prod.fst univ := by
            rw [Measure.map_apply measurable_fst MeasurableSet.univ]
            simp
      _ = source r univ := by rw [hmap]
      _ = 1 := (hsource.isProbabilityMeasure r).measure_univ
  · rw [data.replacement_apply_of_notMem hr]
    exact hcomponent.isProbabilityMeasure r

end FiberwiseOneGapSelectionData

/-- The one active-set selector is sufficient for the full replacement
kernel required by localization. -/
theorem fiberwiseImprovementSelectionPremise_of_oneGapSelection
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (hsource : IsMarkovKernel source)
    (hselection :
      FiberwiseOneGapMeasurableSelectionPremise
        sigma source target carrier cost) :
    FiberwiseImprovementSelectionPremise
      sigma source target carrier cost := by
  intro component hcomponent hfeasible hnot
  let data :=
    Classical.choice
      (hselection component hcomponent hfeasible hnot)
  let replacement := data.replacement
  have hreplacementMarkov :
      IsMarkovKernel replacement :=
    data.replacement_isMarkovKernel hsource hcomponent
  refine ⟨replacement, hreplacementMarkov, ?_, ?_, ?_⟩
  · filter_upwards [hfeasible] with r hrFeasible
    by_cases hr : r ∈ data.active
    · rw [show replacement r = data.selector r by
        exact data.replacement_apply_of_mem hr]
      exact (data.selectorSpec r hr).1
    · rw [show replacement r = component r by
        exact data.replacement_apply_of_notMem hr]
      exact hrFeasible
  · exact Eventually.of_forall fun r => by
      by_cases hr : r ∈ data.active
      · change
          fiberMeasureCost cost r (replacement r) ≤
            fiberMeasureCost cost r (component r)
        rw [show replacement r = data.selector r by
          exact data.replacement_apply_of_mem hr]
        exact
          (le_add_of_nonneg_right
            (fiberRationalImprovementGap_pos data.gapIndex).le).trans
            (data.selectorSpec r hr).2
      · change
          fiberMeasureCost cost r (replacement r) ≤
            fiberMeasureCost cost r (component r)
        rw [show replacement r = component r by
          exact data.replacement_apply_of_notMem hr]
  · intro heq
    obtain ⟨r, hrActive, hrEq⟩ :=
      (data.activeFrequently.and_eventually heq).exists
    have hstrict :
        fiberKernelCost cost replacement r <
          fiberKernelCost cost component r := by
      change
        fiberMeasureCost cost r (replacement r) <
          fiberMeasureCost cost r (component r)
      rw [show replacement r = data.selector r by
        exact data.replacement_apply_of_mem hrActive]
      have hgap := (data.selectorSpec r hrActive).2
      have hgapPos :=
        fiberRationalImprovementGap_pos data.gapIndex
      unfold fiberKernelCost at hgap
      linarith
    exact hstrict.ne hrEq

/-- The all-gaps interface from the preceding development implies the
minimal one-use interface.  The rational gap is chosen only after the
component is known to be feasible and nonminimal. -/
theorem fiberwiseOneGapMeasurableSelectionPremise_of_rationalGapSelection
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y)))
    (cost : R × (X × Y) -> Real)
    (hselection :
      FiberwiseRationalGapMeasurableSelectionPremise
        source target carrier cost) :
    FiberwiseOneGapMeasurableSelectionPremise
      sigma source target carrier cost := by
  intro component hcomponent hfeasible hnot
  obtain ⟨k, hkFrequently⟩ :=
    exists_frequently_fiberRationalGapBadSet_of_not_ae_minimizer
      source target carrier cost sigma component hfeasible hnot
  let data :=
    Classical.choice (hselection component hcomponent k)
  exact
    ⟨{
      gapIndex := k
      active :=
        fiberRationalGapBadSet
          source target carrier cost component k
      activeMeasurable := data.badMeasurable
      activeFrequently := hkFrequently
      selector := data.selector
      selectorMeasurable := data.selectorMeasurable
      selectorSpec := data.selectorSpec }⟩

end OneGap

section MeasurableMeasureEquality

open MeasurableSpace

variable {A E : Type*}
  [MeasurableSpace A] [MeasurableSpace E]
  [CountablyGenerated E]

omit [MeasurableSpace E] [CountablyGenerated E] in
private theorem antitone_memPartitionSet
    (f : Nat -> Set E) (x : E) :
    Antitone (fun n => memPartitionSet f n x) := by
  apply antitone_nat_of_succ_le
  intro n
  classical
  rw [memPartitionSet_succ]
  split_ifs
  · exact inter_subset_left
  · exact diff_subset

private theorem isPiSystem_iUnion_countablePartition :
    IsPiSystem (⋃ n, countablePartition E n) := by
  intro s hs t ht hst
  simp only [mem_iUnion] at hs ht ⊢
  obtain ⟨n, hsn⟩ := hs
  obtain ⟨m, htm⟩ := ht
  obtain ⟨x, hxs, hxt⟩ := hst
  have hsx : countablePartitionSet n x = s :=
    countablePartitionSet_of_mem hsn hxs
  have htx : countablePartitionSet m x = t :=
    countablePartitionSet_of_mem htm hxt
  rcases le_total n m with hnm | hmn
  · have hsub : t ⊆ s := by
      rw [← hsx, ← htx]
      exact antitone_memPartitionSet _ x hnm
    rw [inter_eq_right.mpr hsub]
    exact ⟨m, htm⟩
  · have hsub : s ⊆ t := by
      rw [← hsx, ← htx]
      exact antitone_memPartitionSet _ x hmn
    rw [inter_eq_left.mpr hsub]
    exact ⟨n, hsn⟩

private theorem measure_eq_of_countablePartition
    (mu nu : Measure E)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h :
      ∀ (n : Nat) (s : countablePartition E n),
        mu s = nu s) :
    mu = nu := by
  apply ext_of_generate_finite
    (⋃ n, countablePartition E n)
    (generateFrom_iUnion_countablePartition E).symm
    isPiSystem_iUnion_countablePartition
  · intro s hs
    simp only [mem_iUnion] at hs
    obtain ⟨n, hsn⟩ := hs
    exact h n ⟨s, hsn⟩
  · exact h 0 ⟨univ, by simp [countablePartition]⟩

/-- Equality of finite measure-valued measurable maps is measurable when
the measured space is countably generated. -/
theorem measurableSet_eq_finiteMeasure_fun
    (f g : A -> Measure E)
    (hf : Measurable f) (hg : Measurable g)
    (hfiniteF : ∀ a, IsFiniteMeasure (f a))
    (hfiniteG : ∀ a, IsFiniteMeasure (g a)) :
    MeasurableSet {a | f a = g a} := by
  have heq :
      {a | f a = g a} =
        ⋂ n : Nat, ⋂ s : countablePartition E n,
          {a | f a s = g a s} := by
    ext a
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro h n s
      rw [h]
    · intro h
      letI : IsFiniteMeasure (f a) := hfiniteF a
      letI : IsFiniteMeasure (g a) := hfiniteG a
      exact measure_eq_of_countablePartition
        (f a) (g a) fun n s => h n s
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun s =>
      measurableSet_eq_fun
        ((Measure.measurable_coe
          (measurableSet_countablePartition n s.property)).comp hf)
        ((Measure.measurable_coe
          (measurableSet_countablePartition n s.property)).comp hg)

end MeasurableMeasureEquality

section ProbabilityFibers

variable {n : Nat}

/-- A fixed-marginal coupling on one ray, regarded in the common space of
probability measures. -/
def fixedRayFiniteCouplingProbabilityMeasure
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n)
    (gamma :
      FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R)) :
    ProbabilityMeasure (Euclidean n × Euclidean n) :=
  ⟨gamma.plan, by
    constructor
    calc
      (gamma.plan : Measure (Euclidean n × Euclidean n)) univ =
          (gamma.plan : Measure (Euclidean n × Euclidean n)).map
            Prod.fst univ := by
              rw [Measure.map_apply measurable_fst MeasurableSet.univ]
              simp
      _ = source R univ := by
        have hmap :
            (gamma.plan :
                Measure (Euclidean n × Euclidean n)).map Prod.fst =
              source R := by
          simpa [firstMarginal, FiniteCoupling.plan] using congrArg
            (fun eta : FiniteMeasure (Euclidean n) =>
              (eta : Measure (Euclidean n))) gamma.property.1
        rw [hmap]
      _ = 1 := measure_univ⟩

@[simp]
theorem fixedRayFiniteCouplingProbabilityMeasure_toMeasure
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n)
    (gamma :
      FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R)) :
    (fixedRayFiniteCouplingProbabilityMeasure
        source target R gamma :
      Measure (Euclidean n × Euclidean n)) =
      gamma.plan :=
  rfl

theorem continuous_fixedRayFiniteCouplingProbabilityMeasure
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (R : OrientedOpenRay n) :
    Continuous
      (fixedRayFiniteCouplingProbabilityMeasure
        source target R) := by
  rw [continuous_induced_rng]
  simpa [Function.comp_def, FiniteCoupling.plan] using
    (continuous_subtype_val :
      Continuous
        (fun gamma :
            FiniteCoupling
              (markovKernelValueFiniteMeasure source R)
              (markovKernelValueFiniteMeasure target R) =>
          gamma.1))

/-- The actual rational-gap section in one common weak-topological and
Giry-measurable codomain. -/
def rayForwardRationalGapProbabilitySection
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    Set (ProbabilityMeasure (Euclidean n × Euclidean n)) :=
  {eta |
    (eta : Measure (Euclidean n × Euclidean n)) ∈
        fiberCouplingSet source target
          (rayForwardFiberCarrier n) R ∧
      fiberMeasureCost rayStrictExponentialFiberCost R
          (eta : Measure (Euclidean n × Euclidean n)) +
          fiberRationalImprovementGap k ≤
        fiberKernelCost
          rayStrictExponentialFiberCost component R}

/-- The graph whose sections are the common-codomain rational-gap
probability fibers. -/
def rayForwardRationalGapProbabilityGraph
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (k : Nat) :
    Set
      (OrientedOpenRay n ×
        ProbabilityMeasure (Euclidean n × Euclidean n)) :=
  {p |
    p.2 ∈ rayForwardRationalGapProbabilitySection
      source target component p.1 k}

theorem fixedRayFiniteCouplingProbabilityMeasure_mem_section
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat)
    (gamma :
      FiniteCoupling
        (markovKernelValueFiniteMeasure source R)
        (markovKernelValueFiniteMeasure target R))
    (hgamma :
      gamma ∈ fixedRayRationalGapFiniteCouplingSet
        source target component R k) :
    fixedRayFiniteCouplingProbabilityMeasure source target R gamma ∈
      rayForwardRationalGapProbabilitySection
        source target component R k := by
  refine ⟨?_, ?_⟩
  · exact fixedRayForwardFiniteCoupling_plan_mem_fiberCouplingSet
      source target R gamma hgamma.1
  · simpa [fixedRayFiniteCouplingCost, fiberMeasureCost] using hgamma.2

theorem exists_fixedRayRationalGapFiniteCoupling_of_mem_section
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat)
    (eta : ProbabilityMeasure (Euclidean n × Euclidean n))
    (heta :
      eta ∈ rayForwardRationalGapProbabilitySection
        source target component R k) :
    ∃ gamma :
        FiniteCoupling
          (markovKernelValueFiniteMeasure source R)
          (markovKernelValueFiniteMeasure target R),
      gamma ∈ fixedRayRationalGapFiniteCouplingSet
        source target component R k ∧
      fixedRayFiniteCouplingProbabilityMeasure
        source target R gamma = eta := by
  obtain ⟨gamma, hgammaForward, hplan⟩ :=
    exists_fixedRayForwardFiniteCoupling_of_mem_fiberCouplingSet
      source target R (eta : Measure (Euclidean n × Euclidean n))
        heta.1
  refine ⟨gamma, ⟨hgammaForward, ?_⟩, ?_⟩
  · simpa [fixedRayFiniteCouplingCost, fiberMeasureCost, hplan] using heta.2
  · apply ProbabilityMeasure.toMeasure_injective
    exact hplan

theorem rayForwardRationalGapProbabilitySection_eq_image
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    rayForwardRationalGapProbabilitySection
        source target component R k =
      fixedRayFiniteCouplingProbabilityMeasure source target R ''
        fixedRayRationalGapFiniteCouplingSet
          source target component R k := by
  ext eta
  constructor
  · intro heta
    obtain ⟨gamma, hgamma, rfl⟩ :=
      exists_fixedRayRationalGapFiniteCoupling_of_mem_section
        source target component R k eta heta
    exact ⟨gamma, hgamma, rfl⟩
  · rintro ⟨gamma, hgamma, rfl⟩
    exact fixedRayFiniteCouplingProbabilityMeasure_mem_section
      source target component R k gamma hgamma

/-- Each common-codomain rational-gap section is weakly compact. -/
theorem isCompact_rayForwardRationalGapProbabilitySection
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    IsCompact
      (rayForwardRationalGapProbabilitySection
        source target component R k) := by
  rw [rayForwardRationalGapProbabilitySection_eq_image]
  exact
    (isCompact_fixedRayRationalGapFiniteCouplingSet
      source target component R k).image
        (continuous_fixedRayFiniteCouplingProbabilityMeasure
          source target R)

theorem rayForwardRationalGapProbabilitySection_nonempty_iff
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    (rayForwardRationalGapProbabilitySection
        source target component R k).Nonempty ↔
      R ∈ fiberRationalGapBadSet
        source target (rayForwardFiberCarrier n)
          rayStrictExponentialFiberCost component k := by
  constructor
  · rintro ⟨eta, heta⟩
    exact ⟨(eta : Measure (Euclidean n × Euclidean n)),
      heta.1, heta.2⟩
  · rintro ⟨eta, hetaFeasible, hetaGap⟩
    obtain ⟨gamma, hgammaForward, hplan⟩ :=
      exists_fixedRayForwardFiniteCoupling_of_mem_fiberCouplingSet
        source target R eta hetaFeasible
    let rho :=
      fixedRayFiniteCouplingProbabilityMeasure source target R gamma
    refine ⟨rho, ?_⟩
    have hrho : (rho : Measure (Euclidean n × Euclidean n)) = eta := by
      exact hplan
    refine ⟨?_, ?_⟩
    · simpa [hrho] using hetaFeasible
    · simpa [hrho] using hetaGap

theorem rayForwardRationalGapProbabilityGraph_fiber
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) (k : Nat) :
    {eta |
      (R, eta) ∈ rayForwardRationalGapProbabilityGraph
        source target component k} =
      rayForwardRationalGapProbabilitySection
        source target component R k :=
  rfl

end ProbabilityFibers

section ProbabilityGraphMeasurable

variable {A E : Type*}
  [MeasurableSpace A] [MeasurableSpace E]

/-- Evaluation of the probability-measure coordinate as a Markov kernel. -/
def probabilityMeasureEvaluationKernel :
    Kernel (A × ProbabilityMeasure E) E where
  toFun p := (p.2 : Measure E)
  measurable' := measurable_subtype_coe.comp measurable_snd

@[simp]
theorem probabilityMeasureEvaluationKernel_apply
    (p : A × ProbabilityMeasure E) :
    probabilityMeasureEvaluationKernel p = (p.2 : Measure E) :=
  rfl

theorem probabilityMeasureEvaluationKernel_isMarkovKernel :
    IsMarkovKernel
      (probabilityMeasureEvaluationKernel :
        Kernel (A × ProbabilityMeasure E) E) := by
  constructor
  intro p
  exact p.2.property

variable {F : Type*} [MeasurableSpace F]
  [MeasurableSpace.CountablyGenerated F]

private theorem measurableSet_probabilityMeasure_map_eq_kernel
    (f : E -> F) (hf : Measurable f)
    (kernel : Kernel A F) [IsMarkovKernel kernel] :
    MeasurableSet
      {p : A × ProbabilityMeasure E |
        (p.2 : Measure E).map f = kernel p.1} := by
  apply measurableSet_eq_finiteMeasure_fun
    (fun p : A × ProbabilityMeasure E =>
      (p.2 : Measure E).map f)
    (fun p : A × ProbabilityMeasure E => kernel p.1)
  · exact (Measure.measurable_map f hf).comp
      (measurable_subtype_coe.comp measurable_snd)
  · exact kernel.measurable.comp measurable_fst
  · intro p
    letI : IsProbabilityMeasure ((p.2 : Measure E).map f) :=
      Measure.isProbabilityMeasure_map hf.aemeasurable
    infer_instance
  · intro p
    letI : IsProbabilityMeasure (kernel p.1) :=
      IsMarkovKernel.isProbabilityMeasure p.1
    infer_instance

end ProbabilityGraphMeasurable

section RayProbabilityGraphMeasurable

variable {n : Nat}

/-- The rational-gap graph is measurable in the product of the ray Borel
space and the Giry measurable space on probability measures. -/
theorem measurableSet_rayForwardRationalGapProbabilityGraph
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    [IsMarkovKernel component]
    (k : Nat) :
    MeasurableSet
      (rayForwardRationalGapProbabilityGraph
        source target component k) := by
  let Q :=
    OrientedOpenRay n ×
      ProbabilityMeasure (Euclidean n × Euclidean n)
  let evaluation :
      Kernel Q (Euclidean n × Euclidean n) :=
    probabilityMeasureEvaluationKernel
  letI : IsMarkovKernel evaluation :=
    probabilityMeasureEvaluationKernel_isMarkovKernel
  have hFirst :
      MeasurableSet
        {p : Q |
          (p.2 : Measure (Euclidean n × Euclidean n)).map
              Prod.fst =
            source p.1} :=
    measurableSet_probabilityMeasure_map_eq_kernel
      (A := OrientedOpenRay n)
      (E := Euclidean n × Euclidean n)
      (F := Euclidean n)
      Prod.fst measurable_fst source
  have hSecond :
      MeasurableSet
        {p : Q |
          (p.2 : Measure (Euclidean n × Euclidean n)).map
              Prod.snd =
            target p.1} :=
    measurableSet_probabilityMeasure_map_eq_kernel
      (A := OrientedOpenRay n)
      (E := Euclidean n × Euclidean n)
      (F := Euclidean n)
      Prod.snd measurable_snd target
  have hForwardSet :
      MeasurableSet
        {q : Q × (Euclidean n × Euclidean n) |
          (q.1.1, q.2) ∈ rayForwardFiberCarrier n} := by
    exact (measurableSet_rayForwardFiberCarrier n).preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hForwardMeasure :
      Measurable
        (fun p : Q =>
          evaluation p
            {z |
              (p.1, z) ∉ rayForwardFiberCarrier n}) := by
    have h :=
      Kernel.measurable_kernel_prodMk_left
        (κ := evaluation) hForwardSet.compl
    simpa only [evaluation,
      probabilityMeasureEvaluationKernel_apply,
      mem_preimage, mem_compl_iff, mem_setOf_eq] using h
  have hSupport :
      MeasurableSet
        {p : Q |
          ∀ᵐ z ∂(p.2 : Measure (Euclidean n × Euclidean n)),
            (p.1, z) ∈ rayForwardFiberCarrier n} := by
    have hzero :=
      measurableSet_eq_fun hForwardMeasure
        (measurable_const :
          Measurable
            (fun _ : Q => (0 : ENNReal)))
    simpa only [ae_iff] using hzero
  have hSelectedCost :
      Measurable
        (fun p : Q =>
          fiberMeasureCost rayStrictExponentialFiberCost p.1
            (p.2 : Measure (Euclidean n × Euclidean n))) := by
    have hintegrand :
        StronglyMeasurable
          (fun q : Q × (Euclidean n × Euclidean n) =>
            rayStrictExponentialFiberCost (q.1.1, q.2)) :=
      stronglyMeasurable_rayStrictExponentialFiberCost.comp_measurable
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    simpa only [fiberMeasureCost, evaluation,
      probabilityMeasureEvaluationKernel_apply] using
        (hintegrand.integral_kernel_prod_right'
          (κ := evaluation)).measurable
  have hComponentCost :
      Measurable
        (fiberKernelCost
          rayStrictExponentialFiberCost component) := by
    simpa only [fiberKernelCost, fiberMeasureCost] using
      ((stronglyMeasurable_rayStrictExponentialFiberCost
        (n := n)).integral_kernel_prod_right'
          (κ := component)).measurable
  have hGap :
      MeasurableSet
        {p : Q |
          fiberMeasureCost rayStrictExponentialFiberCost p.1
              (p.2 : Measure (Euclidean n × Euclidean n)) +
              fiberRationalImprovementGap k ≤
            fiberKernelCost
              rayStrictExponentialFiberCost component p.1} :=
    measurableSet_le
      (hSelectedCost.add measurable_const)
      (hComponentCost.comp measurable_fst)
  simpa only [rayForwardRationalGapProbabilityGraph,
    rayForwardRationalGapProbabilitySection,
    fiberCouplingSet, mem_setOf_eq] using
      (hFirst.inter (hSecond.inter hSupport)).inter hGap

end RayProbabilityGraphMeasurable

section RaySelectionFromCompactSections

variable {n : Nat}

/-- Applying the compact-section bridge to one actual rational-gap graph
produces exactly the Giry-measurable data used by the replacement proof. -/
theorem rayForwardRationalGapSelectionData_of_compactSectionSelection
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (component :
      Kernel (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    [IsMarkovKernel component]
    (k : Nat)
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    Nonempty
      (FiberwiseRationalGapSelectionData
        source target (rayForwardFiberCarrier n)
          rayStrictExponentialFiberCost component k) := by
  let graph :=
    rayForwardRationalGapProbabilityGraph
      source target component k
  obtain ⟨selector, hselectorMeasurable, hdomainMeasurable,
      hselectorSpec⟩ :=
    hselection graph
      (measurableSet_rayForwardRationalGapProbabilityGraph
        source target component k)
      (fun R => by
        simpa only [graph,
          rayForwardRationalGapProbabilityGraph_fiber] using
          isCompact_rayForwardRationalGapProbabilitySection
            source target component R k)
  have hbad :
      fiberRationalGapBadSet source target
          (rayForwardFiberCarrier n)
          rayStrictExponentialFiberCost component k =
        {R : OrientedOpenRay n |
          {eta : ProbabilityMeasure (Euclidean n × Euclidean n) |
            (R, eta) ∈ graph}.Nonempty} := by
    ext R
    simpa only [mem_setOf_eq, graph,
      rayForwardRationalGapProbabilityGraph_fiber] using
      (rayForwardRationalGapProbabilitySection_nonempty_iff
        source target component R k).symm
  refine
    ⟨{
      badMeasurable := hbad ▸ hdomainMeasurable
      selector := fun R => (selector R :
        Measure (Euclidean n × Euclidean n))
      selectorMeasurable :=
        measurable_subtype_coe.comp hselectorMeasurable
      selectorSpec := ?_ }⟩
  intro R hR
  have hnonempty :
      {eta : ProbabilityMeasure (Euclidean n × Euclidean n) |
        (R, eta) ∈ graph}.Nonempty := by
    change
      R ∈
        {R : OrientedOpenRay n |
          {eta : ProbabilityMeasure (Euclidean n × Euclidean n) |
            (R, eta) ∈ graph}.Nonempty}
    rw [← hbad]
    exact hR
  have hmem := hselectorSpec R hnonempty
  simpa only [graph,
    rayForwardRationalGapProbabilityGraph,
    rayForwardRationalGapProbabilitySection,
    mem_setOf_eq] using hmem

/-- The one generic compact-section theorem yields the existing all-gaps
ray-forward selector interface. -/
theorem rayForwardRationalGapMeasurableSelectionPremise_of_compactSectionSelection
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    RayForwardRationalGapMeasurableSelectionPremise source target := by
  intro component hcomponent k
  letI : IsMarkovKernel component := hcomponent
  exact
    rayForwardRationalGapSelectionData_of_compactSectionSelection
      source target component k hselection

/-- Minimal ray-forward interface: one selector at one frequent rational
gap, requested only for the component used by localization. -/
def RayForwardOneGapMeasurableSelectionPremise
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n)) : Prop :=
  FiberwiseOneGapMeasurableSelectionPremise
    sigma source target (rayForwardFiberCarrier n)
      rayStrictExponentialFiberCost

/-- The compact-section theorem is invoked only after a frequent gap has
been extracted, so this proof constructs one selector rather than a family
of selectors. -/
theorem rayForwardOneGapMeasurableSelectionPremise_of_compactSectionSelection
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    RayForwardOneGapMeasurableSelectionPremise sigma source target := by
  intro component hcomponent hfeasible hnot
  obtain ⟨k, hkFrequently⟩ :=
    exists_frequently_fiberRationalGapBadSet_of_not_ae_minimizer
      source target (rayForwardFiberCarrier n)
        rayStrictExponentialFiberCost sigma component hfeasible hnot
  letI : IsMarkovKernel component := hcomponent
  let data :=
    Classical.choice
      (rayForwardRationalGapSelectionData_of_compactSectionSelection
        source target component k hselection)
  exact
    ⟨{
      gapIndex := k
      active :=
        fiberRationalGapBadSet source target
          (rayForwardFiberCarrier n)
          rayStrictExponentialFiberCost component k
      activeMeasurable := data.badMeasurable
      activeFrequently := hkFrequently
      selector := data.selector
      selectorMeasurable := data.selectorMeasurable
      selectorSpec := data.selectorSpec }⟩

/-- Direct downstream improvement premise from the one-use compact-section
selector construction. -/
theorem rayForwardFiberwiseImprovementSelectionPremise_of_compactSectionSelection
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    RayForwardFiberwiseImprovementSelectionPremise sigma source target :=
  fiberwiseImprovementSelectionPremise_of_oneGapSelection
    sigma source target (rayForwardFiberCarrier n)
      rayStrictExponentialFiberCost
      (inferInstance : IsMarkovKernel source)
      (rayForwardOneGapMeasurableSelectionPremise_of_compactSectionSelection
        sigma source target hselection)

namespace MaximalRayKernelDisintegration

variable
  {mu nu : FiniteMeasure (Euclidean n)}
  {Gamma : Set (Euclidean n × Euclidean n)}

/-- Canonical specialization of the exact one-selector interface. -/
def CanonicalRayForwardOneGapMeasurableSelectionPremise
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu) : Prop :=
  RayForwardOneGapMeasurableSelectionPremise
    D.sigma D.source (D.canonicalTarget gamma0)

/-- The generic compact-section theorem supplies the original canonical
all-gaps premise.  All graph, compactness, and Giry conversion obligations
have been discharged above. -/
theorem canonicalRayForwardRationalGapMeasurableSelectionPremise_of_compactSectionSelection
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu)
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    CanonicalRayForwardRationalGapMeasurableSelectionPremise D gamma0 := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.canonicalTarget gamma0) :=
    D.canonicalTarget_isMarkovKernel gamma0
  exact
    rayForwardRationalGapMeasurableSelectionPremise_of_compactSectionSelection
      D.source (D.canonicalTarget gamma0) hselection

/-- Canonical rational-gap measurable selection, with the compact-section
selection theorem discharged for the oriented-ray probability graph. -/
theorem canonicalRayForwardRationalGapMeasurableSelectionPremise
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu) :
    CanonicalRayForwardRationalGapMeasurableSelectionPremise D gamma0 :=
  canonicalRayForwardRationalGapMeasurableSelectionPremise_of_compactSectionSelection
    D gamma0
    (CompactSectionMeasurableSelection.compactSectionMeasurableSelectionPremise_orientedOpenRay_probabilityMeasure
      n)

/-- The same bridge supplies the minimized canonical premise while invoking
selection at just the one gap extracted from nonminimality. -/
theorem canonicalRayForwardOneGapMeasurableSelectionPremise_of_compactSectionSelection
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu)
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    CanonicalRayForwardOneGapMeasurableSelectionPremise D gamma0 := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.canonicalTarget gamma0) :=
    D.canonicalTarget_isMarkovKernel gamma0
  exact
    rayForwardOneGapMeasurableSelectionPremise_of_compactSectionSelection
      D.sigma D.source (D.canonicalTarget gamma0) hselection

/-- Canonical downstream improvement selection with only the generic
compact-section measurable-selection theorem left as an input. -/
theorem canonicalRayForwardFiberwiseImprovementSelectionPremise_of_compactSectionSelection
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma0 : FiniteCoupling mu nu)
    (hselection :
      CompactSectionMeasurableSelectionPremise
        (OrientedOpenRay n)
        (ProbabilityMeasure (Euclidean n × Euclidean n))) :
    RayForwardFiberwiseImprovementSelectionPremise
      D.sigma D.source (D.canonicalTarget gamma0) := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.canonicalTarget gamma0) :=
    D.canonicalTarget_isMarkovKernel gamma0
  exact
    fiberwiseImprovementSelectionPremise_of_oneGapSelection
      D.sigma D.source (D.canonicalTarget gamma0)
      (rayForwardFiberCarrier n) rayStrictExponentialFiberCost
      (inferInstance : IsMarkovKernel D.source)
      (canonicalRayForwardOneGapMeasurableSelectionPremise_of_compactSectionSelection
        D gamma0 hselection)

end MaximalRayKernelDisintegration

end RaySelectionFromCompactSections

end ConcaveOTLimit
