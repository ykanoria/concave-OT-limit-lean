import Theorems.Thm_ConcaveOTLimit_liftedSameLabelKernelMinimizer
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-!
# Localizing a lifted kernel minimizer

The only genuinely nonformal input in the localization argument is the
measurable choice of improving fiber couplings.  This file packages that
input as `FiberwiseImprovementSelectionPremise` and proves everything after
it: a measurable positive-measure replacement contradicts global minimality.
-/

section FiberCarrier

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]

/-- A carrier on labeled, but unlifted, source-target pairs. -/
def liftedFiberCarrier (carrier : Set (R × (X × Y))) :
    Set ((R × X) × (R × Y)) :=
  {z |
    z.1.1 = z.2.1 ∧
      (z.1.1, (z.1.2, z.2.2)) ∈ carrier}

theorem measurableSet_liftedFiberCarrier
    [MeasurableEq R]
    {carrier : Set (R × (X × Y))}
    (hcarrier : MeasurableSet carrier) :
    MeasurableSet (liftedFiberCarrier carrier) := by
  exact
    (measurableSet_eq_fun
      (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)).inter
      (hcarrier.preimage (by fun_prop))

/-- Couplings of the two conditional marginals carried by one labeled
fiber.  The ambient type is `Measure`, so a kernel value can be used
directly; the first marginal identity already forces unit mass. -/
def fiberCouplingSet
    (source : Kernel R X) (target : Kernel R Y)
    (carrier : Set (R × (X × Y))) (r : R) :
    Set (Measure (X × Y)) :=
  {eta |
    eta.map Prod.fst = source r ∧
      eta.map Prod.snd = target r ∧
      ∀ᵐ z ∂eta, (r, z) ∈ carrier}

/-- The integral objective on one conditional coupling. -/
def fiberMeasureCost
    (cost : R × (X × Y) -> Real)
    (r : R) (eta : Measure (X × Y)) : Real :=
  ∫ z, cost (r, z) ∂eta

/-- The conditional cost of a component kernel. -/
def fiberKernelCost
    (cost : R × (X × Y) -> Real)
    (component : Kernel R (X × Y)) (r : R) : Real :=
  fiberMeasureCost cost r (component r)

/-- Evaluate a fiber cost on a lifted pair, using its first copied label. -/
def liftedFiberPointCost
    (cost : R × (X × Y) -> Real)
    (z : (R × X) × (R × Y)) : Real :=
  cost (z.1.1, (z.1.2, z.2.2))

/-- The integral objective on a lifted coupling. -/
def liftedFiberIntegralCost
    {alpha : FiniteMeasure (R × X)}
    {beta : FiniteMeasure (R × Y)}
    (cost : R × (X × Y) -> Real)
    (gamma : FiniteCoupling alpha beta) : Real :=
  ∫ z, liftedFiberPointCost cost z
    ∂(gamma.plan : Measure ((R × X) × (R × Y)))

/-- Lifted couplings carried by equal-label copies of a fiber carrier. -/
def liftedFiberCouplingSet
    (alpha : FiniteMeasure (R × X))
    (beta : FiniteMeasure (R × Y))
    (carrier : Set (R × (X × Y))) :
    Set (FiniteCoupling alpha beta) :=
  {gamma | IsSupported gamma (liftedFiberCarrier carrier)}

theorem stronglyMeasurable_liftedFiberPointCost
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost) :
    StronglyMeasurable (liftedFiberPointCost cost) := by
  exact hcost.comp_measurable (by fun_prop)

theorem integrable_cost_compProd_of_bound
    (sigma : FiniteMeasure R)
    (component : Kernel R (X × Y))
    [IsMarkovKernel component]
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost)
    (bound : Real)
    (hbound : ∀ p, ‖cost p‖ ≤ bound) :
    Integrable cost ((sigma : Measure R) ⊗ₘ component) := by
  exact Integrable.of_bound hcost.aestronglyMeasurable bound
    (ae_of_all _ hbound)

theorem integrable_fiberKernelCost_of_bound
    (sigma : FiniteMeasure R)
    (component : Kernel R (X × Y))
    [IsMarkovKernel component]
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost)
    (bound : Real)
    (hbound : ∀ p, ‖cost p‖ ≤ bound) :
    Integrable (fiberKernelCost cost component) (sigma : Measure R) := by
  have hComp :
      Integrable cost ((sigma : Measure R) ⊗ₘ component) :=
    integrable_cost_compProd_of_bound sigma component hcost bound hbound
  have hNorm :
      Integrable
        (fun r => ∫ z, ‖cost (r, z)‖ ∂component r)
        (sigma : Measure R) :=
    (Measure.integrable_compProd_iff hcost.aestronglyMeasurable).mp hComp |>.2
  apply Integrable.mono hNorm
    (hcost.integral_kernel_prod_right').aestronglyMeasurable
  filter_upwards with r
  calc
    ‖∫ z, cost (r, z) ∂component r‖ ≤
        ∫ z, ‖cost (r, z)‖ ∂component r :=
      norm_integral_le_integral_norm _
    _ = ‖∫ z, ‖cost (r, z)‖ ∂component r‖ := by
      rw [Real.norm_of_nonneg]
      exact integral_nonneg fun _ => norm_nonneg _

/-- Fubini plus the definition of the lifted component map: the global
cost of a component plan is the integral of its conditional costs. -/
theorem liftedFiberIntegralCost_liftedComponentCoupling
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost)
    (bound : Real)
    (hbound : ∀ p, ‖cost p‖ ≤ bound) :
    liftedFiberIntegralCost cost
        (liftedComponentCoupling sigma source target component
          hsource htarget) =
      ∫ r, fiberKernelCost cost component r ∂(sigma : Measure R) := by
  have hComp :
      Integrable cost ((sigma : Measure R) ⊗ₘ component) :=
    integrable_cost_compProd_of_bound sigma component hcost bound hbound
  rw [liftedFiberIntegralCost, liftedComponentCoupling_plan,
    liftedComponentPlan_toMeasure]
  rw [integral_map measurable_liftedComponentMap.aemeasurable
    (stronglyMeasurable_liftedFiberPointCost hcost).aestronglyMeasurable]
  change
    (∫ p, cost p ∂((sigma : Measure R) ⊗ₘ component)) =
      ∫ r, fiberKernelCost cost component r ∂(sigma : Measure R)
  exact Measure.integral_compProd hComp

theorem component_mem_fiberCouplingSet_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    (carrier : Set (R × (X × Y)))
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    (hcarrier :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂component r, (r, z) ∈ carrier) :
    ∀ᵐ r ∂(sigma : Measure R),
      component r ∈ fiberCouplingSet source target carrier r := by
  filter_upwards [hsource, htarget, hcarrier] with r hrSource hrTarget hrCarrier
  refine ⟨?_, ?_, hrCarrier⟩
  · simpa [Kernel.map_apply _ measurable_fst] using hrSource
  · simpa [Kernel.map_apply _ measurable_snd] using hrTarget

theorem replacement_marginals_of_mem_fiberCouplingSet_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (replacement : Kernel R (X × Y))
    (carrier : Set (R × (X × Y)))
    (hfeasible :
      ∀ᵐ r ∂(sigma : Measure R),
        replacement r ∈ fiberCouplingSet source target carrier r) :
    replacement.map Prod.fst =ᵐ[(sigma : Measure R)] source ∧
      replacement.map Prod.snd =ᵐ[(sigma : Measure R)] target := by
  constructor
  · filter_upwards [hfeasible] with r hr
    simpa [Kernel.map_apply _ measurable_fst] using hr.1
  · filter_upwards [hfeasible] with r hr
    simpa [Kernel.map_apply _ measurable_snd] using hr.2.1

theorem replacement_carrier_of_mem_fiberCouplingSet_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (replacement : Kernel R (X × Y))
    (carrier : Set (R × (X × Y)))
    (hfeasible :
      ∀ᵐ r ∂(sigma : Measure R),
        replacement r ∈ fiberCouplingSet source target carrier r) :
    ∀ᵐ r ∂(sigma : Measure R),
      ∀ᵐ z ∂replacement r, (r, z) ∈ carrier := by
  filter_upwards [hfeasible] with r hr
  exact hr.2.2

theorem liftedComponentPlan_isSupported_fiberCarrier
    [MeasurableEq R]
    (sigma : FiniteMeasure R)
    (component : Kernel R (X × Y))
    [IsMarkovKernel component]
    {carrier : Set (R × (X × Y))}
    (hcarrierMeasurable : MeasurableSet carrier)
    (hcarrier :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂component r, (r, z) ∈ carrier) :
    ∀ᵐ z ∂(liftedComponentPlan sigma component :
        Measure ((R × X) × (R × Y))),
      z ∈ liftedFiberCarrier carrier := by
  have hLiftedMeasurable :
      MeasurableSet (liftedFiberCarrier carrier) :=
    measurableSet_liftedFiberCarrier hcarrierMeasurable
  change
    ∀ᵐ z ∂((sigma : Measure R) ⊗ₘ component).map liftedComponentMap,
      z.1.1 = z.2.1 ∧
        (z.1.1, (z.1.2, z.2.2)) ∈ carrier
  rw [ae_map_iff measurable_liftedComponentMap.aemeasurable
    hLiftedMeasurable]
  apply Measure.ae_compProd_of_ae_ae
  · exact hLiftedMeasurable.preimage measurable_liftedComponentMap
  · filter_upwards [hcarrier] with r hr
    filter_upwards [hr] with z hz
    exact ⟨rfl, hz⟩

theorem liftedComponentCoupling_mem_fiberCouplingSet
    [MeasurableEq R]
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    {carrier : Set (R × (X × Y))}
    (hcarrierMeasurable : MeasurableSet carrier)
    (hcarrier :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂component r, (r, z) ∈ carrier) :
    liftedComponentCoupling sigma source target component hsource htarget ∈
      liftedFiberCouplingSet
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target) carrier := by
  exact liftedComponentPlan_isSupported_fiberCarrier
    sigma component hcarrierMeasurable hcarrier

end FiberCarrier

section Localization

variable {R X Y : Type*}
  [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]

/-- The precise measurable-selection input left open by the localization
argument.  Whenever a feasible Markov component kernel fails to minimize
on a non-null family of fibers, this premise selects one measurable Markov
kernel which is feasible almost everywhere, no more expensive almost
everywhere, and not cost-equal almost everywhere. -/
def FiberwiseImprovementSelectionPremise
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
    ∃ replacement : Kernel R (X × Y),
      IsMarkovKernel replacement ∧
        (∀ᵐ r ∂(sigma : Measure R),
          replacement r ∈ fiberCouplingSet source target carrier r) ∧
        (fiberKernelCost cost replacement
          ≤ᵐ[(sigma : Measure R)] fiberKernelCost cost component) ∧
        ¬ fiberKernelCost cost replacement
          =ᵐ[(sigma : Measure R)] fiberKernelCost cost component

/-- A measurable positive-measure fiber replacement is incompatible with
global minimality of the lifted component coupling. -/
theorem no_measurableFiberImprovement_of_liftedGlobalMinimality
    [MeasurableEq R]
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component replacement : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component] [IsMarkovKernel replacement]
    (carrier : Set (R × (X × Y)))
    (hcarrierMeasurable : MeasurableSet carrier)
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    (hreplacementFeasible :
      ∀ᵐ r ∂(sigma : Measure R),
        replacement r ∈ fiberCouplingSet source target carrier r)
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost)
    (bound : Real)
    (hbound : ∀ p, ‖cost p‖ ≤ bound)
    (hglobal :
      IsMinimizerOn
        (liftedFiberCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target) carrier)
        (liftedFiberIntegralCost cost)
        (liftedComponentCoupling sigma source target component
          hsource htarget))
    (hcostLe :
      fiberKernelCost cost replacement
        ≤ᵐ[(sigma : Measure R)] fiberKernelCost cost component)
    (hcostNotEq :
      ¬ fiberKernelCost cost replacement
        =ᵐ[(sigma : Measure R)] fiberKernelCost cost component) :
    False := by
  obtain ⟨hreplacementSource, hreplacementTarget⟩ :=
    replacement_marginals_of_mem_fiberCouplingSet_ae
      sigma source target replacement carrier hreplacementFeasible
  have hreplacementCarrier :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂replacement r, (r, z) ∈ carrier :=
    replacement_carrier_of_mem_fiberCouplingSet_ae
      sigma source target replacement carrier hreplacementFeasible
  let replacementCoupling :=
    liftedComponentCoupling sigma source target replacement
      hreplacementSource hreplacementTarget
  have hreplacementMem :
      replacementCoupling ∈
        liftedFiberCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target) carrier := by
    exact liftedComponentCoupling_mem_fiberCouplingSet
      sigma source target replacement hreplacementSource hreplacementTarget
      hcarrierMeasurable hreplacementCarrier
  have hreplacementIntegrable :
      Integrable (fiberKernelCost cost replacement) (sigma : Measure R) :=
    integrable_fiberKernelCost_of_bound
      sigma replacement hcost bound hbound
  have hcomponentIntegrable :
      Integrable (fiberKernelCost cost component) (sigma : Measure R) :=
    integrable_fiberKernelCost_of_bound
      sigma component hcost bound hbound
  have hIntegralLe :
      (∫ r, fiberKernelCost cost replacement r ∂(sigma : Measure R)) ≤
        ∫ r, fiberKernelCost cost component r ∂(sigma : Measure R) :=
    integral_mono_ae hreplacementIntegrable hcomponentIntegrable hcostLe
  have hIntegralNe :
      (∫ r, fiberKernelCost cost replacement r ∂(sigma : Measure R)) ≠
        ∫ r, fiberKernelCost cost component r ∂(sigma : Measure R) := by
    intro hEq
    exact hcostNotEq
      ((integral_eq_iff_of_ae_le
        hreplacementIntegrable hcomponentIntegrable hcostLe).mp hEq)
  have hIntegralLt :
      (∫ r, fiberKernelCost cost replacement r ∂(sigma : Measure R)) <
        ∫ r, fiberKernelCost cost component r ∂(sigma : Measure R) :=
    lt_of_le_of_ne hIntegralLe hIntegralNe
  have hGlobalLe :=
    hglobal.2 replacementCoupling hreplacementMem
  rw [liftedFiberIntegralCost_liftedComponentCoupling
      sigma source target component hsource htarget hcost bound hbound,
    liftedFiberIntegralCost_liftedComponentCoupling
      sigma source target replacement hreplacementSource hreplacementTarget
        hcost bound hbound] at hGlobalLe
  exact (not_lt_of_ge hGlobalLe) hIntegralLt

/-- The downstream localization theorem.  Once the explicit measurable
improvement-selection premise is available, a globally minimizing lifted
component kernel is fiberwise minimizing for almost every base label. -/
theorem ae_fiberwiseKernelMinimality_of_liftedGlobalMinimality
    [MeasurableEq R]
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    (component : Kernel R (X × Y))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel component]
    (carrier : Set (R × (X × Y)))
    (hcarrierMeasurable : MeasurableSet carrier)
    (hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source)
    (htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target)
    (hcomponentCarrier :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂component r, (r, z) ∈ carrier)
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost)
    (bound : Real)
    (hbound : ∀ p, ‖cost p‖ ≤ bound)
    (hselection :
      FiberwiseImprovementSelectionPremise
        sigma source target carrier cost)
    (hglobal :
      IsMinimizerOn
        (liftedFiberCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target) carrier)
        (liftedFiberIntegralCost cost)
        (liftedComponentCoupling sigma source target component
          hsource htarget)) :
    ∀ᵐ r ∂(sigma : Measure R),
      IsMinimizerOn
        (fiberCouplingSet source target carrier r)
        (fiberMeasureCost cost r) (component r) := by
  have hcomponentFeasible :
      ∀ᵐ r ∂(sigma : Measure R),
        component r ∈ fiberCouplingSet source target carrier r :=
    component_mem_fiberCouplingSet_ae
      sigma source target component carrier
      hsource htarget hcomponentCarrier
  by_contra hnot
  obtain
      ⟨replacement, hreplacementMarkov, hreplacementFeasible,
        hreplacementLe, hreplacementNotEq⟩ :=
    hselection component (inferInstance : IsMarkovKernel component)
      hcomponentFeasible hnot
  letI : IsMarkovKernel replacement := hreplacementMarkov
  exact no_measurableFiberImprovement_of_liftedGlobalMinimality
    sigma source target component replacement carrier
    hcarrierMeasurable hsource htarget
    hreplacementFeasible hcost bound hbound hglobal
    hreplacementLe hreplacementNotEq

end Localization

section UnliftGlobalMinimizer

variable {R X Y : Type*}
  [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]

/-- Read the first copied label from a lifted pair. -/
def fiberwiseLiftedFirstLabel
    (z : (R × X) × (R × Y)) : R :=
  z.1.1

/-- Erase both copied labels from a lifted pair. -/
def fiberwiseDropLiftedLabels
    (z : (R × X) × (R × Y)) : X × Y :=
  (z.1.2, z.2.2)

omit [StandardBorelSpace R] [Nonempty R]
  [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] in
theorem measurable_fiberwiseLiftedFirstLabel :
    Measurable
      (fiberwiseLiftedFirstLabel :
        (R × X) × (R × Y) -> R) := by
  unfold fiberwiseLiftedFirstLabel
  fun_prop

omit [StandardBorelSpace R] [Nonempty R]
  [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] in
theorem measurable_fiberwiseDropLiftedLabels :
    Measurable
      (fiberwiseDropLiftedLabels :
        (R × X) × (R × Y) -> X × Y) := by
  unfold fiberwiseDropLiftedLabels
  fun_prop

/-- The component kernel canonically extracted from an arbitrary lifted
coupling: condition on the first label, then erase both copied labels. -/
noncomputable def componentKernelOfLiftedCoupling
    {alpha : FiniteMeasure (R × X)}
    {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta) :
    Kernel R (X × Y) :=
  (ap91Disintegration fiberwiseLiftedFirstLabel
    (gamma.plan : Measure ((R × X) × (R × Y)))).map
      fiberwiseDropLiftedLabels

theorem componentKernelOfLiftedCoupling_isMarkovKernel
    {alpha : FiniteMeasure (R × X)}
    {beta : FiniteMeasure (R × Y)}
    (gamma : FiniteCoupling alpha beta) :
    IsMarkovKernel (componentKernelOfLiftedCoupling gamma) := by
  letI :
      IsMarkovKernel
        (ap91Disintegration fiberwiseLiftedFirstLabel
          (gamma.plan : Measure ((R × X) × (R × Y)))) :=
    ap91Disintegration_isMarkovKernel fiberwiseLiftedFirstLabel
      (gamma.plan : Measure ((R × X) × (R × Y)))
  exact Kernel.IsMarkovKernel.map _
    measurable_fiberwiseDropLiftedLabels

attribute [local instance]
  componentKernelOfLiftedCoupling_isMarkovKernel

omit [StandardBorelSpace R] [Nonempty R]
  [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] in
theorem liftedCoupling_firstLabelBase_forFiberwise
    (sigma : FiniteMeasure R)
    (source : Kernel R X) [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    Measure.map fiberwiseLiftedFirstLabel
        (gamma.plan : Measure ((R × X) × (R × Y))) =
      (sigma : Measure R) := by
  have hFirst :
      Measure.map
          (Prod.fst : (R × X) × (R × Y) -> R × X)
          (gamma.plan : Measure ((R × X) × (R × Y))) =
        (sigma : Measure R) ⊗ₘ source := by
    simpa [firstMarginal, liftedKernelMarginal,
      FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure (R × X) =>
          (eta : Measure (R × X))) gamma.property.1
  calc
    Measure.map fiberwiseLiftedFirstLabel
        (gamma.plan : Measure ((R × X) × (R × Y))) =
        Measure.map Prod.fst
          (Measure.map Prod.fst
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) := by
      rw [Measure.map_map measurable_fst measurable_fst]
      rfl
    _ = Measure.map Prod.fst
          ((sigma : Measure R) ⊗ₘ source) := by
      rw [hFirst]
    _ = (sigma : Measure R) :=
      Measure.fst_compProd (sigma : Measure R) source

omit [StandardBorelSpace R] [Nonempty R]
  [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] in
theorem liftedCoupling_firstMarginal_measure_forFiberwise
    (sigma : FiniteMeasure R)
    (source : Kernel R X) [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    Measure.map
        (Prod.fst : (R × X) × (R × Y) -> R × X)
        (gamma.plan : Measure ((R × X) × (R × Y))) =
      (sigma : Measure R) ⊗ₘ source := by
  simpa [firstMarginal, liftedKernelMarginal,
    FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (R × X) =>
        (eta : Measure (R × X))) gamma.property.1

omit [StandardBorelSpace R] [Nonempty R]
  [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] in
theorem liftedCoupling_secondMarginal_measure_forFiberwise
    {alpha : FiniteMeasure (R × X)}
    (sigma : FiniteMeasure R)
    (target : Kernel R Y) [IsMarkovKernel target]
    (gamma :
      FiniteCoupling alpha (liftedKernelMarginal sigma target)) :
    Measure.map
        (Prod.snd : (R × X) × (R × Y) -> R × Y)
        (gamma.plan : Measure ((R × X) × (R × Y))) =
      (sigma : Measure R) ⊗ₘ target := by
  simpa [secondMarginal, liftedKernelMarginal,
    FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure (R × Y) =>
        (eta : Measure (R × Y))) gamma.property.2

/-- Joint reconstruction of the extracted component kernel. -/
theorem componentKernelOfLiftedCoupling_joint
    (sigma : FiniteMeasure R)
    (source : Kernel R X) [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta) :
    (sigma : Measure R) ⊗ₘ componentKernelOfLiftedCoupling gamma =
      Measure.map
        (fun z =>
          (fiberwiseLiftedFirstLabel z,
            fiberwiseDropLiftedLabels z))
        (gamma.plan : Measure ((R × X) × (R × Y))) := by
  let labelKernel :=
    ap91Disintegration fiberwiseLiftedFirstLabel
      (gamma.plan : Measure ((R × X) × (R × Y)))
  letI : IsMarkovKernel labelKernel :=
    ap91Disintegration_isMarkovKernel fiberwiseLiftedFirstLabel
      (gamma.plan : Measure ((R × X) × (R × Y)))
  have hDropProd :
      Measurable
        (Prod.map id fiberwiseDropLiftedLabels :
          R × ((R × X) × (R × Y)) -> R × (X × Y)) :=
    measurable_id.prodMap measurable_fiberwiseDropLiftedLabels
  have hGraph :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (fiberwiseLiftedFirstLabel z, z)) :=
    measurable_fiberwiseLiftedFirstLabel.prodMk measurable_id
  change
    (sigma : Measure R) ⊗ₘ
        labelKernel.map fiberwiseDropLiftedLabels =
      Measure.map
        (fun z =>
          (fiberwiseLiftedFirstLabel z,
            fiberwiseDropLiftedLabels z))
        (gamma.plan : Measure ((R × X) × (R × Y)))
  rw [← liftedCoupling_firstLabelBase_forFiberwise
    sigma source gamma]
  calc
    Measure.map fiberwiseLiftedFirstLabel
          (gamma.plan : Measure ((R × X) × (R × Y))) ⊗ₘ
        labelKernel.map fiberwiseDropLiftedLabels =
        Measure.map
          (Prod.map id fiberwiseDropLiftedLabels)
          (Measure.map fiberwiseLiftedFirstLabel
              (gamma.plan :
                Measure ((R × X) × (R × Y))) ⊗ₘ
            labelKernel) :=
      Measure.compProd_map measurable_fiberwiseDropLiftedLabels
    _ = Measure.map
          (Prod.map id fiberwiseDropLiftedLabels)
          (Measure.map
            (fun z => (fiberwiseLiftedFirstLabel z, z))
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) := by
      rw [ap91_joint_reconstruction]
    _ = Measure.map
          ((Prod.map id fiberwiseDropLiftedLabels) ∘
            fun z => (fiberwiseLiftedFirstLabel z, z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      rw [Measure.map_map hDropProd hGraph]
    _ = Measure.map
          (fun z =>
            (fiberwiseLiftedFirstLabel z,
              fiberwiseDropLiftedLabels z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      rfl

/-- Every same-label lifted coupling is exactly the lifted component plan
of its canonically extracted component kernel. -/
theorem liftedComponentPlan_componentKernelOfLiftedCoupling
    (sigma : FiniteMeasure R)
    (source : Kernel R X) [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta)
    (hSameLabel :
      IsSupported gamma (liftedSameLabelRelation R X Y)) :
    (liftedComponentPlan sigma
        (componentKernelOfLiftedCoupling gamma) :
      Measure ((R × X) × (R × Y))) =
      (gamma.plan : Measure ((R × X) × (R × Y))) := by
  letI :
      IsMarkovKernel (componentKernelOfLiftedCoupling gamma) :=
    componentKernelOfLiftedCoupling_isMarkovKernel gamma
  have hUnlift :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (fiberwiseLiftedFirstLabel z,
            fiberwiseDropLiftedLabels z)) := by
    exact measurable_fiberwiseLiftedFirstLabel.prodMk
      measurable_fiberwiseDropLiftedLabels
  rw [liftedComponentPlan_toMeasure,
    componentKernelOfLiftedCoupling_joint sigma source gamma,
    Measure.map_map measurable_liftedComponentMap hUnlift]
  calc
    Measure.map
          (liftedComponentMap ∘
            fun z =>
              (fiberwiseLiftedFirstLabel z,
                fiberwiseDropLiftedLabels z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) =
        Measure.map id
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      apply Measure.map_congr
      filter_upwards [hSameLabel] with z hz
      rcases z with ⟨⟨r, x⟩, ⟨s, y⟩⟩
      change r = s at hz
      simp [liftedComponentMap, fiberwiseLiftedFirstLabel,
        fiberwiseDropLiftedLabels, hz]
    _ = (gamma.plan :
          Measure ((R × X) × (R × Y))) :=
      Measure.map_id

theorem componentKernelOfLiftedCoupling_map_fst_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target)) :
    (componentKernelOfLiftedCoupling gamma).map Prod.fst
      =ᵐ[(sigma : Measure R)] source := by
  letI :
      IsMarkovKernel (componentKernelOfLiftedCoupling gamma) :=
    componentKernelOfLiftedCoupling_isMarkovKernel gamma
  have hUnlift :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (fiberwiseLiftedFirstLabel z,
            fiberwiseDropLiftedLabels z)) := by
    exact measurable_fiberwiseLiftedFirstLabel.prodMk
      measurable_fiberwiseDropLiftedLabels
  have hFstProd :
      Measurable
        (Prod.map id Prod.fst : R × (X × Y) -> R × X) :=
    measurable_id.prodMap measurable_fst
  apply Kernel.ae_eq_of_compProd_eq
  calc
    (sigma : Measure R) ⊗ₘ
          (componentKernelOfLiftedCoupling gamma).map Prod.fst =
        Measure.map (Prod.map id Prod.fst)
          ((sigma : Measure R) ⊗ₘ
            componentKernelOfLiftedCoupling gamma) :=
      Measure.compProd_map measurable_fst
    _ = Measure.map (Prod.map id Prod.fst)
          (Measure.map
            (fun z =>
              (fiberwiseLiftedFirstLabel z,
                fiberwiseDropLiftedLabels z))
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) := by
      rw [componentKernelOfLiftedCoupling_joint
        sigma source gamma]
    _ = Measure.map
          ((Prod.map id Prod.fst) ∘
            fun z =>
              (fiberwiseLiftedFirstLabel z,
                fiberwiseDropLiftedLabels z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      rw [Measure.map_map hFstProd hUnlift]
    _ = Measure.map Prod.fst
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      congr 1
    _ = (sigma : Measure R) ⊗ₘ source :=
      liftedCoupling_firstMarginal_measure_forFiberwise
        sigma source gamma

theorem componentKernelOfLiftedCoupling_map_snd_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
    (hSameLabel :
      IsSupported gamma (liftedSameLabelRelation R X Y)) :
    (componentKernelOfLiftedCoupling gamma).map Prod.snd
      =ᵐ[(sigma : Measure R)] target := by
  letI :
      IsMarkovKernel (componentKernelOfLiftedCoupling gamma) :=
    componentKernelOfLiftedCoupling_isMarkovKernel gamma
  have hUnlift :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (fiberwiseLiftedFirstLabel z,
            fiberwiseDropLiftedLabels z)) := by
    exact measurable_fiberwiseLiftedFirstLabel.prodMk
      measurable_fiberwiseDropLiftedLabels
  have hSndProd :
      Measurable
        (Prod.map id Prod.snd : R × (X × Y) -> R × Y) :=
    measurable_id.prodMap measurable_snd
  apply Kernel.ae_eq_of_compProd_eq
  calc
    (sigma : Measure R) ⊗ₘ
          (componentKernelOfLiftedCoupling gamma).map Prod.snd =
        Measure.map (Prod.map id Prod.snd)
          ((sigma : Measure R) ⊗ₘ
            componentKernelOfLiftedCoupling gamma) :=
      Measure.compProd_map measurable_snd
    _ = Measure.map (Prod.map id Prod.snd)
          (Measure.map
            (fun z =>
              (fiberwiseLiftedFirstLabel z,
                fiberwiseDropLiftedLabels z))
            (gamma.plan :
              Measure ((R × X) × (R × Y)))) := by
      rw [componentKernelOfLiftedCoupling_joint
        sigma source gamma]
    _ = Measure.map
          ((Prod.map id Prod.snd) ∘
            fun z =>
              (fiberwiseLiftedFirstLabel z,
                fiberwiseDropLiftedLabels z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      rw [Measure.map_map hSndProd hUnlift]
    _ = Measure.map Prod.snd
          (gamma.plan :
            Measure ((R × X) × (R × Y))) := by
      apply Measure.map_congr
      filter_upwards [hSameLabel] with z hz
      rcases z with ⟨⟨r, x⟩, ⟨s, y⟩⟩
      change r = s at hz
      simp [fiberwiseLiftedFirstLabel,
        fiberwiseDropLiftedLabels, hz]
    _ = (sigma : Measure R) ⊗ₘ target :=
      liftedCoupling_secondMarginal_measure_forFiberwise
        sigma target gamma

theorem componentKernelOfLiftedCoupling_carrier_ae
    (sigma : FiniteMeasure R)
    (source : Kernel R X) [IsMarkovKernel source]
    {beta : FiniteMeasure (R × Y)}
    (gamma :
      FiniteCoupling (liftedKernelMarginal sigma source) beta)
    {carrier : Set (R × (X × Y))}
    (hcarrierMeasurable : MeasurableSet carrier)
    (hgammaCarrier :
      IsSupported gamma (liftedFiberCarrier carrier)) :
    ∀ᵐ r ∂(sigma : Measure R),
      ∀ᵐ z ∂componentKernelOfLiftedCoupling gamma r,
        (r, z) ∈ carrier := by
  letI :
      IsMarkovKernel (componentKernelOfLiftedCoupling gamma) :=
    componentKernelOfLiftedCoupling_isMarkovKernel gamma
  have hUnlift :
      Measurable
        (fun z : (R × X) × (R × Y) =>
          (fiberwiseLiftedFirstLabel z,
            fiberwiseDropLiftedLabels z)) := by
    exact measurable_fiberwiseLiftedFirstLabel.prodMk
      measurable_fiberwiseDropLiftedLabels
  have hJoint :
      ∀ᵐ p ∂
          ((sigma : Measure R) ⊗ₘ
            componentKernelOfLiftedCoupling gamma),
        p ∈ carrier := by
    rw [componentKernelOfLiftedCoupling_joint
      sigma source gamma]
    change
      ∀ᵐ p ∂Measure.map
          (fun z =>
            (fiberwiseLiftedFirstLabel z,
              fiberwiseDropLiftedLabels z))
          (gamma.plan :
            Measure ((R × X) × (R × Y))),
        carrier p
    rw [ae_map_iff hUnlift.aemeasurable hcarrierMeasurable]
    filter_upwards [hgammaCarrier] with z hz
    exact hz.2
  exact Measure.ae_ae_of_ae_compProd hJoint

theorem liftedComponentCoupling_componentKernelOfLiftedCoupling
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
    (hSameLabel :
      IsSupported gamma (liftedSameLabelRelation R X Y)) :
    let component := componentKernelOfLiftedCoupling gamma
    letI : IsMarkovKernel component :=
      componentKernelOfLiftedCoupling_isMarkovKernel gamma
    let hsource :=
      componentKernelOfLiftedCoupling_map_fst_ae
        sigma source target gamma
    let htarget :=
      componentKernelOfLiftedCoupling_map_snd_ae
        sigma source target gamma hSameLabel
    liftedComponentCoupling sigma source target component
      hsource htarget = gamma := by
  dsimp only
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  exact liftedComponentPlan_componentKernelOfLiftedCoupling
    sigma source gamma hSameLabel

/-- Strong form of the bridge: an arbitrary globally minimizing lifted
coupling is disintegrated into a canonical component kernel, and that
kernel is fiberwise minimizing almost everywhere under exactly the
measurable-improvement selection premise. -/
theorem ae_componentKernelOfLiftedGlobalMinimizer_fiberwiseMinimal
    (sigma : FiniteMeasure R)
    (source : Kernel R X) (target : Kernel R Y)
    [IsMarkovKernel source] [IsMarkovKernel target]
    (carrier : Set (R × (X × Y)))
    (hcarrierMeasurable : MeasurableSet carrier)
    {cost : R × (X × Y) -> Real}
    (hcost : StronglyMeasurable cost)
    (bound : Real)
    (hbound : ∀ p, ‖cost p‖ ≤ bound)
    (hselection :
      FiberwiseImprovementSelectionPremise
        sigma source target carrier cost)
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
    (hglobal :
      IsMinimizerOn
        (liftedFiberCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target) carrier)
        (liftedFiberIntegralCost cost) gamma) :
    ∀ᵐ r ∂(sigma : Measure R),
      IsMinimizerOn
        (fiberCouplingSet source target carrier r)
        (fiberMeasureCost cost r)
        (componentKernelOfLiftedCoupling gamma r) := by
  have hSameLabel :
      IsSupported gamma (liftedSameLabelRelation R X Y) := by
    filter_upwards [hglobal.1] with z hz
    exact hz.1
  let component := componentKernelOfLiftedCoupling gamma
  letI : IsMarkovKernel component :=
    componentKernelOfLiftedCoupling_isMarkovKernel gamma
  have hsource :
      component.map Prod.fst =ᵐ[(sigma : Measure R)] source :=
    componentKernelOfLiftedCoupling_map_fst_ae
      sigma source target gamma
  have htarget :
      component.map Prod.snd =ᵐ[(sigma : Measure R)] target :=
    componentKernelOfLiftedCoupling_map_snd_ae
      sigma source target gamma hSameLabel
  have hcomponentCarrier :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ z ∂component r, (r, z) ∈ carrier :=
    componentKernelOfLiftedCoupling_carrier_ae
      sigma source gamma hcarrierMeasurable hglobal.1
  have hCouplingEq :
      liftedComponentCoupling sigma source target component
        hsource htarget = gamma := by
    exact liftedComponentCoupling_componentKernelOfLiftedCoupling
      sigma source target gamma hSameLabel
  have hcomponentGlobal :
      IsMinimizerOn
        (liftedFiberCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target) carrier)
        (liftedFiberIntegralCost cost)
        (liftedComponentCoupling sigma source target component
          hsource htarget) := by
    rw [hCouplingEq]
    exact hglobal
  exact ae_fiberwiseKernelMinimality_of_liftedGlobalMinimality
    sigma source target component carrier hcarrierMeasurable
    hsource htarget hcomponentCarrier hcost bound hbound
    hselection hcomponentGlobal

end UnliftGlobalMinimizer

section RayForwardStrictExponential

/-- The unlifted forward carrier on one oriented ray. -/
def rayForwardFiberCarrier (n : Nat) :
    Set
      (OrientedOpenRay n ×
        (Euclidean n × Euclidean n)) :=
  {p |
    rayCoordinate p.1 p.2.1 ≤
      rayCoordinate p.1 p.2.2}

theorem isClosed_rayForwardFiberCarrier (n : Nat) :
    IsClosed (rayForwardFiberCarrier n) := by
  exact isClosed_le
    (continuous_rayCoordinate_uncurry.comp
      (continuous_fst.prodMk
        (continuous_fst.comp continuous_snd)))
    (continuous_rayCoordinate_uncurry.comp
      (continuous_fst.prodMk
        (continuous_snd.comp continuous_snd)))

theorem measurableSet_rayForwardFiberCarrier (n : Nat) :
    MeasurableSet (rayForwardFiberCarrier n) :=
  (isClosed_rayForwardFiberCarrier n).measurableSet

@[simp]
theorem liftedFiberCarrier_rayForwardFiberCarrier (n : Nat) :
    liftedFiberCarrier (rayForwardFiberCarrier n) =
      liftedRayForwardRelation n :=
  rfl

/-- The strict bounded profile, written on an unlifted ray fiber. -/
def rayStrictExponentialFiberCost
    {n : Nat}
    (p :
      OrientedOpenRay n ×
        (Euclidean n × Euclidean n)) : Real :=
  1 - Real.exp (-dist p.2.1 p.2.2)

theorem continuous_rayStrictExponentialFiberCost
    {n : Nat} :
    Continuous (rayStrictExponentialFiberCost (n := n)) := by
  unfold rayStrictExponentialFiberCost
  fun_prop

theorem stronglyMeasurable_rayStrictExponentialFiberCost
    {n : Nat} :
    StronglyMeasurable
      (rayStrictExponentialFiberCost (n := n)) :=
  continuous_rayStrictExponentialFiberCost.stronglyMeasurable

theorem norm_rayStrictExponentialFiberCost_le_one
    {n : Nat}
    (p :
      OrientedOpenRay n ×
        (Euclidean n × Euclidean n)) :
    ‖rayStrictExponentialFiberCost p‖ ≤ 1 := by
  have hexp :
      Real.exp (-dist p.2.1 p.2.2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr dist_nonneg)
  change |1 - Real.exp (-dist p.2.1 p.2.2)| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr hexp)]
  exact sub_le_self 1 (Real.exp_nonneg _)

/-- The exact selection premise needed for the oriented-ray forward,
strict-exponential problem. -/
def RayForwardFiberwiseImprovementSelectionPremise
    {n : Nat}
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n)) : Prop :=
  FiberwiseImprovementSelectionPremise
    sigma source target
    (rayForwardFiberCarrier n)
    rayStrictExponentialFiberCost

/-- Direct specialization for an arbitrary global minimizer supplied by
`existsLiftedRayForwardKernelMinimizer_strictExponentialProfile`. -/
theorem ae_rayForwardComponentKernel_minimal_of_liftedGlobalMinimizer
    {n : Nat} [Nonempty (OrientedOpenRay n)]
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    (hselection :
      RayForwardFiberwiseImprovementSelectionPremise
        sigma source target)
    (gamma :
      FiniteCoupling
        (liftedKernelMarginal sigma source)
        (liftedKernelMarginal sigma target))
    (hglobal :
      IsMinimizerOn
        (liftedRayForwardCouplingSet
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target))
        (fun eta =>
          ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
            ∂(eta.plan :
              Measure
                ((OrientedOpenRay n × Euclidean n) ×
                  (OrientedOpenRay n × Euclidean n))))
        gamma) :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      IsMinimizerOn
        (fiberCouplingSet source target
          (rayForwardFiberCarrier n) R)
        (fiberMeasureCost rayStrictExponentialFiberCost R)
        (componentKernelOfLiftedCoupling gamma R) := by
  apply
    ae_componentKernelOfLiftedGlobalMinimizer_fiberwiseMinimal
      sigma source target (rayForwardFiberCarrier n)
      (measurableSet_rayForwardFiberCarrier n)
      stronglyMeasurable_rayStrictExponentialFiberCost 1
      norm_rayStrictExponentialFiberCost_le_one
      hselection gamma
  simpa [liftedFiberCouplingSet, liftedFiberCarrier,
    rayForwardFiberCarrier, liftedRayForwardCouplingSet,
    liftedFiberIntegralCost, liftedFiberPointCost,
    rayStrictExponentialFiberCost] using hglobal

/-- The existing compactness theorem plus measurable improvement selection
produces a lifted minimizer whose canonical conditional kernel is
fiberwise minimal almost everywhere. -/
theorem existsLiftedRayForwardMinimizer_with_ae_fiberwiseMinimality
    {n : Nat} [Nonempty (OrientedOpenRay n)]
    (sigma : FiniteMeasure (OrientedOpenRay n))
    (source target :
      Kernel (OrientedOpenRay n) (Euclidean n))
    (witness :
      Kernel
        (OrientedOpenRay n)
        (Euclidean n × Euclidean n))
    [IsMarkovKernel source] [IsMarkovKernel target]
    [IsMarkovKernel witness]
    (hsource :
      witness.map Prod.fst
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] source)
    (htarget :
      witness.map Prod.snd
        =ᵐ[(sigma : Measure (OrientedOpenRay n))] target)
    (hforward :
      ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂witness R,
          rayCoordinate R z.1 ≤ rayCoordinate R z.2)
    (hselection :
      RayForwardFiberwiseImprovementSelectionPremise
        sigma source target) :
    ∃ gamma :
        FiniteCoupling
          (liftedKernelMarginal sigma source)
          (liftedKernelMarginal sigma target),
      IsMinimizerOn
          (liftedRayForwardCouplingSet
            (liftedKernelMarginal sigma source)
            (liftedKernelMarginal sigma target))
          (fun eta =>
            ∫ z, (1 - Real.exp (-dist z.1.2 z.2.2))
              ∂(eta.plan :
                Measure
                  ((OrientedOpenRay n × Euclidean n) ×
                    (OrientedOpenRay n × Euclidean n))))
          gamma ∧
        ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
          IsMinimizerOn
            (fiberCouplingSet source target
              (rayForwardFiberCarrier n) R)
            (fiberMeasureCost
              rayStrictExponentialFiberCost R)
            (componentKernelOfLiftedCoupling gamma R) := by
  obtain ⟨gamma, hglobal⟩ :=
    existsLiftedRayForwardKernelMinimizer_strictExponentialProfile
      sigma source target witness hsource htarget hforward
  refine ⟨gamma, hglobal, ?_⟩
  exact
    ae_rayForwardComponentKernel_minimal_of_liftedGlobalMinimizer
      sigma source target hselection gamma hglobal

end RayForwardStrictExponential

end ConcaveOTLimit
