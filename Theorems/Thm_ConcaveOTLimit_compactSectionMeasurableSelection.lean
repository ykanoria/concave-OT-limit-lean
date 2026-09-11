import Theorems.Thm_ConcaveOTLimit_orientedOpenRayStandardBorel
import Theorems.Thm_ConcaveOTLimit_probabilityMeasureCompactification
import ErgodicTheory.MeasureTheory.CompactSectionProjection
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Compact-section measurable selection

This module builds the project-specific measurable selector and specializes it
to ray-indexed probability measures. The Borel compact-section projection
theorem is imported from the attributed Apache-2.0 modules under
`ErgodicTheory/MeasureTheory`; see `NOTICE` and `formalization.yaml`.
-/

namespace ConcaveOTLimit

section Interface

variable (A B : Type*)
  [MeasurableSpace A] [MeasurableSpace B] [TopologicalSpace B]

/-- A measurable graph with compact sections has a measurable
nonempty-section projection and an everywhere-defined measurable selector
which selects on that projection. -/
def CompactSectionMeasurableSelectionPremise : Prop :=
  ∀ graph : Set (A × B),
    MeasurableSet graph ->
    (∀ a : A, IsCompact {b : B | (a, b) ∈ graph}) ->
    ∃ selector : A -> B,
      Measurable selector ∧
        MeasurableSet
          {a : A | {b : B | (a, b) ∈ graph}.Nonempty} ∧
        ∀ a : A,
          {b : B | (a, b) ∈ graph}.Nonempty ->
            (a, selector a) ∈ graph

end Interface

end ConcaveOTLimit

namespace ConcaveOTLimit.CompactSectionMeasurableSelection

open Filter Function MeasureTheory Metric Set Topology

noncomputable section

variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [CompleteSpace Y] [Nonempty Y]

structure CompactGraph (X Y : Type*)
    [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y] where
  carrier : Set (X × Y)
  measurable_carrier : MeasurableSet carrier
  compact_section : ∀ x, IsCompact {y | (x, y) ∈ carrier}

namespace CompactGraph

def fiber (G : CompactGraph X Y) (x : X) : Set Y :=
  {y | (x, y) ∈ G.carrier}

def domain (G : CompactGraph X Y) : Set X :=
  {x | (G.fiber x).Nonempty}

theorem domain_eq_image_fst (G : CompactGraph X Y) :
    G.domain = Prod.fst '' G.carrier := by
  ext x
  simp only [domain, fiber, mem_setOf_eq, Set.Nonempty, mem_image]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩
  · rintro ⟨⟨x', y⟩, hy, rfl⟩
    exact ⟨y, hy⟩

theorem measurableSet_domain (G : CompactGraph X Y) :
    MeasurableSet G.domain := by
  rw [G.domain_eq_image_fst]
  exact
    ErgodicTheory.measurableSet_image_fst_of_isCompact_sections
      G.measurable_carrier G.compact_section

def restrictClosedBall (G : CompactGraph X Y) (c : X → Y)
    (hc : Measurable c) (r : ℝ) : CompactGraph X Y where
  carrier := {p | p ∈ G.carrier ∧ dist p.2 (c p.1) ≤ r}
  measurable_carrier :=
    G.measurable_carrier.inter <|
      measurableSet_le
        (Measurable.dist measurable_snd (hc.comp measurable_fst))
        measurable_const
  compact_section := fun x => by
    have h :
        IsCompact
          ({y | (x, y) ∈ G.carrier} ∩ closedBall (c x) r) :=
      (G.compact_section x).inter_right isClosed_closedBall
    simpa only [fiber, mem_setOf_eq, mem_inter_iff, mem_closedBall] using h

theorem fiber_restrictClosedBall (G : CompactGraph X Y)
    (c : X → Y) (hc : Measurable c) (r : ℝ) (x : X) :
    (G.restrictClosedBall c hc r).fiber x =
      G.fiber x ∩ closedBall (c x) r := by
  ext y
  simp only [restrictClosedBall, fiber, mem_setOf_eq, mem_inter_iff,
    mem_closedBall]

def hit (G : CompactGraph X Y) (u : ℕ → Y) (r : ℝ)
    (x : X) (k : ℕ) : Prop :=
  ((G.restrictClosedBall (fun _ => u k) measurable_const r).fiber x).Nonempty

theorem measurableSet_hit (G : CompactGraph X Y) (u : ℕ → Y)
    (r : ℝ) (k : ℕ) :
    MeasurableSet {x | G.hit u r x k} :=
  (G.restrictClosedBall (fun _ => u k) measurable_const r).measurableSet_domain

def choosePred (G : CompactGraph X Y) (u : ℕ → Y) (r : ℝ)
    (x : X) (k : ℕ) : Prop :=
  G.hit u r x k ∨ (x ∉ G.domain ∧ k = 0)

theorem exists_choosePred (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (r : ℝ) (hr : 0 < r) (x : X) :
    ∃ k, G.choosePred u r x k := by
  by_cases hx : x ∈ G.domain
  · obtain ⟨y, hy⟩ := hx
    obtain ⟨k, hk⟩ := hu.exists_dist_lt y hr
    refine ⟨k, Or.inl ?_⟩
    refine ⟨y, ?_⟩
    simp only [restrictClosedBall, fiber, mem_setOf_eq]
    exact ⟨hy, by simpa only [dist_comm] using hk.le⟩
  · exact ⟨0, Or.inr ⟨hx, rfl⟩⟩

theorem measurableSet_choosePred (G : CompactGraph X Y) (u : ℕ → Y)
    (r : ℝ) (k : ℕ) :
    MeasurableSet {x | G.choosePred u r x k} := by
  have hhit : MeasurableSet {x | G.hit u r x k} :=
    G.measurableSet_hit u r k
  have hempty : MeasurableSet {x | x ∉ G.domain} :=
    G.measurableSet_domain.compl
  by_cases hk : k = 0
  · subst k
    simpa only [choosePred, and_true, setOf_or] using hhit.union hempty
  · simpa only [choosePred, hk, and_false, or_false] using hhit

def center (G : CompactGraph X Y) (u : ℕ → Y) (hu : DenseRange u)
    (r : ℝ) (hr : 0 < r) (x : X) : Y :=
  open Classical in
  u (Nat.find (G.exists_choosePred u hu r hr x))

theorem measurable_center (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (r : ℝ) (hr : 0 < r) :
    Measurable (G.center u hu r hr) := by
  classical
  exact (measurable_of_countable u).comp <|
    measurable_find (G.exists_choosePred u hu r hr) <|
      G.measurableSet_choosePred u r

theorem center_hits (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (r : ℝ) (hr : 0 < r) {x : X}
    (hx : x ∈ G.domain) :
    (G.fiber x ∩ closedBall (G.center u hu r hr x) r).Nonempty := by
  classical
  have hp :=
    Nat.find_spec (G.exists_choosePred u hu r hr x)
  rcases hp with hp | hp
  · simpa only [hit, G.fiber_restrictClosedBall,
      center] using hp
  · exact False.elim (hp.1 hx)

theorem center_eq_zero_of_notMem_domain (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) (r : ℝ) (hr : 0 < r)
    {x : X} (hx : x ∉ G.domain) :
    G.center u hu r hr x = u 0 := by
  classical
  simp only [center]
  apply congrArg u
  apply (Nat.find_eq_zero _).2
  exact Or.inr ⟨hx, rfl⟩

def next (G : CompactGraph X Y) (u : ℕ → Y) (hu : DenseRange u)
    (r : ℝ) (hr : 0 < r) : CompactGraph X Y :=
  G.restrictClosedBall (G.center u hu r hr)
    (G.measurable_center u hu r hr) r

theorem fiber_next (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (r : ℝ) (hr : 0 < r) (x : X) :
    (G.next u hu r hr).fiber x =
      G.fiber x ∩ closedBall (G.center u hu r hr x) r :=
  G.fiber_restrictClosedBall _ _ _ _

theorem mem_domain_next_iff (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (r : ℝ) (hr : 0 < r) (x : X) :
    x ∈ (G.next u hu r hr).domain ↔ x ∈ G.domain := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (G.fiber_next u hu r hr x ▸ hy).1⟩
  · intro hx
    exact G.center_hits u hu r hr hx

def radius (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  simp only [radius]
  positivity

theorem radius_anti {n m : ℕ} (h : n ≤ m) :
    radius m ≤ radius n := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right h 1

theorem tendsto_radius : Tendsto radius atTop (𝓝 0) := by
  simpa only [radius] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))

def iterGraph (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) : ℕ → CompactGraph X Y
  | 0 => G
  | n + 1 => (iterGraph G u hu n).next u hu (radius n) (radius_pos n)

@[simp]
theorem iterGraph_zero (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) :
    iterGraph G u hu 0 = G :=
  rfl

@[simp]
theorem iterGraph_succ (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (n : ℕ) :
    iterGraph G u hu (n + 1) =
      (iterGraph G u hu n).next u hu (radius n) (radius_pos n) :=
  rfl

def centerSeq (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (n : ℕ) (x : X) : Y :=
  (iterGraph G u hu n).center u hu (radius n) (radius_pos n) x

theorem measurable_centerSeq (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (n : ℕ) :
    Measurable (G.centerSeq u hu n) :=
  (iterGraph G u hu n).measurable_center u hu (radius n) (radius_pos n)

theorem mem_iterGraph_domain_iff (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) (n : ℕ) (x : X) :
    x ∈ (iterGraph G u hu n).domain ↔ x ∈ G.domain := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterGraph_succ,
        (iterGraph G u hu n).mem_domain_next_iff]
      exact ih

theorem fiber_iterGraph_succ_subset (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) (n : ℕ) (x : X) :
    (iterGraph G u hu (n + 1)).fiber x ⊆
      (iterGraph G u hu n).fiber x := by
  rw [iterGraph_succ,
    (iterGraph G u hu n).fiber_next]
  exact inter_subset_left

theorem fiber_iterGraph_mono (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) {n m : ℕ} (hnm : n ≤ m)
    (x : X) :
    (iterGraph G u hu m).fiber x ⊆
      (iterGraph G u hu n).fiber x := by
  induction m, hnm using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m hnm ih =>
      exact (G.fiber_iterGraph_succ_subset u hu m x).trans ih

theorem centerSeq_eq_zero_of_notMem_domain (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) {x : X} (hx : x ∉ G.domain)
    (n : ℕ) :
    G.centerSeq u hu n x = u 0 := by
  apply (iterGraph G u hu n).center_eq_zero_of_notMem_domain
  rwa [mem_iterGraph_domain_iff]

theorem mem_closedBall_centerSeq_of_mem_iterGraph_succ
    (G : CompactGraph X Y) (u : ℕ → Y) (hu : DenseRange u)
    {n : ℕ} {x : X} {y : Y}
    (hy : y ∈ (iterGraph G u hu (n + 1)).fiber x) :
    y ∈ closedBall (G.centerSeq u hu n x) (radius n) := by
  rw [iterGraph_succ,
    (iterGraph G u hu n).fiber_next] at hy
  exact hy.2

theorem cauchySeq_centerSeq (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) (x : X) :
    CauchySeq (fun n => G.centerSeq u hu n x) := by
  by_cases hx : x ∈ G.domain
  · rw [cauchySeq_iff_le_tendsto_0]
    refine ⟨fun N => 2 * radius N, fun N => mul_nonneg (by positivity) (radius_pos N).le,
      ?_, by simpa using tendsto_radius.const_mul 2⟩
    intro n m N hNn hNm
    have hxmax :
        x ∈ (iterGraph G u hu (max n m + 1)).domain := by
      rwa [mem_iterGraph_domain_iff]
    obtain ⟨z, hz⟩ := hxmax
    have hzn :
        z ∈ (iterGraph G u hu (n + 1)).fiber x :=
      G.fiber_iterGraph_mono u hu
        (Nat.add_le_add_right (le_max_left n m) 1) x hz
    have hzm :
        z ∈ (iterGraph G u hu (m + 1)).fiber x :=
      G.fiber_iterGraph_mono u hu
        (Nat.add_le_add_right (le_max_right n m) 1) x hz
    have hbn :=
      G.mem_closedBall_centerSeq_of_mem_iterGraph_succ u hu hzn
    have hbm :=
      G.mem_closedBall_centerSeq_of_mem_iterGraph_succ u hu hzm
    calc
      dist (G.centerSeq u hu n x) (G.centerSeq u hu m x) ≤
          dist (G.centerSeq u hu n x) z +
            dist z (G.centerSeq u hu m x) :=
        dist_triangle _ _ _
      _ ≤ radius n + radius m := by
        exact add_le_add (by simpa only [dist_comm] using hbn) hbm
      _ ≤ radius N + radius N :=
        add_le_add (radius_anti hNn) (radius_anti hNm)
      _ = 2 * radius N := by ring
  · have heq :
        (fun n => G.centerSeq u hu n x) = fun _ => u 0 := by
      funext n
      exact G.centerSeq_eq_zero_of_notMem_domain u hu hx n
    rw [heq]
    exact cauchySeq_const _

def selector (G : CompactGraph X Y) (u : ℕ → Y)
    (hu : DenseRange u) (x : X) : Y :=
  limUnder atTop (fun n => G.centerSeq u hu n x)

theorem tendsto_centerSeq_selector (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) (x : X) :
    Tendsto (fun n => G.centerSeq u hu n x) atTop
      (𝓝 (G.selector u hu x)) :=
  (G.cauchySeq_centerSeq u hu x).tendsto_limUnder

theorem measurable_selector (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) :
    Measurable (G.selector u hu) := by
  apply measurable_of_tendsto_metrizable (G.measurable_centerSeq u hu)
  rw [tendsto_pi_nhds]
  exact G.tendsto_centerSeq_selector u hu

theorem selector_mem (G : CompactGraph X Y)
    (u : ℕ → Y) (hu : DenseRange u) {x : X}
    (hx : x ∈ G.domain) :
    G.selector u hu x ∈ G.fiber x := by
  let z : ℕ → Y := fun n =>
    Classical.choose <|
      (G.mem_iterGraph_domain_iff u hu (n + 1) x).2 hx
  have hzmem (n : ℕ) :
      z n ∈ (iterGraph G u hu (n + 1)).fiber x :=
    Classical.choose_spec <|
      (G.mem_iterGraph_domain_iff u hu (n + 1) x).2 hx
  have hzball (n : ℕ) :
      z n ∈ closedBall (G.centerSeq u hu n x) (radius n) :=
    G.mem_closedBall_centerSeq_of_mem_iterGraph_succ u hu (hzmem n)
  have hzlim : Tendsto z atTop (𝓝 (G.selector u hu x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero'
      (g := fun n =>
        radius n +
          dist (G.centerSeq u hu n x) (G.selector u hu x))
      (Eventually.of_forall fun n => dist_nonneg)
      (Eventually.of_forall fun n => ?_) ?_
    · calc
        dist (z n) (G.selector u hu x) ≤
            dist (z n) (G.centerSeq u hu n x) +
              dist (G.centerSeq u hu n x) (G.selector u hu x) :=
          dist_triangle _ _ _
        _ ≤ radius n +
              dist (G.centerSeq u hu n x) (G.selector u hu x) :=
          add_le_add (hzball n) le_rfl
    · simpa using tendsto_radius.add
        (tendsto_iff_dist_tendsto_zero.1 <|
          G.tendsto_centerSeq_selector u hu x)
  apply (G.compact_section x).isClosed.mem_of_tendsto hzlim
  filter_upwards [] with n
  exact G.fiber_iterGraph_mono u hu (Nat.zero_le (n + 1)) x (hzmem n)

theorem exists_measurable_selector (G : CompactGraph X Y) :
    ∃ f : X → Y, Measurable f ∧ MeasurableSet G.domain ∧
      ∀ x, x ∈ G.domain → f x ∈ G.fiber x := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Y
  exact ⟨G.selector u hu, G.measurable_selector u hu,
    G.measurableSet_domain, fun x => G.selector_mem u hu⟩

end CompactGraph

/-- A Borel graph with compact fibers between Polish spaces has a Borel
nonempty-fiber domain and an everywhere-defined Borel selector. -/
private theorem
    compactSectionMeasurableSelectionPremise_of_completeMetric :
    CompactSectionMeasurableSelectionPremise X Y := by
  intro graph hgraph hcompact
  let G : CompactGraph X Y := {
    carrier := graph
    measurable_carrier := hgraph
    compact_section := hcompact
  }
  obtain ⟨selector, hselector, hdomain, hselect⟩ :=
    G.exists_measurable_selector
  refine ⟨selector, hselector, ?_, ?_⟩
  · simpa only [G, CompactGraph.domain, CompactGraph.fiber] using hdomain
  · intro x hx
    have hxG : x ∈ G.domain := by
      simpa only [G, CompactGraph.domain, CompactGraph.fiber] using hx
    simpa only [G, CompactGraph.fiber] using hselect x hxG

end

/-- A Borel graph with compact fibers between Polish spaces has a Borel
nonempty-fiber domain and an everywhere-defined Borel selector. -/
theorem compactSectionMeasurableSelectionPremise_of_polish
    {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y] :
    CompactSectionMeasurableSelectionPremise X Y := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  exact compactSectionMeasurableSelectionPremise_of_completeMetric

end ConcaveOTLimit.CompactSectionMeasurableSelection

namespace ConcaveOTLimit

namespace CompactSectionMeasurableSelection

open MeasureTheory Set

open scoped OnePoint

private def pairToOnePoint (n : Nat) :
    Euclidean n × Euclidean n →
      OnePoint (Euclidean n × Euclidean n) :=
  OnePoint.some

private theorem continuous_pairToOnePoint (n : Nat) :
    Continuous (pairToOnePoint n) :=
  OnePoint.continuous_coe

private theorem measurableEmbedding_pairToOnePoint (n : Nat) :
    MeasurableEmbedding (pairToOnePoint n) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

private noncomputable def compactifyProbabilityMeasure (n : Nat) :
    ProbabilityMeasure (Euclidean n × Euclidean n) →
      ProbabilityMeasure
        (OnePoint (Euclidean n × Euclidean n)) :=
  fun μ =>
    μ.map (continuous_pairToOnePoint n).measurable.aemeasurable

private theorem continuous_compactifyProbabilityMeasure (n : Nat) :
    Continuous (compactifyProbabilityMeasure n) :=
  ProbabilityMeasure.continuous_map (continuous_pairToOnePoint n)

private theorem measurable_compactifyProbabilityMeasure (n : Nat) :
    Measurable (compactifyProbabilityMeasure n) := by
  apply Measurable.subtype_mk
  exact
    (Measure.measurable_map
      (pairToOnePoint n)
      (continuous_pairToOnePoint n).measurable).comp
        measurable_subtype_coe

private theorem injective_compactifyProbabilityMeasure (n : Nat) :
    Function.Injective (compactifyProbabilityMeasure n) := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply (measurableEmbedding_pairToOnePoint n).map_injective
  exact congrArg ProbabilityMeasure.toMeasure h

private theorem measurableEmbedding_compactifyProbabilityMeasure
    (n : Nat) :
    MeasurableEmbedding (compactifyProbabilityMeasure n) :=
  (measurable_compactifyProbabilityMeasure n).measurableEmbedding
    (injective_compactifyProbabilityMeasure n)

/-- Compact-section measurable selection for the ray-indexed probability
graphs used by the canonical rational-gap construction. -/
theorem
    compactSectionMeasurableSelectionPremise_orientedOpenRay_probabilityMeasure
    (n : Nat) :
    CompactSectionMeasurableSelectionPremise
      (OrientedOpenRay n)
      (ProbabilityMeasure (Euclidean n × Euclidean n)) := by
  intro graph hgraph hcompact
  let compactGraph : Set
      (OrientedOpenRay n ×
        ProbabilityMeasure
          (OnePoint (Euclidean n × Euclidean n))) :=
    Prod.map (id : OrientedOpenRay n → OrientedOpenRay n)
      (compactifyProbabilityMeasure n) '' graph
  have hprodEmbedding :
      MeasurableEmbedding
        (Prod.map (id : OrientedOpenRay n → OrientedOpenRay n)
          (compactifyProbabilityMeasure n)) :=
    MeasurableEmbedding.id.prodMap
      (measurableEmbedding_compactifyProbabilityMeasure n)
  have hcompactGraph : MeasurableSet compactGraph :=
    hprodEmbedding.measurableSet_image.2 hgraph
  have hfiber (R : OrientedOpenRay n) :
      {ν : ProbabilityMeasure
          (OnePoint (Euclidean n × Euclidean n)) |
        (R, ν) ∈ compactGraph} =
        compactifyProbabilityMeasure n ''
          {μ : ProbabilityMeasure (Euclidean n × Euclidean n) |
            (R, μ) ∈ graph} := by
    ext ν
    constructor
    · rintro ⟨⟨R', μ⟩, hRμ, heq⟩
      have hR : R' = R := congrArg Prod.fst heq
      have hν :
          compactifyProbabilityMeasure n μ = ν :=
        congrArg Prod.snd heq
      subst R'
      exact ⟨μ, hRμ, hν⟩
    · rintro ⟨μ, hRμ, rfl⟩
      exact ⟨(R, μ), hRμ, rfl⟩
  have hcompactFiber (R : OrientedOpenRay n) :
      IsCompact
        {ν : ProbabilityMeasure
            (OnePoint (Euclidean n × Euclidean n)) |
          (R, ν) ∈ compactGraph} := by
    rw [hfiber R]
    exact (hcompact R).image
      (continuous_compactifyProbabilityMeasure n)
  letI :=
    TopologicalSpace.upgradeIsCompletelyMetrizable
      (ProbabilityMeasure
        (OnePoint (Euclidean n × Euclidean n)))
  let G : CompactGraph
      (OrientedOpenRay n)
      (ProbabilityMeasure
        (OnePoint (Euclidean n × Euclidean n))) := {
    carrier := compactGraph
    measurable_carrier := hcompactGraph
    compact_section := hcompactFiber
  }
  obtain ⟨compactSelector, hcompactSelector, hdomain, hselect⟩ :=
    G.exists_measurable_selector
  have hdomainEq :
      G.domain =
        {R : OrientedOpenRay n |
          {μ : ProbabilityMeasure (Euclidean n × Euclidean n) |
            (R, μ) ∈ graph}.Nonempty} := by
    ext R
    change
      {ν : ProbabilityMeasure
          (OnePoint (Euclidean n × Euclidean n)) |
        (R, ν) ∈ compactGraph}.Nonempty ↔
        {μ : ProbabilityMeasure (Euclidean n × Euclidean n) |
          (R, μ) ∈ graph}.Nonempty
    rw [hfiber R]
    exact image_nonempty
  let embedding :=
    measurableEmbedding_compactifyProbabilityMeasure n
  let selector :
      OrientedOpenRay n →
        ProbabilityMeasure (Euclidean n × Euclidean n) :=
    embedding.invFun ∘ compactSelector
  refine ⟨selector, ?_, ?_, ?_⟩
  · exact embedding.measurable_invFun.comp hcompactSelector
  · rw [← hdomainEq]
    exact hdomain
  · intro R hR
    have hRG : R ∈ G.domain := by
      rw [hdomainEq]
      exact hR
    have hs := hselect R hRG
    change compactSelector R ∈
      {ν : ProbabilityMeasure
          (OnePoint (Euclidean n × Euclidean n)) |
        (R, ν) ∈ compactGraph} at hs
    rw [hfiber R] at hs
    obtain ⟨μ, hμ, hμeq⟩ := hs
    have hinv : embedding.invFun (compactSelector R) = μ := by
      rw [← hμeq]
      exact embedding.leftInverse_invFun μ
    simpa only [selector, Function.comp_apply, hinv] using hμ

end CompactSectionMeasurableSelection

end ConcaveOTLimit
