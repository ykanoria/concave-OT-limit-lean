import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Probability-measure compactification infrastructure

This module supplies the project-specific Borel and Polish instances used to
embed probability measures on a Euclidean pair into probability measures on
its one-point compactification.
-/

open Filter Function MeasureTheory Set Topology

open scoped ENNReal MeasureTheory OnePoint

noncomputable section

namespace ConcaveOTLimit.ProbabilityMeasureCompactification

private theorem standardBorelSpace_of_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] (e : A ≃ᵐ B) :
    StandardBorelSpace A := by
  letI := upgradeStandardBorel B
  let t : TopologicalSpace A :=
    TopologicalSpace.induced e
      (inferInstance : TopologicalSpace B)
  have ht : @PolishSpace A t :=
    e.toEquiv.polishSpace_induced
  letI : TopologicalSpace A := t
  have hBorel : BorelSpace A :=
    e.measurableEmbedding.borelSpace ⟨rfl⟩
  exact ⟨t, hBorel, ht⟩

private def compactProbabilityCoordinates
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    ProbabilityMeasure X -> Nat -> NNReal :=
  fun mu k =>
    mu.toFiniteMeasure.testAgainstNN
      ((ContinuousMap.equivBoundedOfCompact X NNReal)
        (TopologicalSpace.denseSeq C(X, NNReal) k))

private theorem compactProbabilityCoordinates_continuous
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    Continuous (compactProbabilityCoordinates X) := by
  apply continuous_pi
  intro k
  exact ProbabilityMeasure.continuous_testAgainstNN_eval _

private theorem compactProbabilityCoordinates_measurable
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    Measurable (compactProbabilityCoordinates X) := by
  apply measurable_pi_lambda
  intro k
  have hf :
      Measurable fun x : X =>
        ((TopologicalSpace.denseSeq C(X, NNReal) k x :
            NNReal) : ENNReal) :=
    measurable_coe_nnreal_ennreal.comp
      (TopologicalSpace.denseSeq C(X, NNReal) k).continuous.measurable
  change Measurable fun mu : ProbabilityMeasure X =>
    (∫⁻ x, ((TopologicalSpace.denseSeq C(X, NNReal) k x :
      NNReal) : ENNReal) ∂(mu : Measure X)).toNNReal
  exact ENNReal.measurable_toNNReal.comp
    ((Measure.measurable_lintegral hf).comp measurable_subtype_coe)

private theorem compactProbabilityCoordinates_injective
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    Injective (compactProbabilityCoordinates X) := by
  intro mu nu h
  have hmu :
      Continuous fun f : C(X, NNReal) =>
        mu.toFiniteMeasure.testAgainstNN
          ((ContinuousMap.equivBoundedOfCompact X NNReal) f) :=
    mu.toFiniteMeasure.testAgainstNN_lipschitz.continuous.comp
      (ContinuousMap.isometryEquivBoundedOfCompact X NNReal).continuous
  have hnu :
      Continuous fun f : C(X, NNReal) =>
        nu.toFiniteMeasure.testAgainstNN
          ((ContinuousMap.equivBoundedOfCompact X NNReal) f) :=
    nu.toFiniteMeasure.testAgainstNN_lipschitz.continuous.comp
      (ContinuousMap.isometryEquivBoundedOfCompact X NNReal).continuous
  have hall :
      (fun f : C(X, NNReal) =>
        mu.toFiniteMeasure.testAgainstNN
          ((ContinuousMap.equivBoundedOfCompact X NNReal) f)) =
      fun f : C(X, NNReal) =>
        nu.toFiniteMeasure.testAgainstNN
          ((ContinuousMap.equivBoundedOfCompact X NNReal) f) := by
    apply
      (TopologicalSpace.denseRange_denseSeq C(X, NNReal)).equalizer
        hmu hnu
    funext k
    simpa only [Function.comp_apply, compactProbabilityCoordinates]
      using congrFun h k
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  have hf :=
    congrFun hall
      ((ContinuousMap.equivBoundedOfCompact X NNReal).symm f)
  have hf' := congrArg ((↑) : NNReal -> ENNReal) hf
  simpa only [FiniteMeasure.testAgainstNN_coe_eq] using hf'

private theorem borelSpace_probabilityMeasure_of_compact
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    BorelSpace (ProbabilityMeasure X) := by
  let mP : MeasurableSpace (ProbabilityMeasure X) :=
    inferInstance
  have hborel_le :
      borel (ProbabilityMeasure X) <= mP := by
    have hinducing :
        IsInducing (compactProbabilityCoordinates X) :=
      ((compactProbabilityCoordinates_continuous X).isClosedEmbedding
        (compactProbabilityCoordinates_injective X)).isInducing
    calc
      borel (ProbabilityMeasure X) =
          (borel (Nat -> NNReal)).comap
            (compactProbabilityCoordinates X) := by
        rw [← borel_comap, hinducing.eq_induced]
      _ =
          (inferInstance : MeasurableSpace (Nat -> NNReal)).comap
            (compactProbabilityCoordinates X) := by
        rw [BorelSpace.measurable_eq (α := Nat -> NNReal)]
      _ <= mP :=
        (compactProbabilityCoordinates_measurable X).comap_le
  have hmP_le :
      mP <= borel (ProbabilityMeasure X) := by
    letI : MeasurableSpace (ProbabilityMeasure X) :=
      borel (ProbabilityMeasure X)
    haveI : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
    have hcoe :
        Measurable fun mu : ProbabilityMeasure X =>
          (mu : Measure X) := by
      apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        BorelSpace.measurable_eq isPiSystem_isOpen
      intro s hs
      apply LowerSemicontinuous.measurable
      rw [lowerSemicontinuous_iff_le_liminf]
      intro mu
      exact
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto
          tendsto_id hs
    change
      MeasurableSpace.comap
          (fun mu : ProbabilityMeasure X => (mu : Measure X))
          (inferInstanceAs (MeasurableSpace (Measure X))) <=
        borel (ProbabilityMeasure X)
    exact hcoe.comap_le
  exact ⟨le_antisymm hmP_le hborel_le⟩

private theorem polishSpace_probabilityMeasure_of_compact
    {X : Type*} [t : TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] :
    PolishSpace (ProbabilityMeasure X) := by
  haveI :
      TopologicalSpace.IsCompletelyMetrizableSpace
        (ProbabilityMeasure X) := by
    letI : MetricSpace (ProbabilityMeasure X) :=
      TopologicalSpace.metrizableSpaceMetric _
    infer_instance
  infer_instance

private instance compactifiedPairMeasurableSpace (n : Nat) :
    MeasurableSpace
      (OnePoint (Euclidean n × Euclidean n)) :=
  borel _

private instance compactifiedPairBorelSpace (n : Nat) :
    BorelSpace (OnePoint (Euclidean n × Euclidean n)) :=
  ⟨rfl⟩

private instance compactifiedPairPolishSpace (n : Nat) :
    PolishSpace (OnePoint (Euclidean n × Euclidean n)) := by
  let e :=
    onePointEquivSphereOfFinrankEq
      (ι := Fin (2 * n + 1))
      (V := Euclidean n × Euclidean n)
      (by simp [Module.finrank_prod]; omega)
  exact e.isClosedEmbedding.polishSpace

private instance compactifiedProbabilityPolishSpace (n : Nat) :
    PolishSpace
      (ProbabilityMeasure
        (OnePoint (Euclidean n × Euclidean n))) :=
  polishSpace_probabilityMeasure_of_compact

private instance compactifiedProbabilityBorelSpace (n : Nat) :
    BorelSpace
      (ProbabilityMeasure
        (OnePoint (Euclidean n × Euclidean n))) :=
  borelSpace_probabilityMeasure_of_compact _

private def pairToOnePoint (n : Nat) :
    Euclidean n × Euclidean n ->
      OnePoint (Euclidean n × Euclidean n) :=
  OnePoint.some

private theorem pairToOnePoint_continuous (n : Nat) :
    Continuous (pairToOnePoint n) :=
  OnePoint.continuous_coe

private theorem pairToOnePoint_measurableEmbedding (n : Nat) :
    MeasurableEmbedding (pairToOnePoint n) := by
  exact OnePoint.isOpenEmbedding_coe.measurableEmbedding

private def compactifyProbabilityMeasure (n : Nat) :
    ProbabilityMeasure (Euclidean n × Euclidean n) ->
      ProbabilityMeasure
        (OnePoint (Euclidean n × Euclidean n)) :=
  fun mu =>
    mu.map (pairToOnePoint_continuous n).measurable.aemeasurable

private theorem compactifyProbabilityMeasure_measurable (n : Nat) :
    Measurable (compactifyProbabilityMeasure n) := by
  apply Measurable.subtype_mk
  exact
    (Measure.measurable_map
      (pairToOnePoint n)
      (pairToOnePoint_continuous n).measurable).comp
        measurable_subtype_coe

private theorem range_compactifyProbabilityMeasure (n : Nat) :
    range (compactifyProbabilityMeasure n) =
      {nu :
          ProbabilityMeasure
            (OnePoint (Euclidean n × Euclidean n)) |
        (nu : Measure (OnePoint (Euclidean n × Euclidean n)))
          ({OnePoint.infty} : Set
            (OnePoint (Euclidean n × Euclidean n))) = 0} := by
  ext nu
  constructor
  · rintro ⟨mu, rfl⟩
    change
      Measure.map (pairToOnePoint n)
          (mu : Measure (Euclidean n × Euclidean n))
          ({OnePoint.infty} : Set
            (OnePoint (Euclidean n × Euclidean n))) = 0
    rw [Measure.map_apply
      (pairToOnePoint_continuous n).measurable
      OnePoint.isClosed_infty.measurableSet]
    simp [pairToOnePoint]
  · intro hnu
    have hcoe :
        MeasurableEmbedding (pairToOnePoint n) :=
      pairToOnePoint_measurableEmbedding n
    have hae :
        ∀ᵐ z ∂(nu :
            Measure (OnePoint (Euclidean n × Euclidean n))),
          z ∈ range (pairToOnePoint n) := by
      rw [ae_iff]
      change
        (nu : Measure (OnePoint (Euclidean n × Euclidean n)))
          ((range (pairToOnePoint n))ᶜ) = 0
      have hrange :
          (range (pairToOnePoint n))ᶜ =
            ({OnePoint.infty} :
              Set (OnePoint (Euclidean n × Euclidean n))) := by
        ext z
        cases z <;> simp [pairToOnePoint]
      rw [hrange]
      exact hnu
    let mu :
        ProbabilityMeasure (Euclidean n × Euclidean n) :=
      ⟨Measure.comap (pairToOnePoint n)
          (nu : Measure
            (OnePoint (Euclidean n × Euclidean n))),
        hcoe.isProbabilityMeasure_comap hae⟩
    refine ⟨mu, ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    change
      Measure.map (pairToOnePoint n)
          (Measure.comap (pairToOnePoint n)
            (nu : Measure
              (OnePoint (Euclidean n × Euclidean n)))) =
        (nu : Measure
          (OnePoint (Euclidean n × Euclidean n)))
    rw [hcoe.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem hae

private theorem
    measurableSet_range_compactifyProbabilityMeasure (n : Nat) :
    MeasurableSet (range (compactifyProbabilityMeasure n)) := by
  rw [range_compactifyProbabilityMeasure]
  exact measurableSet_eq_fun
    ((Measure.measurable_coe
      OnePoint.isClosed_infty.measurableSet).comp
        measurable_subtype_coe)
    measurable_const

private def decompactifyProbabilityMeasureOnRange (n : Nat) :
    range (compactifyProbabilityMeasure n) ->
      ProbabilityMeasure (Euclidean n × Euclidean n) :=
  fun nu =>
    ⟨Measure.comap (pairToOnePoint n)
        (nu.1 : Measure
          (OnePoint (Euclidean n × Euclidean n))),
      by
        obtain ⟨mu, hmu⟩ := nu.2
        rw [← hmu]
        change
          IsProbabilityMeasure
            (Measure.comap (pairToOnePoint n)
              (Measure.map (pairToOnePoint n)
                (mu : Measure (Euclidean n × Euclidean n))))
        rw [(pairToOnePoint_measurableEmbedding n).comap_map]
        exact mu.property⟩

private theorem
    measurable_decompactifyProbabilityMeasureOnRange (n : Nat) :
    Measurable (decompactifyProbabilityMeasureOnRange n) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have himage :
      MeasurableSet (pairToOnePoint n '' s) :=
    (pairToOnePoint_measurableEmbedding n).measurableSet_image' hs
  simpa only [decompactifyProbabilityMeasureOnRange,
    (pairToOnePoint_measurableEmbedding n).comap_apply]
    using
      (Measure.measurable_coe himage).comp
        (measurable_subtype_coe.comp measurable_subtype_coe)

private theorem compactifyProbabilityMeasure_measurableEmbedding
    (n : Nat) :
    MeasurableEmbedding (compactifyProbabilityMeasure n) := by
  apply MeasurableEmbedding.of_measurable_inverse_on_range
    (compactifyProbabilityMeasure_measurable n)
    (measurableSet_range_compactifyProbabilityMeasure n)
    (measurable_decompactifyProbabilityMeasureOnRange n)
  intro mu
  apply ProbabilityMeasure.toMeasure_injective
  exact
    (pairToOnePoint_measurableEmbedding n).comap_map
      (mu : Measure (Euclidean n × Euclidean n))

private instance standardBorelSpace_probabilityMeasure_euclideanPair
    (n : Nat) :
    StandardBorelSpace
      (ProbabilityMeasure (Euclidean n × Euclidean n)) := by
  have hrange :
      StandardBorelSpace
        (range (compactifyProbabilityMeasure n)) :=
    (measurableSet_range_compactifyProbabilityMeasure n).standardBorel
  letI := hrange
  exact standardBorelSpace_of_measurableEquiv
    (compactifyProbabilityMeasure_measurableEmbedding n).equivRange

end ConcaveOTLimit.ProbabilityMeasureCompactification
