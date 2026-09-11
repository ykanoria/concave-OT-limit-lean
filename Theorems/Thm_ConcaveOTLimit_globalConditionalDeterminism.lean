import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementAssembly
import Theorems.Thm_ConcaveOTLimit_raywiseExcursionIdentification
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.MeasurableIntegral

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Extracting a measurable map from an a.e. Dirac kernel -/

noncomputable def boundedEuclideanEmbedding (n : Nat) :
    Euclidean n -> Euclidean n :=
  fun x => (Homeomorph.unitBall x : Euclidean n)

theorem boundedEuclideanEmbedding_measurableEmbedding (n : Nat) :
    MeasurableEmbedding (boundedEuclideanEmbedding n) := by
  exact
    (MeasurableEmbedding.subtype_coe measurableSet_ball).comp
      (Homeomorph.unitBall (E := Euclidean n)).measurableEmbedding

theorem boundedEuclideanEmbedding_stronglyMeasurable (n : Nat) :
    StronglyMeasurable (boundedEuclideanEmbedding n) := by
  exact
    ((Homeomorph.unitBall (E := Euclidean n)).continuous.subtype_val).measurable
      |>.stronglyMeasurable

noncomputable def euclideanKernelSelector
    {X : Type*} [MeasurableSpace X] (n : Nat)
    (kappa : Kernel X (Euclidean n)) :
    X -> Euclidean n :=
  fun x =>
    (boundedEuclideanEmbedding_measurableEmbedding n).invFun
      (integral (kappa x) (boundedEuclideanEmbedding n))

theorem measurable_euclideanKernelSelector
    {X : Type*} [MeasurableSpace X] (n : Nat)
    (kappa : Kernel X (Euclidean n)) :
    Measurable (euclideanKernelSelector n kappa) := by
  change Measurable (fun x =>
    (boundedEuclideanEmbedding_measurableEmbedding n).invFun
      (integral (kappa x) (boundedEuclideanEmbedding n)))
  exact
    (boundedEuclideanEmbedding_measurableEmbedding n).measurable_invFun.comp
      ((boundedEuclideanEmbedding_stronglyMeasurable n).integral_kernel
        |>.measurable)

theorem kernel_ae_eq_deterministic_of_ae_isZeroOne
    {X : Type*} [MeasurableSpace X]
    (n : Nat) (mu : Measure X)
    (kappa : Kernel X (Euclidean n)) [IsMarkovKernel kappa]
    (hzero :
      ∀ᵐ x ∂mu, IsZeroOneMeasure (kappa x)) :
    kappa =ᵐ[mu]
      Kernel.deterministic
        (euclideanKernelSelector n kappa)
        (measurable_euclideanKernelSelector n kappa) := by
  filter_upwards [hzero] with x hx
  letI : IsZeroOneMeasure (kappa x) := hx
  letI : IsProbabilityMeasure (kappa x) :=
    (inferInstance : IsMarkovKernel kappa).isProbabilityMeasure x
  obtain ⟨y, hy⟩ :=
    IsZeroOneMeasure.exists_eq_dirac (μ := kappa x)
  have hintegral :
      integral (kappa x) (boundedEuclideanEmbedding n) =
        boundedEuclideanEmbedding n y := by
    rw [hy]
    exact integral_dirac _ _
  have hselector : euclideanKernelSelector n kappa x = y := by
    rw [euclideanKernelSelector, hintegral]
    exact
      MeasurableEmbedding.leftInverse_invFun
        (boundedEuclideanEmbedding_measurableEmbedding n) y
  rw [hy, Kernel.deterministic_apply, hselector]

theorem isGraphPlan_of_condDistrib_ae_isZeroOne
    {X : Type*} [MeasurableSpace X]
    {n : Nat}
    {mu : FiniteMeasure X} {nu : FiniteMeasure (Euclidean n)}
    (gamma : FiniteCoupling mu nu)
    (hzero :
      ∀ᵐ x ∂(gamma.plan : Measure (X × Euclidean n)).map Prod.fst,
        IsZeroOneMeasure
          (condDistrib Prod.snd Prod.fst
            (gamma.plan : Measure (X × Euclidean n)) x)) :
    exists T : X -> Euclidean n, IsGraphPlan gamma T := by
  let kappa :=
    condDistrib Prod.snd Prod.fst
      (gamma.plan : Measure (X × Euclidean n))
  let T := euclideanKernelSelector n kappa
  have hT : Measurable T :=
    measurable_euclideanKernelSelector n kappa
  have hcond :
      condDistrib Prod.snd Prod.fst
          (gamma.plan : Measure (X × Euclidean n)) =ᵐ[
        (gamma.plan : Measure (X × Euclidean n)).map Prod.fst]
        Kernel.deterministic T hT := by
    exact
      kernel_ae_eq_deterministic_of_ae_isZeroOne
        n
        ((gamma.plan : Measure (X × Euclidean n)).map Prod.fst)
        kappa hzero
  exact ⟨T, isGraphPlan_of_condDistrib_ae_eq_deterministic
    gamma T hT hcond⟩

/-! ## Gluing graph fibers over a source-determined label -/

/-- Graph measures can be glued without a measurable choice of their
fiberwise graph maps when the fiber label is a measurable function of the
source. The jointly measurable conditional kernel supplies the global map. -/
theorem kernelComposition_eq_graphMap_of_ae_fiber_graph
    {R X : Type*} [MeasurableSpace R]
    [MeasurableSpace X] [StandardBorelSpace X]
    (n : Nat)
    (sigma : FiniteMeasure R)
    (source : Kernel R X) [IsMarkovKernel source]
    (component : Kernel R (X × Euclidean n))
    [IsMarkovKernel component]
    (label : X -> R) (hlabel : Measurable label)
    (hfst :
      Kernel.fst component =ᵐ[(sigma : Measure R)] source)
    (hsourceLabel :
      ∀ᵐ r ∂(sigma : Measure R),
        ∀ᵐ x ∂source r, label x = r)
    (hfiberGraph :
      ∀ᵐ r ∂(sigma : Measure R),
        exists T : X -> Euclidean n, Measurable T ∧
          component r =
            (source r).map (fun x => (x, T x))) :
    exists T : X -> Euclidean n, Measurable T ∧
      component ∘ₘ (sigma : Measure R) =
        (source ∘ₘ (sigma : Measure R)).map
          (fun x => (x, T x)) := by
  let joint : Kernel (R × X) (Euclidean n) :=
    Kernel.condKernel component
  letI : IsMarkovKernel joint := by
    dsimp only [joint]
    infer_instance
  have hlabelPair : Measurable (fun x : X => (label x, x)) :=
    hlabel.prodMk measurable_id
  let candidate : Kernel X (Euclidean n) :=
    joint.comap (fun x => (label x, x)) hlabelPair
  letI : IsMarkovKernel candidate := by
    dsimp only [candidate]
    infer_instance
  let T : X -> Euclidean n :=
    euclideanKernelSelector n candidate
  have hT : Measurable T :=
    measurable_euclideanKernelSelector n candidate
  refine ⟨T, hT, ?_⟩
  have hfiberFinal :
      component =ᵐ[(sigma : Measure R)]
        source.map (fun x => (x, T x)) := by
    filter_upwards
        [hfst, hsourceLabel, hfiberGraph] with
        r hfstR hsourceLabelR hfiberGraphR
    obtain ⟨fiberMap, hfiberMap, hgraph⟩ := hfiberGraphR
    have hcomponentFst : (component r).fst = source r := by
      simpa only [Kernel.fst_apply] using hfstR
    have hcomponentCompProd :
        component r =
          (component r).fst ⊗ₘ
            Kernel.deterministic fiberMap hfiberMap := by
      rw [hcomponentFst,
        Measure.compProd_deterministic hfiberMap]
      exact hgraph
    have hfiberCond :
        (component r).condKernel =ᵐ[source r]
          Kernel.deterministic fiberMap hfiberMap := by
      have h :=
        eq_condKernel_of_measure_eq_compProd
          (ρ := component r)
          (Kernel.deterministic fiberMap hfiberMap)
          hcomponentCompProd
      rw [hcomponentFst] at h
      filter_upwards [h] with x hx
      exact hx.symm
    have hjointCond :
        (fun x => joint (r, x)) =ᵐ[source r]
          (component r).condKernel := by
      have h :=
        Kernel.condKernel_apply_eq_condKernel component r
      rw [hfstR] at h
      simpa only [joint] using h
    have hcandidateFiber :
        candidate =ᵐ[source r]
          Kernel.deterministic fiberMap hfiberMap := by
      filter_upwards
          [hsourceLabelR, hjointCond, hfiberCond] with
          x hxLabel hxJoint hxFiber
      change joint (label x, x) =
        Kernel.deterministic fiberMap hfiberMap x
      rw [hxLabel, hxJoint, hxFiber]
    have hzero :
        ∀ᵐ x ∂source r,
          IsZeroOneMeasure (candidate x) := by
      filter_upwards [hcandidateFiber] with x hx
      rw [hx]
      infer_instance
    have hcandidateGlobal :
        candidate =ᵐ[source r]
          Kernel.deterministic T hT :=
      kernel_ae_eq_deterministic_of_ae_isZeroOne
        n (source r) candidate hzero
    have hfiberFinalMeasure :
        component r =
          (source r).map (fun x => (x, T x)) := by
      calc
        component r =
            source r ⊗ₘ
              Kernel.deterministic fiberMap hfiberMap := by
          rw [Measure.compProd_deterministic hfiberMap]
          exact hgraph
        _ = source r ⊗ₘ candidate :=
          Measure.compProd_congr hcandidateFiber.symm
        _ = source r ⊗ₘ Kernel.deterministic T hT :=
          Measure.compProd_congr hcandidateGlobal
        _ = (source r).map (fun x => (x, T x)) :=
          Measure.compProd_deterministic hT
    exact hfiberFinalMeasure.trans
      (Kernel.map_apply source
        (show Measurable (fun x : X => (x, T x)) from
          measurable_id.prodMk hT) r).symm
  calc
    component ∘ₘ (sigma : Measure R) =
        source.map (fun x => (x, T x)) ∘ₘ
          (sigma : Measure R) :=
      Measure.comp_congr hfiberFinal
    _ = (source ∘ₘ (sigma : Measure R)).map
        (fun x => (x, T x)) :=
      (Measure.map_comp
        (sigma : Measure R) source
          (measurable_id.prodMk hT)).symm

/-! ## Assembled-ray specialization -/

/-- A.e. raywise excursion graphness glues to one global graph plan. This
uses C174 on each coordinate coupling and does not choose the C174 maps as a
measurable family. -/
theorem assembledRaywiseCoupling_graph_and_condDistrib_ae_deterministic_of_inheritance
    {n : Nat}
    {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hInheritance :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        RaywiseCoordinateInheritance Gamma R
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R)
          (assembledRaywiseComponentFiber D gamma gammaLift R))
    (hExcursion :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          ((assembledRaywiseComponentFiber D gamma gammaLift R).map
            fun z =>
              (rayCoordinate R z.1, rayCoordinate R z.2))) :
    exists T : Euclidean n -> Euclidean n,
      exists hT : Measurable T,
        IsGraphPlan
            (assembledRaywiseCoupling
              D gamma hSupported gammaLift) T ∧
          condDistrib Prod.snd Prod.fst
              ((assembledRaywiseCoupling
                D gamma hSupported gammaLift).plan :
                  Measure (Euclidean n × Euclidean n))
            =ᵐ[(mu : Measure (Euclidean n))]
              Kernel.deterministic T hT := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  letI : IsMarkovKernel
      (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  have hPhysicalCoupling :=
    assembledRaywiseComponent_isCoupling_ae
      D gamma gammaLift hLiftedForward
  have hfiberGraph :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        exists T : Euclidean n -> Euclidean n,
          Measurable T ∧
            assembledRaywiseKernel D gamma gammaLift R =
              (D.source R).map (fun x => (x, T x)) := by
    filter_upwards
        [hPhysicalCoupling, hInheritance, hExcursion] with
        R hCouplingR hInheritanceR hExcursionR
    let physical :
        FiniteCoupling
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R) :=
      ⟨assembledRaywiseComponentFiber
        D gamma gammaLift R, hCouplingR⟩
    let coordinate := hInheritanceR.coordinateCoupling
    have hExcursionCoordinate :
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          coordinate.plan := by
      simpa only [coordinate,
        RaywiseCoordinateInheritance.coordinateCoupling] using hExcursionR
    obtain ⟨coordinateMap, hCoordinateGraph⟩ :=
      juilletExcursionPlanIsGraph coordinate
        hInheritanceR.coordinateMarginalsMutuallySingular
        hInheritanceR.coordinateSourceAtomless
        hInheritanceR.coordinateTargetDominates
        hExcursionCoordinate
    let physicalMap : Euclidean n -> Euclidean n :=
      fun x => R.point (coordinateMap (rayCoordinate R x))
    have hPhysicalGraph : IsGraphPlan physical physicalMap :=
      rayPhysicalGraph_of_coordinateGraph
        R
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        physical hInheritanceR coordinateMap hCoordinateGraph
    obtain ⟨hPhysicalMap, hPhysicalPlan⟩ := hPhysicalGraph
    refine ⟨physicalMap, hPhysicalMap, ?_⟩
    have hPhysicalPlanMeasure :=
      congrArg
        (fun rho : FiniteMeasure (Euclidean n × Euclidean n) =>
          (rho : Measure (Euclidean n × Euclidean n)))
        hPhysicalPlan
    simpa only [physical, finiteGraphPlan,
      assembledRaywiseComponentFiber_toMeasure,
      maximalRaySourceFiber_toMeasure,
      FiniteMeasure.toMeasure_map] using hPhysicalPlanMeasure
  have hfst :
      Kernel.fst (assembledRaywiseKernel D gamma gammaLift)
        =ᵐ[(D.sigma : Measure (OrientedOpenRay n))] D.source := by
    simpa only [Kernel.fst_eq] using
      assembledRaywiseKernel_map_fst_ae D gamma gammaLift
  obtain ⟨T, hT, hGraphMeasure⟩ :=
    kernelComposition_eq_graphMap_of_ae_fiber_graph
      n D.sigma D.source
      (assembledRaywiseKernel D gamma gammaLift)
      D.pointRay D.measurable_pointRay hfst
      D.source_ae_fiber_eq hfiberGraph
  rw [assembledRaywiseKernel_reconstruction
      D gamma hSupported gammaLift,
    D.source_reconstruction] at hGraphMeasure
  have hGraph :
      IsGraphPlan
        (assembledRaywiseCoupling
          D gamma hSupported gammaLift) T := by
    refine ⟨hT, ?_⟩
    apply FiniteMeasure.toMeasure_injective
    simpa only [finiteGraphPlan,
      FiniteMeasure.toMeasure_map] using hGraphMeasure
  obtain ⟨hT', hConditional⟩ :=
    condDistrib_ae_eq_deterministic_of_isGraphPlan
      (assembledRaywiseCoupling
        D gamma hSupported gammaLift) T hGraph
  exact ⟨T, hT', hGraph, hConditional⟩

/-- All coordinate-inheritance hypotheses used above are already consequences
of the maximal-ray assembly data. Thus the a.e. excursion premise alone is
the remaining graph input. -/
theorem assembledRaywiseCoupling_graph_and_condDistrib_ae_deterministic_of_weakPremise
    {n : Nat}
    {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hAtomless :
      CountablyLipschitzRayCoordinateAtomlessPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hSingular : FiniteMutuallySingular mu nu)
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hExcursion :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          ((assembledRaywiseComponentFiber D gamma gammaLift R).map
            fun z =>
              (rayCoordinate R z.1, rayCoordinate R z.2))) :
    exists T : Euclidean n -> Euclidean n,
      exists hT : Measurable T,
        IsGraphPlan
            (assembledRaywiseCoupling
              D gamma hSupported gammaLift) T ∧
          condDistrib Prod.snd Prod.fst
              ((assembledRaywiseCoupling
                D gamma hSupported gammaLift).plan :
                  Measure (Euclidean n × Euclidean n))
            =ᵐ[(mu : Measure (Euclidean n))]
              Kernel.deterministic T hT := by
  have hInheritance :=
    assembledRaywiseCoordinateInheritance_ae_of_weakPremise
      D hRegularity gamma hSupported gammaLift hLiftedForward
      hmuAC hAtomless hSingular hFirstMu hFirstNu
  exact
    assembledRaywiseCoupling_graph_and_condDistrib_ae_deterministic_of_inheritance
      D gamma hSupported gammaLift hLiftedForward
      hInheritance hExcursion

theorem assembledRaywiseCoupling_graph_and_condDistrib_ae_deterministic
    {n : Nat}
    {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hCoarea :
      CountablyLipschitzRayCoareaPremise
        mu Gamma hRegularity D.rayAssignment D.defaultRay)
    (hSingular : FiniteMutuallySingular mu nu)
    (hFirstMu :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hFirstNu :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hExcursion :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        IsJuilletExcursionPlan
          ((maximalRaySourceFiber D R).map (rayCoordinate R))
          ((maximalRayTargetFiber D gamma R).map (rayCoordinate R))
          ((assembledRaywiseComponentFiber D gamma gammaLift R).map
            fun z =>
              (rayCoordinate R z.1, rayCoordinate R z.2))) :
    exists T : Euclidean n -> Euclidean n,
      exists hT : Measurable T,
        IsGraphPlan
            (assembledRaywiseCoupling
              D gamma hSupported gammaLift) T ∧
          condDistrib Prod.snd Prod.fst
              ((assembledRaywiseCoupling
                D gamma hSupported gammaLift).plan :
                  Measure (Euclidean n × Euclidean n))
            =ᵐ[(mu : Measure (Euclidean n))]
              Kernel.deterministic T hT := by
  exact
    assembledRaywiseCoupling_graph_and_condDistrib_ae_deterministic_of_weakPremise
      D hRegularity gamma hSupported gammaLift hLiftedForward
      hmuAC
      (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
        mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
      hSingular hFirstMu hFirstNu hExcursion

end ConcaveOTLimit
