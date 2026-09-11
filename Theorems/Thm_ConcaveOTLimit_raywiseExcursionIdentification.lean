import Theorems.Thm_ConcaveOTLimit_raywiseCoordinateInheritance
import Theorems.Thm_ConcaveOTLimit_fiberwiseImprovementSelection
import Theorems.Thm_ConcaveOTLimit_existsJuilletExcursionPlan
import Theorems.Thm_ConcaveOTLimit_juilletExcursionPlanIsGraph
import Mathlib.Probability.Kernel.CondDistrib

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## Coordinate pullback on one ray -/

def rayCoordinatePair {n : Nat} (R : OrientedOpenRay n)
    (z : Euclidean n × Euclidean n) : Real × Real :=
  (rayCoordinate R z.1, rayCoordinate R z.2)

def rayPointPair {n : Nat} (R : OrientedOpenRay n)
    (z : Real × Real) : Euclidean n × Euclidean n :=
  (R.point z.1, R.point z.2)

theorem measurable_rayCoordinatePair {n : Nat} (R : OrientedOpenRay n) :
    Measurable (rayCoordinatePair R) := by
  exact (measurable_rayCoordinate R).prodMap (measurable_rayCoordinate R)

theorem measurable_rayPointPair {n : Nat} (R : OrientedOpenRay n) :
    Measurable (rayPointPair R) := by
  exact
    (OrientedOpenRay.measurable_point R).prodMap
      (OrientedOpenRay.measurable_point R)

@[simp]
theorem rayCoordinatePair_rayPointPair {n : Nat}
    (R : OrientedOpenRay n) (z : Real × Real) :
    rayCoordinatePair R (rayPointPair R z) = z := by
  ext <;> simp [rayCoordinatePair, rayPointPair,
    rayCoordinate_point_apply]

theorem rayPoint_dist_eq {n : Nat} (R : OrientedOpenRay n)
    (s t : Real) :
    dist (R.point s) (R.point t) = dist s t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  rw [dist_eq_norm, Real.dist_eq]
  simp only [OrientedOpenRay.point, add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs]

theorem dist_eq_norm_rayCoordinate_sub_of_mem_closure
    {n : Nat} (R : OrientedOpenRay n) {x y : Euclidean n}
    (hx : x ∈ closure R.carrier) (hy : y ∈ closure R.carrier) :
    dist x y = ‖rayCoordinate R x - rayCoordinate R y‖ := by
  calc
    dist x y =
        dist (R.point (rayCoordinate R x))
          (R.point (rayCoordinate R y)) := by
      rw [rayPoint_rayCoordinate_eq_of_mem_closure R hx,
        rayPoint_rayCoordinate_eq_of_mem_closure R hy]
    _ = dist (rayCoordinate R x) (rayCoordinate R y) :=
      rayPoint_dist_eq R _ _
    _ = ‖rayCoordinate R x - rayCoordinate R y‖ := dist_eq_norm _ _

theorem map_rayPoint_map_rayCoordinate_eq_of_mem_closure
    {n : Nat} (R : OrientedOpenRay n)
    (rho : FiniteMeasure (Euclidean n))
    (hOnRay :
      ∀ᵐ x ∂(rho : Measure (Euclidean n)), x ∈ closure R.carrier) :
    (rho.map (rayCoordinate R)).map R.point = rho := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map]
  rw [Measure.map_map
    (OrientedOpenRay.measurable_point R) (measurable_rayCoordinate R)]
  calc
    Measure.map (R.point ∘ rayCoordinate R)
        (rho : Measure (Euclidean n)) =
        Measure.map id (rho : Measure (Euclidean n)) := by
      apply Measure.map_congr
      filter_upwards [hOnRay] with x hx
      exact rayPoint_rayCoordinate_eq_of_mem_closure R hx
    _ = (rho : Measure (Euclidean n)) := Measure.map_id

theorem map_rayPointPair_map_rayCoordinatePair_eq_of_mem_closure
    {n : Nat} (R : OrientedOpenRay n)
    (eta : FiniteMeasure (Euclidean n × Euclidean n))
    (hOnRay :
      ∀ᵐ z ∂(eta : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier) :
    (eta.map (rayCoordinatePair R)).map (rayPointPair R) = eta := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_rayPointPair R) (measurable_rayCoordinatePair R)]
  calc
    Measure.map (rayPointPair R ∘ rayCoordinatePair R)
        (eta : Measure (Euclidean n × Euclidean n)) =
        Measure.map id
          (eta : Measure (Euclidean n × Euclidean n)) := by
      apply Measure.map_congr
      filter_upwards [hOnRay] with z hz
      apply Prod.ext
      · exact rayPoint_rayCoordinate_eq_of_mem_closure R hz.1
      · exact rayPoint_rayCoordinate_eq_of_mem_closure R hz.2
    _ = (eta : Measure (Euclidean n × Euclidean n)) := Measure.map_id

theorem finiteMeasure_eq_of_rayCoordinatePair_map_eq
    {n : Nat} (R : OrientedOpenRay n)
    (eta xi : FiniteMeasure (Euclidean n × Euclidean n))
    (heta :
      ∀ᵐ z ∂(eta : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hxi :
      ∀ᵐ z ∂(xi : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier)
    (hmap :
      eta.map (rayCoordinatePair R) =
        xi.map (rayCoordinatePair R)) :
    eta = xi := by
  rw [← map_rayPointPair_map_rayCoordinatePair_eq_of_mem_closure
      R eta heta,
    ← map_rayPointPair_map_rayCoordinatePair_eq_of_mem_closure
      R xi hxi,
    hmap]

noncomputable def rayCoordinateCouplingPullback
    {n : Nat} (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (hSourceOnRay :
      ∀ᵐ x ∂(source : Measure (Euclidean n)),
        x ∈ closure R.carrier)
    (hTargetOnRay :
      ∀ᵐ y ∂(target : Measure (Euclidean n)),
        y ∈ closure R.carrier)
    (eta :
      FiniteCoupling
        (source.map (rayCoordinate R))
        (target.map (rayCoordinate R))) :
    FiniteCoupling source target := by
  have hSource :
      (source.map (rayCoordinate R)).map R.point = source :=
    map_rayPoint_map_rayCoordinate_eq_of_mem_closure
      R source hSourceOnRay
  have hTarget :
      (target.map (rayCoordinate R)).map R.point = target :=
    map_rayPoint_map_rayCoordinate_eq_of_mem_closure
      R target hTargetOnRay
  refine ⟨eta.plan.map (rayPointPair R), ?_, ?_⟩
  · apply FiniteMeasure.toMeasure_injective
    simp only [firstMarginal, FiniteMeasure.toMeasure_map]
    rw [Measure.map_map measurable_fst (measurable_rayPointPair R)]
    change
      Measure.map (R.point ∘ Prod.fst)
          (eta.plan : Measure (Real × Real)) =
        (source : Measure (Euclidean n))
    rw [← Measure.map_map
      (OrientedOpenRay.measurable_point R) measurable_fst]
    have hEtaSource :
        Measure.map Prod.fst
            (eta.plan : Measure (Real × Real)) =
          (source.map (rayCoordinate R) : Measure Real) := by
      simpa [firstMarginal, FiniteCoupling.plan] using congrArg
        (fun rho : FiniteMeasure Real => (rho : Measure Real))
        eta.property.1
    rw [hEtaSource]
    simpa only [FiniteMeasure.toMeasure_map] using congrArg
      (fun rho : FiniteMeasure (Euclidean n) =>
        (rho : Measure (Euclidean n))) hSource
  · apply FiniteMeasure.toMeasure_injective
    simp only [secondMarginal, FiniteMeasure.toMeasure_map]
    rw [Measure.map_map measurable_snd (measurable_rayPointPair R)]
    change
      Measure.map (R.point ∘ Prod.snd)
          (eta.plan : Measure (Real × Real)) =
        (target : Measure (Euclidean n))
    rw [← Measure.map_map
      (OrientedOpenRay.measurable_point R) measurable_snd]
    have hEtaTarget :
        Measure.map Prod.snd
            (eta.plan : Measure (Real × Real)) =
          (target.map (rayCoordinate R) : Measure Real) := by
      simpa [secondMarginal, FiniteCoupling.plan] using congrArg
        (fun rho : FiniteMeasure Real => (rho : Measure Real))
        eta.property.2
    rw [hEtaTarget]
    simpa only [FiniteMeasure.toMeasure_map] using congrArg
      (fun rho : FiniteMeasure (Euclidean n) =>
        (rho : Measure (Euclidean n))) hTarget

@[simp]
theorem rayCoordinateCouplingPullback_plan
    {n : Nat} (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (hSourceOnRay :
      ∀ᵐ x ∂(source : Measure (Euclidean n)),
        x ∈ closure R.carrier)
    (hTargetOnRay :
      ∀ᵐ y ∂(target : Measure (Euclidean n)),
        y ∈ closure R.carrier)
    (eta :
      FiniteCoupling
        (source.map (rayCoordinate R))
        (target.map (rayCoordinate R))) :
    (rayCoordinateCouplingPullback R source target
        hSourceOnRay hTargetOnRay eta).plan =
      eta.plan.map (rayPointPair R) := by
  rfl

def rayCoordinateForwardCouplingSet
    {n : Nat} (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n)) :
    Set (FiniteCoupling source target) :=
  {eta |
    ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
      rayCoordinate R z.1 ≤ rayCoordinate R z.2}

theorem rayCoordinateCouplingPullback_mem_forward
    {n : Nat} (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (hSourceOnRay :
      ∀ᵐ x ∂(source : Measure (Euclidean n)),
        x ∈ closure R.carrier)
    (hTargetOnRay :
      ∀ᵐ y ∂(target : Measure (Euclidean n)),
        y ∈ closure R.carrier)
    (eta :
      FiniteCoupling
        (source.map (rayCoordinate R))
        (target.map (rayCoordinate R)))
    (hForward : IsForwardPlan eta) :
    rayCoordinateCouplingPullback R source target
        hSourceOnRay hTargetOnRay eta ∈
      rayCoordinateForwardCouplingSet R source target := by
  unfold rayCoordinateForwardCouplingSet
  simp only [Set.mem_setOf_eq]
  rw [rayCoordinateCouplingPullback_plan]
  simp only [FiniteMeasure.toMeasure_map]
  apply
    (ae_map_iff (measurable_rayPointPair R).aemeasurable
      (measurableSet_le
        ((measurable_rayCoordinate R).comp measurable_fst)
        ((measurable_rayCoordinate R).comp measurable_snd))).2
  filter_upwards [hForward] with z hz
  simpa only [Function.comp_apply, rayPointPair,
    rayCoordinate_point_apply] using hz

/-! ## Strict-exponential cost transfer -/

theorem strictExponentialProfileCost_map_rayPoint
    {n : Nat} (R : OrientedOpenRay n)
    {source target : FiniteMeasure Real}
    (eta : FiniteCoupling source target) :
    profileCost strictExponentialProfile
        (mapFiniteCoupling eta R.point R.point
          (OrientedOpenRay.measurable_point R)
          (OrientedOpenRay.measurable_point R)) =
      profileCost strictExponentialProfile eta := by
  unfold profileCost
  simp only [mapFiniteCoupling_plan, FiniteMeasure.toMeasure_map]
  change
    (∫ z, strictExponentialProfile ‖z.1 - z.2‖
      ∂Measure.map (rayPointPair R)
        (eta.plan : Measure (Real × Real))) =
      ∫ z, strictExponentialProfile ‖z.1 - z.2‖
        ∂(eta.plan : Measure (Real × Real))
  have hCostMeasurable :
      AEStronglyMeasurable
        (fun z : Euclidean n × Euclidean n =>
          strictExponentialProfile ‖z.1 - z.2‖)
        (Measure.map (rayPointPair R)
          (eta.plan : Measure (Real × Real))) :=
    (continuous_strictExponentialProfile.comp
      (continuous_norm.comp
        (continuous_fst.sub continuous_snd))).aestronglyMeasurable
  rw [integral_map
    (μ := (eta.plan : Measure (Real × Real)))
    (φ := rayPointPair R)
    (f := fun z : Euclidean n × Euclidean n =>
      strictExponentialProfile ‖z.1 - z.2‖)
    (measurable_rayPointPair R).aemeasurable
    hCostMeasurable]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [rayPointPair, strictExponentialProfile]
  rw [show ‖R.point z.1 - R.point z.2‖ = ‖z.1 - z.2‖ by
    simpa only [dist_eq_norm] using rayPoint_dist_eq R z.1 z.2]

theorem strictExponentialProfileCost_map_rayCoordinate
    {n : Nat} (R : OrientedOpenRay n)
    {source target : FiniteMeasure (Euclidean n)}
    (eta : FiniteCoupling source target)
    (hOnRay :
      ∀ᵐ z ∂(eta.plan : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier) :
    profileCost strictExponentialProfile
        (mapFiniteCoupling eta (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R) (measurable_rayCoordinate R)) =
      profileCost strictExponentialProfile eta := by
  unfold profileCost
  simp only [mapFiniteCoupling_plan, FiniteMeasure.toMeasure_map]
  change
    (∫ z, strictExponentialProfile ‖z.1 - z.2‖
      ∂Measure.map (rayCoordinatePair R)
        (eta.plan : Measure (Euclidean n × Euclidean n))) =
      ∫ z, strictExponentialProfile ‖z.1 - z.2‖
        ∂(eta.plan : Measure (Euclidean n × Euclidean n))
  have hCostMeasurable :
      AEStronglyMeasurable
        (fun z : Real × Real =>
          strictExponentialProfile ‖z.1 - z.2‖)
        (Measure.map (rayCoordinatePair R)
          (eta.plan :
            Measure (Euclidean n × Euclidean n))) :=
    (continuous_strictExponentialProfile.comp
      (continuous_norm.comp
        (continuous_fst.sub continuous_snd))).aestronglyMeasurable
  rw [integral_map
    (μ := (eta.plan :
      Measure (Euclidean n × Euclidean n)))
    (φ := rayCoordinatePair R)
    (f := fun z : Real × Real =>
      strictExponentialProfile ‖z.1 - z.2‖)
    (measurable_rayCoordinatePair R).aemeasurable
    hCostMeasurable]
  apply integral_congr_ae
  filter_upwards [hOnRay] with z hz
  simp only [rayCoordinatePair, strictExponentialProfile]
  rw [← dist_eq_norm_rayCoordinate_sub_of_mem_closure R hz.1 hz.2,
    dist_eq_norm]

theorem strictExponentialProfileCost_rayCoordinateCouplingPullback
    {n : Nat} (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (hSourceOnRay :
      ∀ᵐ x ∂(source : Measure (Euclidean n)),
        x ∈ closure R.carrier)
    (hTargetOnRay :
      ∀ᵐ y ∂(target : Measure (Euclidean n)),
        y ∈ closure R.carrier)
    (eta :
      FiniteCoupling
        (source.map (rayCoordinate R))
        (target.map (rayCoordinate R))) :
    profileCost strictExponentialProfile
        (rayCoordinateCouplingPullback R source target
          hSourceOnRay hTargetOnRay eta) =
    profileCost strictExponentialProfile eta := by
  unfold profileCost
  rw [rayCoordinateCouplingPullback_plan]
  simp only [FiniteMeasure.toMeasure_map]
  have hCostMeasurable :
      AEStronglyMeasurable
        (fun z : Euclidean n × Euclidean n =>
          strictExponentialProfile ‖z.1 - z.2‖)
        (Measure.map (rayPointPair R)
          (eta.plan : Measure (Real × Real))) :=
    (continuous_strictExponentialProfile.comp
      (continuous_norm.comp
        (continuous_fst.sub continuous_snd))).aestronglyMeasurable
  rw [integral_map
    (μ := (eta.plan : Measure (Real × Real)))
    (φ := rayPointPair R)
    (f := fun z : Euclidean n × Euclidean n =>
      strictExponentialProfile ‖z.1 - z.2‖)
    (measurable_rayPointPair R).aemeasurable
    hCostMeasurable]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [rayPointPair, strictExponentialProfile]
  rw [show ‖R.point z.1 - R.point z.2‖ = ‖z.1 - z.2‖ by
    simpa only [dist_eq_norm] using rayPoint_dist_eq R z.1 z.2]

theorem strictExponentialCoordinate_minimal_of_ray_minimal
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (physical : FiniteCoupling source target)
    (hInheritance :
      RaywiseCoordinateInheritance Gamma R source target physical.plan)
    (hSourceOnRay :
      ∀ᵐ x ∂(source : Measure (Euclidean n)),
        x ∈ closure R.carrier)
    (hTargetOnRay :
      ∀ᵐ y ∂(target : Measure (Euclidean n)),
        y ∈ closure R.carrier)
    (hMinimal :
      IsMinimizerOn
        (rayCoordinateForwardCouplingSet R source target)
        (profileCost strictExponentialProfile) physical) :
    IsMinimizerOn
      {eta :
          FiniteCoupling
            (source.map (rayCoordinate R))
            (target.map (rayCoordinate R)) |
        IsForwardPlan eta}
      (profileCost strictExponentialProfile)
      hInheritance.coordinateCoupling := by
  have hCoordinateEq :
      hInheritance.coordinateCoupling =
        mapFiniteCoupling physical (rayCoordinate R) (rayCoordinate R)
          (measurable_rayCoordinate R)
          (measurable_rayCoordinate R) := by
    apply Subtype.ext
    rfl
  refine ⟨hInheritance.coordinateCoupling_isForward, ?_⟩
  intro eta hEta
  let etaBack :=
    rayCoordinateCouplingPullback R source target
      hSourceOnRay hTargetOnRay eta
  have hEtaBack :
      etaBack ∈ rayCoordinateForwardCouplingSet R source target :=
    rayCoordinateCouplingPullback_mem_forward
      R source target hSourceOnRay hTargetOnRay eta hEta
  have hLe := hMinimal.2 etaBack hEtaBack
  rw [hCoordinateEq,
    strictExponentialProfileCost_map_rayCoordinate
      R physical hInheritance.componentOnRay]
  simpa only [etaBack,
    strictExponentialProfileCost_rayCoordinateCouplingPullback] using hLe

/-! ## Graph and conditional-law adapters -/

theorem ae_target_eq_of_isGraphPlan
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableEq Y]
    {source : FiniteMeasure X} {target : FiniteMeasure Y}
    (gamma : FiniteCoupling source target) (T : X → Y)
    (hGraph : IsGraphPlan gamma T) :
    ∀ᵐ z ∂(gamma.plan : Measure (X × Y)), z.2 = T z.1 := by
  obtain ⟨hT, hPlan⟩ := hGraph
  rw [hPlan]
  change
    ∀ᵐ z ∂Measure.map (fun x => (x, T x)) (source : Measure X),
      z.2 = T z.1
  apply
    (ae_map_iff (measurable_id.prodMk hT).aemeasurable
      (measurableSet_eq_fun measurable_snd
        (hT.comp measurable_fst))).2
  exact Eventually.of_forall fun _ => rfl

theorem isGraphPlan_of_ae_target_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {source : FiniteMeasure X} {target : FiniteMeasure Y}
    (gamma : FiniteCoupling source target) (T : X → Y)
    (hT : Measurable T)
    (hTarget :
      ∀ᵐ z ∂(gamma.plan : Measure (X × Y)), z.2 = T z.1) :
    IsGraphPlan gamma T := by
  refine ⟨hT, ?_⟩
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteCoupling.plan, finiteGraphPlan,
    FiniteMeasure.toMeasure_map]
  have hFirst :
      Measure.map Prod.fst
          (gamma.plan : Measure (X × Y)) =
        (source : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X))
      gamma.property.1
  calc
    (gamma.plan : Measure (X × Y)) =
        Measure.map id
          (gamma.plan : Measure (X × Y)) := Measure.map_id.symm
    _ = Measure.map
          ((fun x => (x, T x)) ∘ Prod.fst)
          (gamma.plan : Measure (X × Y)) := by
      apply Measure.map_congr
      filter_upwards [hTarget] with z hz
      exact Prod.ext rfl hz
    _ = Measure.map (fun x => (x, T x))
          (Measure.map Prod.fst
            (gamma.plan : Measure (X × Y))) := by
      exact
        (Measure.map_map
          (show Measurable (fun x : X => (x, T x)) by
            exact measurable_id.prodMk hT)
          measurable_fst).symm
    _ = Measure.map (fun x => (x, T x))
          (source : Measure X) := by rw [hFirst]

theorem condDistrib_ae_eq_deterministic_of_isGraphPlan
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    {source : FiniteMeasure X} {target : FiniteMeasure Y}
    (gamma : FiniteCoupling source target) (T : X → Y)
    (hGraph : IsGraphPlan gamma T) :
    ∃ hT : Measurable T,
      condDistrib Prod.snd Prod.fst
          (gamma.plan : Measure (X × Y))
        =ᵐ[(source : Measure X)] Kernel.deterministic T hT := by
  obtain ⟨hT, hPlan⟩ := hGraph
  refine ⟨hT, ?_⟩
  have hTarget :=
    ae_target_eq_of_isGraphPlan gamma T ⟨hT, hPlan⟩
  have hFirst :
      Measure.map Prod.fst
          (gamma.plan : Measure (X × Y)) =
        (source : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X))
      gamma.property.1
  have hConditional :
      condDistrib Prod.snd Prod.fst
          (gamma.plan : Measure (X × Y))
        =ᵐ[Measure.map Prod.fst
          (gamma.plan : Measure (X × Y))]
          Kernel.deterministic T hT := by
    rw [condDistrib_congr_left hTarget]
    exact condDistrib_comp_self Prod.fst hT
  simpa only [hFirst] using hConditional

theorem rayPhysicalGraph_of_coordinateGraph
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (physical : FiniteCoupling source target)
    (hInheritance :
      RaywiseCoordinateInheritance Gamma R source target physical.plan)
    (T : Real → Real)
    (hCoordinateGraph :
      IsGraphPlan hInheritance.coordinateCoupling T) :
    IsGraphPlan physical
      (fun x => R.point (T (rayCoordinate R x))) := by
  obtain ⟨hT, hPlan⟩ := hCoordinateGraph
  have hCoordinateTarget :=
    ae_target_eq_of_isGraphPlan
      hInheritance.coordinateCoupling T ⟨hT, hPlan⟩
  have hCoordinateTargetPhysical :
      ∀ᵐ z ∂(physical.plan :
          Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.2 = T (rayCoordinate R z.1) := by
    apply
      (ae_map_iff (measurable_rayCoordinatePair R).aemeasurable
        (measurableSet_eq_fun measurable_snd
          (hT.comp measurable_fst))).1
    simpa only [RaywiseCoordinateInheritance.coordinateCoupling,
      rayCoordinatePair] using hCoordinateTarget
  have hPhysicalTarget :
      ∀ᵐ z ∂(physical.plan :
          Measure (Euclidean n × Euclidean n)),
        z.2 = R.point (T (rayCoordinate R z.1)) := by
    filter_upwards
        [hInheritance.componentOnRay,
          hCoordinateTargetPhysical] with z hzRay hzTarget
    calc
      z.2 = R.point (rayCoordinate R z.2) :=
        (rayPoint_rayCoordinate_eq_of_mem_closure R hzRay.2).symm
      _ = R.point (T (rayCoordinate R z.1)) := by rw [hzTarget]
  apply isGraphPlan_of_ae_target_eq physical
  · exact
      (OrientedOpenRay.measurable_point R).comp
        (hT.comp (measurable_rayCoordinate R))
  · exact hPhysicalTarget

theorem finiteCoupling_marginalMass_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {source : FiniteMeasure X} {target : FiniteMeasure Y}
    (gamma : FiniteCoupling source target) :
    source.mass = target.mass := by
  have hFirstMass :
      (firstMarginal gamma.plan).mass = source.mass :=
    congrArg FiniteMeasure.mass gamma.property.1
  have hSecondMass :
      (secondMarginal gamma.plan).mass = target.mass :=
    congrArg FiniteMeasure.mass gamma.property.2
  calc
    source.mass = (firstMarginal gamma.plan).mass := hFirstMass.symm
    _ = gamma.plan.mass := by
      simp [firstMarginal, FiniteMeasure.mass,
        FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ]
    _ = (secondMarginal gamma.plan).mass := by
      simp [secondMarginal, FiniteMeasure.mass,
        FiniteMeasure.map_apply _ measurable_snd MeasurableSet.univ]
    _ = target.mass := hSecondMass

/-! ## C173/C174 pointwise identification -/

structure RaywiseExcursionIdentification
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (physical : FiniteCoupling source target)
    (hInheritance :
      RaywiseCoordinateInheritance Gamma R source target physical.plan) :
    Prop where
  coordinateStrictExponentialMinimizer :
    IsMinimizerOn
      {eta :
          FiniteCoupling
            (source.map (rayCoordinate R))
            (target.map (rayCoordinate R)) |
        IsForwardPlan eta}
      (profileCost strictExponentialProfile)
      hInheritance.coordinateCoupling
  coordinateIsExcursion :
    IsJuilletExcursionPlan
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R))
      hInheritance.coordinateCoupling.plan
  coordinateExcursionUnique :
    ∀ eta :
        FiniteCoupling
          (source.map (rayCoordinate R))
          (target.map (rayCoordinate R)),
      IsJuilletExcursionPlan
          (source.map (rayCoordinate R))
          (target.map (rayCoordinate R)) eta.plan →
        eta = hInheritance.coordinateCoupling
  coordinateMonotoneArchSupport :
    ∃ S : Set (Real × Real),
      MeasurableSet S ∧
        IsSupported hInheritance.coordinateCoupling S ∧
        IsMonotoneArchSet S
  coordinateGraph :
    ∃ T : Real → Real,
      IsGraphPlan hInheritance.coordinateCoupling T
  componentRecovery :
    hInheritance.coordinateCoupling.plan.map (rayPointPair R) =
      physical.plan
  componentDeterminedByCoordinates :
    ∀ eta : FiniteCoupling source target,
      (∀ᵐ z ∂(eta.plan :
          Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier ∧ z.2 ∈ closure R.carrier) →
      eta.plan.map (rayCoordinatePair R) =
          hInheritance.coordinateCoupling.plan →
        eta = physical
  componentGraph :
    ∃ T : Euclidean n → Euclidean n, IsGraphPlan physical T
  componentConditionalDeterministic :
    ∃ (T : Euclidean n → Euclidean n) (hT : Measurable T),
      IsGraphPlan physical T ∧
        condDistrib Prod.snd Prod.fst
            (physical.plan :
              Measure (Euclidean n × Euclidean n))
          =ᵐ[(source : Measure (Euclidean n))]
            Kernel.deterministic T hT

theorem raywiseExcursionIdentification_of_strictExponentialMinimality
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)}
    (R : OrientedOpenRay n)
    (source target : FiniteMeasure (Euclidean n))
    (physical : FiniteCoupling source target)
    (hInheritance :
      RaywiseCoordinateInheritance Gamma R source target physical.plan)
    (hSourceOnRay :
      ∀ᵐ x ∂(source : Measure (Euclidean n)),
        x ∈ closure R.carrier)
    (hTargetOnRay :
      ∀ᵐ y ∂(target : Measure (Euclidean n)),
        y ∈ closure R.carrier)
    (hPositive :
      0 < (source.map (rayCoordinate R)).mass)
    (hPhysicalMinimal :
      IsMinimizerOn
        (rayCoordinateForwardCouplingSet R source target)
        (profileCost strictExponentialProfile) physical) :
    RaywiseExcursionIdentification
      R source target physical hInheritance := by
  let coordinate := hInheritance.coordinateCoupling
  have hMass :
      (source.map (rayCoordinate R)).mass =
        (target.map (rayCoordinate R)).mass :=
    finiteCoupling_marginalMass_eq coordinate
  have hCoordinateMinimal :
      IsMinimizerOn
        {eta :
            FiniteCoupling
              (source.map (rayCoordinate R))
              (target.map (rayCoordinate R)) |
          IsForwardPlan eta}
        (profileCost strictExponentialProfile) coordinate :=
    strictExponentialCoordinate_minimal_of_ray_minimal
      R source target physical hInheritance
      hSourceOnRay hTargetOnRay hPhysicalMinimal
  obtain ⟨gammaEC, _hECForward, hEC⟩ :=
    existsJuilletExcursionPlan
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R))
      hMass hPositive
      hInheritance.coordinateSourceFirstMoment
      hInheritance.coordinateTargetFirstMoment
      hInheritance.coordinateMarginalsMutuallySingular
      hInheritance.coordinateSourceAtomless
      hInheritance.coordinateTargetDominates
  have hVariational :=
    oneDimensionalExcursionVariational
      (source.map (rayCoordinate R))
      (target.map (rayCoordinate R))
      hMass hPositive
      hInheritance.coordinateSourceFirstMoment
      hInheritance.coordinateTargetFirstMoment
      hInheritance.coordinateMarginalsMutuallySingular
      hInheritance.coordinateSourceAtomless
      hInheritance.coordinateTargetDominates
      gammaEC hEC
  have hUniqueMinimizer :
      IsUniqueMinimizerOn
        {eta :
            FiniteCoupling
              (source.map (rayCoordinate R))
              (target.map (rayCoordinate R)) |
          IsForwardPlan eta}
        (profileCost strictExponentialProfile) gammaEC :=
    hVariational.2.2.2
      strictExponentialProfile strictExponentialProfile_admissible
  have hCoordinateEq : coordinate = gammaEC :=
    hUniqueMinimizer.2 coordinate hCoordinateMinimal
  have hCoordinateExcursion :
      IsJuilletExcursionPlan
        (source.map (rayCoordinate R))
        (target.map (rayCoordinate R)) coordinate.plan := by
    rw [hCoordinateEq]
    exact hEC
  have hCoordinateUnique :
      ∀ eta :
          FiniteCoupling
            (source.map (rayCoordinate R))
            (target.map (rayCoordinate R)),
        IsJuilletExcursionPlan
            (source.map (rayCoordinate R))
            (target.map (rayCoordinate R)) eta.plan →
          eta = coordinate := by
    intro eta hEta
    exact monotoneArchPlan_unique
      hInheritance.coordinateSourceAtomless
      hInheritance.coordinateTargetDominates
      eta coordinate hEta hCoordinateExcursion
  obtain ⟨S, hSMeasurable, hSFull, hSMonotone⟩ :=
    hCoordinateExcursion.2
  obtain ⟨TCoordinate, hCoordinateGraph⟩ :=
    juilletExcursionPlanIsGraph coordinate
      hInheritance.coordinateMarginalsMutuallySingular
      hInheritance.coordinateSourceAtomless
      hInheritance.coordinateTargetDominates
      hCoordinateExcursion
  let TPhysical : Euclidean n → Euclidean n :=
    fun x => R.point (TCoordinate (rayCoordinate R x))
  have hPhysicalGraph : IsGraphPlan physical TPhysical :=
    rayPhysicalGraph_of_coordinateGraph
      R source target physical hInheritance
      TCoordinate hCoordinateGraph
  obtain ⟨hTPhysical, hConditional⟩ :=
    condDistrib_ae_eq_deterministic_of_isGraphPlan
      physical TPhysical hPhysicalGraph
  refine {
    coordinateStrictExponentialMinimizer := hCoordinateMinimal
    coordinateIsExcursion := hCoordinateExcursion
    coordinateExcursionUnique := hCoordinateUnique
    coordinateMonotoneArchSupport :=
      ⟨S, hSMeasurable, hSFull, hSMonotone⟩
    coordinateGraph := ⟨TCoordinate, hCoordinateGraph⟩
    componentRecovery := ?_
    componentDeterminedByCoordinates := ?_
    componentGraph := ⟨TPhysical, hPhysicalGraph⟩
    componentConditionalDeterministic :=
      ⟨TPhysical, hTPhysical, hPhysicalGraph, hConditional⟩
  }
  · change
      (physical.plan.map (rayCoordinatePair R)).map
          (rayPointPair R) =
        physical.plan
    exact
      map_rayPointPair_map_rayCoordinatePair_eq_of_mem_closure
        R physical.plan hInheritance.componentOnRay
  · intro eta hEtaOnRay hEtaCoordinate
    apply Subtype.ext
    apply finiteMeasure_eq_of_rayCoordinatePair_map_eq
      R eta.plan physical.plan hEtaOnRay hInheritance.componentOnRay
    simpa only [RaywiseCoordinateInheritance.coordinateCoupling]
      using hEtaCoordinate

/-! ## Canonical maximal-ray assembly -/

noncomputable def assembledRaywisePhysicalCoupling
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n)
    (hCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R)) :
    FiniteCoupling
      (maximalRaySourceFiber D R)
      (maximalRayTargetFiber D gamma R) :=
  ⟨assembledRaywiseComponentFiber D gamma gammaLift R, hCoupling⟩

@[simp]
theorem assembledRaywisePhysicalCoupling_plan
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n)
    (hCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R)) :
    (assembledRaywisePhysicalCoupling
      D gamma gammaLift R hCoupling).plan =
        assembledRaywiseComponentFiber D gamma gammaLift R :=
  rfl

/-- The complete pointwise output needed after localization. It records the
physical coupling proof and the inherited coordinate hypotheses together
with C173/C174 identification, graphness, and component determinism. -/
def CanonicalRaywiseExcursionIdentification
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n) : Prop :=
  ∃ hCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R),
    ∃ hInheritance :
        RaywiseCoordinateInheritance Gamma R
          (maximalRaySourceFiber D R)
          (maximalRayTargetFiber D gamma R)
          (assembledRaywiseComponentFiber D gamma gammaLift R),
      RaywiseExcursionIdentification R
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywisePhysicalCoupling
          D gamma gammaLift R hCoupling)
        hInheritance

theorem assembledRaywisePhysical_minimal_of_fiberMinimality
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (R : OrientedOpenRay n)
    (hCoupling :
      IsFiniteCoupling
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R)
        (assembledRaywiseComponentFiber D gamma gammaLift R))
    (hMinimal :
      IsMinimizerOn
        (fiberCouplingSet D.source
          (maximalRayTargetKernel D gamma)
          (rayForwardFiberCarrier n) R)
        (fiberMeasureCost rayStrictExponentialFiberCost R)
        (assembledRaywiseKernel D gamma gammaLift R)) :
    IsMinimizerOn
      (rayCoordinateForwardCouplingSet R
        (maximalRaySourceFiber D R)
        (maximalRayTargetFiber D gamma R))
      (profileCost strictExponentialProfile)
      (assembledRaywisePhysicalCoupling
        D gamma gammaLift R hCoupling) := by
  refine ⟨?_, ?_⟩
  · simpa only [rayCoordinateForwardCouplingSet,
      assembledRaywisePhysicalCoupling_plan,
      assembledRaywiseComponentFiber_toMeasure,
      rayForwardFiberCarrier, mem_setOf_eq] using hMinimal.1.2.2
  · intro eta hEtaForward
    have hEtaSource :
        Measure.map Prod.fst
            (eta.plan : Measure (Euclidean n × Euclidean n)) =
          D.source R := by
      simpa [firstMarginal, FiniteCoupling.plan] using congrArg
        (fun rho : FiniteMeasure (Euclidean n) =>
          (rho : Measure (Euclidean n))) eta.property.1
    have hEtaTarget :
        Measure.map Prod.snd
            (eta.plan : Measure (Euclidean n × Euclidean n)) =
          maximalRayTargetKernel D gamma R := by
      simpa [secondMarginal, FiniteCoupling.plan] using congrArg
        (fun rho : FiniteMeasure (Euclidean n) =>
          (rho : Measure (Euclidean n))) eta.property.2
    have hEtaFeasible :
        (eta.plan : Measure (Euclidean n × Euclidean n)) ∈
          fiberCouplingSet D.source
            (maximalRayTargetKernel D gamma)
            (rayForwardFiberCarrier n) R :=
      ⟨hEtaSource, hEtaTarget, hEtaForward⟩
    have hLe := hMinimal.2 (eta.plan : Measure _) hEtaFeasible
    simpa [profileCost, fiberMeasureCost,
      strictExponentialProfile, rayStrictExponentialFiberCost,
      dist_eq_norm, assembledRaywisePhysicalCoupling,
      assembledRaywiseComponentFiber_toMeasure] using hLe

theorem maximalRayCoordinateSource_mass_eq_one
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (R : OrientedOpenRay n) :
    (maximalRayCoordinateSource D R).mass = 1 := by
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change
    Measure.map (rayCoordinate R) (D.source R) univ = 1
  rw [Measure.map_apply
    (measurable_rayCoordinate R) MeasurableSet.univ]
  exact (D.source_isMarkovKernel.isProbabilityMeasure R).measure_univ

/-- Coarea and the inherited ray geometry turn localized physical
minimality into the full C173/C174 identification package almost
everywhere. No additional coordinate competitor-transfer premise is
needed. -/
theorem canonicalRaywiseExcursionIdentification_ae_of_weakPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
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
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      CanonicalRaywiseExcursionIdentification
        D gamma gammaLift R := by
  have hInheritance :=
    assembledRaywiseCoordinateInheritance_ae_of_weakPremise
      D hRegularity gamma hSupported gammaLift hLiftedForward
      hmuAC hAtomless hSingular hFirstMu hFirstNu
  have hCoupling :=
    assembledRaywiseComponent_isCoupling_ae
      D gamma gammaLift hLiftedForward
  have hSourceOnRay := D.source_on_ray_ae
  have hTargetOnRay :=
    maximalRayTarget_on_ray_ae D gamma hSupported
  filter_upwards
      [hInheritance, hCoupling, hSourceOnRay,
        hTargetOnRay, hFiberMinimal] with
      R hRInheritance hRCoupling hRSource hRTarget hRMinimal
  have hSourceClosure :
      ∀ᵐ x ∂(maximalRaySourceFiber D R :
          Measure (Euclidean n)),
        x ∈ closure R.carrier :=
    hRSource.mono fun _ hx => subset_closure hx
  have hPhysicalMinimal :=
    assembledRaywisePhysical_minimal_of_fiberMinimality
      D gamma gammaLift R hRCoupling hRMinimal
  have hPositive :
      0 < (maximalRayCoordinateSource D R).mass := by
    rw [maximalRayCoordinateSource_mass_eq_one D R]
    exact zero_lt_one
  refine ⟨hRCoupling, hRInheritance, ?_⟩
  exact
    raywiseExcursionIdentification_of_strictExponentialMinimality
      R (maximalRaySourceFiber D R)
      (maximalRayTargetFiber D gamma R)
      (assembledRaywisePhysicalCoupling
        D gamma gammaLift R hRCoupling)
      hRInheritance hSourceClosure hRTarget
      hPositive hPhysicalMinimal

theorem canonicalRaywiseExcursionIdentification_ae
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
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
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      CanonicalRaywiseExcursionIdentification
        D gamma gammaLift R := by
  exact canonicalRaywiseExcursionIdentification_ae_of_weakPremise
    D hRegularity gamma hSupported gammaLift hLiftedForward
    hmuAC
    (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
      mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
    hSingular hFirstMu hFirstNu hFiberMinimal

/-- Architecture-facing projection: canonical fiber minimality identifies
the coordinate component as Juillet's unique monotone-arch coupling almost
everywhere. -/
theorem canonicalRayFiberMinimality_identifiesExcursion_of_weakPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
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
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsJuilletExcursionPlan
        (maximalRayCoordinateSource D R)
        (maximalRayCoordinateTarget D gamma R)
        (assembledRaywiseCoordinateComponent
          D gamma gammaLift R) := by
  filter_upwards
      [canonicalRaywiseExcursionIdentification_ae_of_weakPremise
        D hRegularity gamma hSupported gammaLift hLiftedForward
        hmuAC hAtomless hSingular hFirstMu hFirstNu hFiberMinimal] with
      R hR
  obtain ⟨_hCoupling, hInheritance, hIdentification⟩ := hR
  simpa only [maximalRayCoordinateSource,
    maximalRayCoordinateTarget,
    assembledRaywiseCoordinateComponent,
    rayCoordinatePair,
    RaywiseCoordinateInheritance.coordinateCoupling] using
    hIdentification.coordinateIsExcursion

theorem canonicalRayFiberMinimality_identifiesExcursion
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
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
    (hFiberMinimal :
      CanonicalRayFiberMinimality D gamma gammaLift) :
    ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
      IsJuilletExcursionPlan
        (maximalRayCoordinateSource D R)
        (maximalRayCoordinateTarget D gamma R)
        (assembledRaywiseCoordinateComponent
          D gamma gammaLift R) := by
  exact canonicalRayFiberMinimality_identifiesExcursion_of_weakPremise
    D hRegularity gamma hSupported gammaLift hLiftedForward
    hmuAC
    (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
      mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
    hSingular hFirstMu hFirstNu hFiberMinimal

/-- Under the explicit coarea and canonical rational-gap selector premises,
there exists a canonical lifted minimizer whose components have the full
raywise excursion-identification package almost everywhere. -/
theorem existsCanonicalRayLiftedMinimizer_with_raywiseExcursionIdentification_of_weakPremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
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
    (hSelection :
      MaximalRayKernelDisintegration.CanonicalRayForwardRationalGapMeasurableSelectionPremise
        D gamma) :
    ∃ gammaLift :
        FiniteCoupling
          (maximalRayLiftedSource D)
          (maximalRayLiftedTarget D gamma),
      IsCanonicalRayLiftedMinimizer D gamma gammaLift ∧
        CanonicalRayFiberMinimality D gamma gammaLift ∧
        ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
          CanonicalRaywiseExcursionIdentification
            D gamma gammaLift R := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  have hImprovementSelection :
      RayForwardFiberwiseImprovementSelectionPremise
        D.sigma D.source (maximalRayTargetKernel D gamma) := by
    simpa only [maximalRayTargetKernel] using
      D.rayForwardFiberwiseImprovementSelectionPremise_of_canonical
        gamma hSelection
  obtain ⟨gammaLift, hGlobal, hFiberRaw⟩ :=
    existsCanonicalRayLiftedMinimizer_with_fiberwiseMinimality
      D gamma hSupported hImprovementSelection
  have hFiber :
      CanonicalRayFiberMinimality D gamma gammaLift := by
    unfold CanonicalRayFiberMinimality
    simpa only
        [assembledRaywiseKernel_eq_componentKernelOfLiftedCoupling] using
      hFiberRaw
  have hIdentification :=
    canonicalRaywiseExcursionIdentification_ae_of_weakPremise
      D hRegularity gamma hSupported gammaLift hGlobal.1
      hmuAC hAtomless hSingular hFirstMu hFirstNu hFiber
  exact ⟨gammaLift, hGlobal, hFiber, hIdentification⟩

theorem existsCanonicalRayLiftedMinimizer_with_raywiseExcursionIdentification
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
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
    (hSelection :
      MaximalRayKernelDisintegration.CanonicalRayForwardRationalGapMeasurableSelectionPremise
        D gamma) :
    ∃ gammaLift :
        FiniteCoupling
          (maximalRayLiftedSource D)
          (maximalRayLiftedTarget D gamma),
      IsCanonicalRayLiftedMinimizer D gamma gammaLift ∧
        CanonicalRayFiberMinimality D gamma gammaLift ∧
        ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
          CanonicalRaywiseExcursionIdentification
            D gamma gammaLift R := by
  exact
    existsCanonicalRayLiftedMinimizer_with_raywiseExcursionIdentification_of_weakPremise
      D hRegularity gamma hSupported hmuAC
      (coordinateAtomlessPremise_of_countablyLipschitzRayCoarea
        mu Gamma hRegularity D.rayAssignment D.defaultRay hCoarea)
      hSingular hFirstMu hFirstNu hSelection

end ConcaveOTLimit
