import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_orientedOpenRayStandardBorel
import Mathlib.Order.Interval.Set.OrdConnectedComponent
import Mathlib.Topology.Connected.Clopen

open Set Topology

noncomputable section

open ConcaveOTLimit

namespace BorelMaximalRay

/-! ## Elementary no-crossing and sigma-compactness tools -/

private theorem normalize_sub_left_eq_rayDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y z : E} (hz : z ∈ openSegment Real x y) :
    NormedSpace.normalize (z - x) = rayDirection x y := by
  rw [openSegment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hsub : x + t • (y - x) - x = t • (y - x) := by
    module
  rw [hsub, NormedSpace.normalize_smul_of_pos ht.1]
  rfl

private theorem normalize_sub_right_eq_rayDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y z : E} (hz : z ∈ openSegment Real x y) :
    NormedSpace.normalize (y - z) = rayDirection x y := by
  rw [openSegment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hsub : y - (x + t • (y - x)) = (1 - t) • (y - x) := by
    module
  rw [hsub, NormedSpace.normalize_smul_of_pos (sub_pos.mpr ht.2)]
  rfl

private theorem rayDirection_eq_of_common_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y y' z : E}
    (hz : z ∈ openSegment Real x y)
    (hz' : z ∈ openSegment Real x y') :
    rayDirection x y = rayDirection x y' :=
  (normalize_sub_left_eq_rayDirection hz).symm.trans
    (normalize_sub_left_eq_rayDirection hz')

private theorem rayDirection_eq_of_common_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x x' y z : E}
    (hz : z ∈ openSegment Real x y)
    (hz' : z ∈ openSegment Real x' y) :
    rayDirection x y = rayDirection x' y :=
  (normalize_sub_right_eq_rayDirection hz).symm.trans
    (normalize_sub_right_eq_rayDirection hz')

private theorem direction_eq_of_mem_openSegments
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} (hGamma : NoCrossing Gamma)
    {x y x' y' z : E}
    (hxy : (x, y) ∈ Gamma) (hxy' : (x', y') ∈ Gamma)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hz : z ∈ openSegment Real x y)
    (hz' : z ∈ openSegment Real x' y') :
    rayDirection x y = rayDirection x' y' := by
  by_contra hdir
  have hinter : (segment Real x y ∩ segment Real x' y').Nonempty :=
    ⟨z, openSegment_subset_segment _ _ _ hz,
      openSegment_subset_segment _ _ _ hz'⟩
  rcases hGamma x y x' y' hxy hxy' hne hne' hdir hinter with hleft | hright
  · subst x'
    exact hdir (rayDirection_eq_of_common_left hz hz')
  · subst y'
    exact hdir (rayDirection_eq_of_common_right hz hz')

private theorem isSigmaCompact_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y}
    (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) :
    IsSigmaCompact (s ×ˢ t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  obtain ⟨L, hL, hLt⟩ := ht
  have hcover : s ×ˢ t = ⋃ i, ⋃ j, K i ×ˢ L j := by
    rw [← hKs, ← hLt]
    ext p
    simp only [mem_prod, mem_iUnion]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨i, j, hi, hj⟩
    · rintro ⟨i, j, hi, hj⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [hcover]
  exact isSigmaCompact_iUnion _ fun i =>
    isSigmaCompact_iUnion _ fun j =>
      ((hK i).prod (hL j)).isSigmaCompact

private theorem isSigmaCompact_inter_isClosed
    {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsSigmaCompact s) (ht : IsClosed t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine ⟨fun i => K i ∩ t, fun i => (hK i).inter_right ht, ?_⟩
  rw [← iUnion_inter, hKs]

private theorem isSigmaCompact_inter_isOpen
    {X : Type*} [PseudoEMetricSpace X] {s t : Set X}
    (hs : IsSigmaCompact s) (ht : IsOpen t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  obtain ⟨F, hFclosed, _hFsub, hFt, _hFmono⟩ :=
    ht.exists_iUnion_isClosed
  have hcover : s ∩ t = ⋃ i, ⋃ j, K i ∩ F j := by
    rw [← hKs, ← hFt]
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨i, j, hi, hj⟩
    · rintro ⟨i, j, hi, hj⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [hcover]
  exact isSigmaCompact_iUnion _ fun i =>
    isSigmaCompact_iUnion _ fun j =>
      ((hK i).inter_right (hFclosed j)).isSigmaCompact

private theorem isSigmaCompact_Ioo_real (a b : Real) :
    IsSigmaCompact (Ioo a b) := by
  obtain ⟨F, hFclosed, hFsub, hFunion, _hFmono⟩ :=
    (isOpen_Ioo : IsOpen (Ioo a b)).exists_iUnion_isClosed
  refine ⟨F, ?_, hFunion⟩
  intro i
  exact IsCompact.of_isClosed_subset isCompact_Icc (hFclosed i)
    ((hFsub i).trans Ioo_subset_Icc_self)

private theorem measurableSet_of_isSigmaCompact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, hKs⟩ := hs
  rw [← hKs]
  exact MeasurableSet.iUnion fun i => (hK i).measurableSet

/-! ## Canonical affine-line incidence -/

private def offDiagonal {E : Type*} : Set (E × E) :=
  {p | p.1 ≠ p.2}

private theorem isOpen_offDiagonal
    {E : Type*} [TopologicalSpace E] [T2Space E] :
    IsOpen (offDiagonal : Set (E × E)) :=
  isOpen_ne_fun continuous_fst continuous_snd

private def segmentEvaluation
    {E : Type*} [AddCommGroup E] [Module Real E]
    (q : (E × E) × Real) : E :=
  AffineMap.lineMap q.1.1 q.1.2 q.2

private theorem continuous_segmentEvaluation
    {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module Real E] [IsTopologicalAddGroup E] [ContinuousSMul Real E] :
    Continuous (segmentEvaluation : ((E × E) × Real) -> E) := by
  unfold segmentEvaluation
  fun_prop

private theorem transportSet_eq_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (Gamma : Set (E × E)) :
    transportSet Gamma =
      segmentEvaluation ''
        ((Gamma ∩ offDiagonal) ×ˢ Ioo (0 : Real) 1) := by
  ext z
  constructor
  · rintro ⟨p, hpGamma, hpne, hzp⟩
    rw [openSegment_eq_image_lineMap] at hzp
    obtain ⟨t, ht, rfl⟩ := hzp
    exact ⟨(p, t), ⟨⟨hpGamma, hpne⟩, ht⟩, rfl⟩
  · rintro ⟨q, ⟨⟨hqGamma, hqne⟩, hqt⟩, rfl⟩
    exact ⟨q.1, hqGamma, hqne,
      lineMap_mem_openSegment Real q.1.1 q.1.2 hqt⟩

private theorem transportSet_isSigmaCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} (hGamma : IsSigmaCompact Gamma) :
    IsSigmaCompact (transportSet Gamma) := by
  rw [transportSet_eq_image]
  apply IsSigmaCompact.image continuous_segmentEvaluation
  exact isSigmaCompact_prod
    (isSigmaCompact_inter_isOpen hGamma isOpen_offDiagonal)
    (isSigmaCompact_Ioo_real 0 1)

private theorem transportSet_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E]
    {Gamma : Set (E × E)} (hGamma : IsSigmaCompact Gamma) :
    MeasurableSet (transportSet Gamma) :=
  measurableSet_of_isSigmaCompact (transportSet_isSigmaCompact hGamma)

private def lineAnchor {n : Nat} (d z : Euclidean n) : Euclidean n :=
  z - (inner Real z d) • d

private def lineCoordinate {n : Nat} (d z : Euclidean n) : Real :=
  inner Real z d

private theorem lineAnchor_add_lineCoordinate {n : Nat}
    (d z : Euclidean n) :
    lineAnchor d z + lineCoordinate d z • d = z := by
  unfold lineAnchor lineCoordinate
  module

private theorem inner_lineAnchor_eq_zero {n : Nat}
    {d z : Euclidean n} (hd : ‖d‖ = 1) :
    inner Real (lineAnchor d z) d = 0 := by
  unfold lineAnchor
  rw [inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hd]
  norm_num

private abbrev TransportLinePoint (n : Nat) :=
  (Euclidean n × Euclidean n) × Real

private def primitiveDirection {n : Nat}
    (p : Euclidean n × Euclidean n) : Euclidean n :=
  rayDirection p.1 p.2

private def primitiveLine {n : Nat}
    (p : Euclidean n × Euclidean n) : Euclidean n × Euclidean n :=
  let d := primitiveDirection p
  (d, lineAnchor d p.1)

private def primitiveLower {n : Nat}
    (p : Euclidean n × Euclidean n) : Real :=
  lineCoordinate (primitiveDirection p) p.1

private def primitiveUpper {n : Nat}
    (p : Euclidean n × Euclidean n) : Real :=
  lineCoordinate (primitiveDirection p) p.2

private theorem lineCoordinate_add_smul {n : Nat}
    {d z : Euclidean n} (hd : ‖d‖ = 1) (r : Real) :
    lineCoordinate d (z + r • d) = lineCoordinate d z + r := by
  unfold lineCoordinate
  rw [inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hd]
  norm_num

private theorem lineAnchor_add_smul {n : Nat}
    {d z : Euclidean n} (hd : ‖d‖ = 1) (r : Real) :
    lineAnchor d (z + r • d) = lineAnchor d z := by
  unfold lineAnchor
  rw [show inner Real (z + r • d) d =
      inner Real z d + r by
    simpa only [lineCoordinate] using lineCoordinate_add_smul hd r]
  module

private theorem lineCoordinate_point {n : Nat}
    {d a : Euclidean n} {t : Real}
    (hd : ‖d‖ = 1) (ha : inner Real a d = 0) :
    lineCoordinate d (a + t • d) = t := by
  unfold lineCoordinate
  rw [inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, ha, hd]
  norm_num

private theorem lineAnchor_point {n : Nat}
    {d a : Euclidean n} {t : Real}
    (hd : ‖d‖ = 1) (ha : inner Real a d = 0) :
    lineAnchor d (a + t • d) = a := by
  unfold lineAnchor
  rw [show inner Real (a + t • d) d = t by
    simpa only [lineCoordinate] using lineCoordinate_point hd ha]
  module

private theorem primitiveDirection_norm {n : Nat}
    {p : Euclidean n × Euclidean n} (hp : p.1 ≠ p.2) :
    ‖primitiveDirection p‖ = 1 := by
  unfold primitiveDirection rayDirection
  exact NormedSpace.norm_normalize (sub_ne_zero.mpr hp.symm)

private theorem primitive_second_eq {n : Nat}
    {p : Euclidean n × Euclidean n} :
    p.2 = p.1 + ‖p.2 - p.1‖ • primitiveDirection p := by
  calc
    p.2 = p.1 + (p.2 - p.1) := by abel
    _ = p.1 + ‖p.2 - p.1‖ • primitiveDirection p := by
      rw [primitiveDirection, rayDirection,
        NormedSpace.norm_smul_normalize]

private theorem primitiveAnchor_second {n : Nat}
    {p : Euclidean n × Euclidean n} (hp : p.1 ≠ p.2) :
    lineAnchor (primitiveDirection p) p.2 =
      lineAnchor (primitiveDirection p) p.1 := by
  rw [primitive_second_eq,
    lineAnchor_add_smul (primitiveDirection_norm hp)]

private theorem primitiveUpper_eq_lower_add_norm {n : Nat}
    {p : Euclidean n × Euclidean n} (hp : p.1 ≠ p.2) :
    primitiveUpper p =
      primitiveLower p + ‖p.2 - p.1‖ := by
  unfold primitiveUpper primitiveLower
  calc
    lineCoordinate (primitiveDirection p) p.2 =
        lineCoordinate (primitiveDirection p)
          (p.1 + ‖p.2 - p.1‖ • primitiveDirection p) := by
            exact congrArg (lineCoordinate (primitiveDirection p))
              primitive_second_eq
    _ = lineCoordinate (primitiveDirection p) p.1 +
          ‖p.2 - p.1‖ :=
      lineCoordinate_add_smul (primitiveDirection_norm hp) _

private theorem primitiveLower_lt_upper {n : Nat}
    {p : Euclidean n × Euclidean n} (hp : p.1 ≠ p.2) :
    primitiveLower p < primitiveUpper p := by
  rw [primitiveUpper_eq_lower_add_norm hp]
  exact lt_add_of_pos_right _ (norm_pos_iff.mpr (sub_ne_zero.mpr hp.symm))

private theorem primitive_first_point {n : Nat}
    (p : Euclidean n × Euclidean n) :
    (primitiveLine p).2 + primitiveLower p • (primitiveLine p).1 =
      p.1 :=
  lineAnchor_add_lineCoordinate (primitiveDirection p) p.1

private theorem primitive_second_point {n : Nat}
    {p : Euclidean n × Euclidean n} (hp : p.1 ≠ p.2) :
    (primitiveLine p).2 + primitiveUpper p • (primitiveLine p).1 =
      p.2 := by
  change
    lineAnchor (primitiveDirection p) p.1 +
        lineCoordinate (primitiveDirection p) p.2 •
          primitiveDirection p = p.2
  rw [← primitiveAnchor_second hp]
  exact lineAnchor_add_lineCoordinate (primitiveDirection p) p.2

private def primitiveIncidenceEvaluation {n : Nat}
    (q : (Euclidean n × Euclidean n) × Real) :
    TransportLinePoint n :=
  (primitiveLine q.1,
    AffineMap.lineMap (primitiveLower q.1) (primitiveUpper q.1) q.2)

private theorem continuousOn_primitiveIncidenceEvaluation {n : Nat} :
    ContinuousOn (primitiveIncidenceEvaluation :
      ((Euclidean n × Euclidean n) × Real) → TransportLinePoint n)
      (offDiagonal ×ˢ (univ : Set Real)) := by
  intro q hq
  have hnorm : ‖q.1.2 - q.1.1‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq.1.symm)
  unfold primitiveIncidenceEvaluation primitiveLine primitiveLower
    primitiveUpper primitiveDirection rayDirection lineAnchor
    lineCoordinate NormedSpace.normalize
  apply ContinuousAt.continuousWithinAt
  fun_prop

private def orientedLineIncidenceSet {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Set (TransportLinePoint n) :=
  {c | ∃ p : Euclidean n × Euclidean n,
    p ∈ Gamma ∧ p.1 ≠ p.2 ∧
      c.1 = primitiveLine p ∧
      c.2 ∈ Ioo (primitiveLower p) (primitiveUpper p)}

private theorem orientedLineIncidence_eq_image {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    orientedLineIncidenceSet Gamma =
      primitiveIncidenceEvaluation ''
        ((Gamma ∩ offDiagonal) ×ˢ Ioo (0 : Real) 1) := by
  ext c
  constructor
  · rintro ⟨p, hpGamma, hpne, hline, ht⟩
    have hlu := primitiveLower_lt_upper hpne
    rw [← openSegment_eq_Ioo hlu,
      openSegment_eq_image_lineMap] at ht
    obtain ⟨s, hs, hst⟩ := ht
    refine ⟨(p, s), ⟨⟨hpGamma, hpne⟩, hs⟩, ?_⟩
    exact Prod.ext hline.symm hst
  · rintro ⟨⟨p, s⟩, ⟨⟨hpGamma, hpne⟩, hs⟩, rfl⟩
    refine ⟨p, hpGamma, hpne, rfl, ?_⟩
    rw [← openSegment_eq_Ioo (primitiveLower_lt_upper hpne)]
    exact lineMap_mem_openSegment Real _ _ hs

private theorem orientedLineIncidence_isSigmaCompact {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : IsSigmaCompact Gamma) :
    IsSigmaCompact (orientedLineIncidenceSet Gamma) := by
  rw [orientedLineIncidence_eq_image]
  apply IsSigmaCompact.image_of_continuousOn
    (isSigmaCompact_prod
      (isSigmaCompact_inter_isOpen hGamma isOpen_offDiagonal)
      (isSigmaCompact_Ioo_real 0 1))
  exact ContinuousOn.mono continuousOn_primitiveIncidenceEvaluation
    (fun _ hq => ⟨hq.1.2, mem_univ _⟩)

private theorem orientedLineIncidence_measurable {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : IsSigmaCompact Gamma) :
    MeasurableSet (orientedLineIncidenceSet Gamma) :=
  measurableSet_of_isSigmaCompact
    (orientedLineIncidence_isSigmaCompact hGamma)

private def orientedLineSection {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (line : Euclidean n × Euclidean n) : Set Real :=
  {t | (line, t) ∈ orientedLineIncidenceSet Gamma}

private theorem isOpen_orientedLineSection {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (line : Euclidean n × Euclidean n) :
    IsOpen (orientedLineSection Gamma line) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨p, hpGamma, hpne, hline, ht⟩ := ht
  apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
  intro s hs
  exact ⟨p, hpGamma, hpne, hline, hs⟩

private def linePointEvaluation {n : Nat}
    (c : TransportLinePoint n) : Euclidean n :=
  c.1.2 + c.2 • c.1.1

private theorem continuous_linePointEvaluation {n : Nat} :
    Continuous (linePointEvaluation :
      TransportLinePoint n → Euclidean n) := by
  unfold linePointEvaluation
  fun_prop

private theorem linePointEvaluation_primitiveIncidenceEvaluation {n : Nat}
    {q : (Euclidean n × Euclidean n) × Real}
    (hq : q.1.1 ≠ q.1.2) :
    linePointEvaluation (primitiveIncidenceEvaluation q) =
      segmentEvaluation q := by
  have hx := primitive_first_point q.1
  have hy := primitive_second_point hq
  unfold linePointEvaluation primitiveIncidenceEvaluation segmentEvaluation
  dsimp only
  rw [AffineMap.lineMap_apply_module,
    AffineMap.lineMap_apply_module]
  calc
    (primitiveLine q.1).2 +
          ((1 - q.2) • primitiveLower q.1 +
            q.2 • primitiveUpper q.1) • (primitiveLine q.1).1 =
        (1 - q.2) •
            ((primitiveLine q.1).2 +
              primitiveLower q.1 • (primitiveLine q.1).1) +
          q.2 •
            ((primitiveLine q.1).2 +
              primitiveUpper q.1 • (primitiveLine q.1).1) := by module
    _ = (1 - q.2) • q.1.1 + q.2 • q.1.2 := by rw [hx, hy]

private theorem linePointEvaluation_image {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    linePointEvaluation '' orientedLineIncidenceSet Gamma =
      transportSet Gamma := by
  rw [orientedLineIncidence_eq_image, transportSet_eq_image]
  ext z
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq,
      (linePointEvaluation_primitiveIncidenceEvaluation hq.1.2).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨primitiveIncidenceEvaluation q, ⟨q, hq, rfl⟩,
      linePointEvaluation_primitiveIncidenceEvaluation hq.1.2⟩

private theorem orientedLineIncidence_direction_norm {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c : TransportLinePoint n}
    (hc : c ∈ orientedLineIncidenceSet Gamma) :
    ‖c.1.1‖ = 1 := by
  obtain ⟨p, _, hpne, hline, _⟩ := hc
  rw [hline]
  exact primitiveDirection_norm hpne

private theorem orientedLineIncidence_anchor_orthogonal {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c : TransportLinePoint n}
    (hc : c ∈ orientedLineIncidenceSet Gamma) :
    inner Real c.1.2 c.1.1 = 0 := by
  obtain ⟨p, _, hpne, hline, _⟩ := hc
  rw [hline]
  exact inner_lineAnchor_eq_zero (primitiveDirection_norm hpne)

private theorem lineAnchor_linePointEvaluation {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c : TransportLinePoint n}
    (hc : c ∈ orientedLineIncidenceSet Gamma) :
    lineAnchor c.1.1 (linePointEvaluation c) = c.1.2 :=
  lineAnchor_point
    (orientedLineIncidence_direction_norm hc)
    (orientedLineIncidence_anchor_orthogonal hc)

private theorem lineCoordinate_linePointEvaluation {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c : TransportLinePoint n}
    (hc : c ∈ orientedLineIncidenceSet Gamma) :
    lineCoordinate c.1.1 (linePointEvaluation c) = c.2 :=
  lineCoordinate_point
    (orientedLineIncidence_direction_norm hc)
    (orientedLineIncidence_anchor_orthogonal hc)

private theorem linePointEvaluation_mem_openSegment {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c : TransportLinePoint n}
    (hc : c ∈ orientedLineIncidenceSet Gamma) :
    ∃ p : Euclidean n × Euclidean n,
      p ∈ Gamma ∧ p.1 ≠ p.2 ∧
        linePointEvaluation c ∈ openSegment Real p.1 p.2 ∧
        c.1.1 = primitiveDirection p := by
  rw [orientedLineIncidence_eq_image] at hc
  obtain ⟨⟨p, s⟩, ⟨⟨hpGamma, hpne⟩, hs⟩, rfl⟩ := hc
  refine ⟨p, hpGamma, hpne, ?_, rfl⟩
  rw [linePointEvaluation_primitiveIncidenceEvaluation hpne]
  exact lineMap_mem_openSegment Real _ _ hs

private theorem linePointEvaluation_injOn {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma) :
    InjOn linePointEvaluation (orientedLineIncidenceSet Gamma) := by
  intro c hc c' hc' heval
  obtain ⟨p, hpGamma, hpne, hpseg, hpdir⟩ :=
    linePointEvaluation_mem_openSegment hc
  obtain ⟨p', hpGamma', hpne', hpseg', hpdir'⟩ :=
    linePointEvaluation_mem_openSegment hc'
  have hdir : c.1.1 = c'.1.1 := by
    rw [hpdir, hpdir']
    exact direction_eq_of_mem_openSegments hNoCrossing
      hpGamma hpGamma' hpne hpne' hpseg (heval ▸ hpseg')
  apply Prod.ext
  · apply Prod.ext
    · exact hdir
    · rw [← lineAnchor_linePointEvaluation hc,
        ← lineAnchor_linePointEvaluation hc', heval, hdir]
  · rw [← lineCoordinate_linePointEvaluation hc,
      ← lineCoordinate_linePointEvaluation hc', heval, hdir]

private abbrev OrientedLineIncidence {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :=
  {c : TransportLinePoint n // c ∈ orientedLineIncidenceSet Gamma}

private def lineIncidenceToTransport {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (c : OrientedLineIncidence Gamma) : transportSet Gamma :=
  ⟨linePointEvaluation c.1, by
    rw [← linePointEvaluation_image Gamma]
    exact mem_image_of_mem linePointEvaluation c.property⟩

private theorem measurable_lineIncidenceToTransport {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Measurable (lineIncidenceToTransport Gamma) := by
  apply Measurable.subtype_mk
  exact continuous_linePointEvaluation.measurable.comp measurable_subtype_coe

private theorem injective_lineIncidenceToTransport {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma) :
    Function.Injective (lineIncidenceToTransport Gamma) := by
  intro c d h
  apply Subtype.ext
  apply linePointEvaluation_injOn hNoCrossing c.property d.property
  exact congrArg Subtype.val h

private theorem surjective_lineIncidenceToTransport {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Function.Surjective (lineIncidenceToTransport Gamma) := by
  intro z
  obtain ⟨c, hc, hcz⟩ := (linePointEvaluation_image Gamma).symm.subset z.property
  exact ⟨⟨c, hc⟩, Subtype.ext hcz⟩

/-! ## Borel connected components from finite primitive chains -/

private def primitivePairEvaluation {n : Nat}
    (q : ((Euclidean n × Euclidean n) × Real) × Real) :
    TransportLinePoint n × TransportLinePoint n :=
  (primitiveIncidenceEvaluation q.1,
    primitiveIncidenceEvaluation (q.1.1, q.2))

private theorem continuousOn_primitivePairEvaluation {n : Nat} :
    ContinuousOn (primitivePairEvaluation :
      (((Euclidean n × Euclidean n) × Real) × Real) →
        TransportLinePoint n × TransportLinePoint n)
      (((offDiagonal : Set (Euclidean n × Euclidean n)) ×ˢ
          (univ : Set Real)) ×ˢ (univ : Set Real)) := by
  intro q hq
  have hnorm : ‖q.1.1.2 - q.1.1.1‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq.1.1.symm)
  unfold primitivePairEvaluation primitiveIncidenceEvaluation primitiveLine
    primitiveLower primitiveUpper primitiveDirection rayDirection lineAnchor
    lineCoordinate NormedSpace.normalize
  apply ContinuousAt.continuousWithinAt
  fun_prop

private def samePrimitiveSet {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Set (TransportLinePoint n × TransportLinePoint n) :=
  {q | ∃ p : Euclidean n × Euclidean n,
    p ∈ Gamma ∧ p.1 ≠ p.2 ∧
      q.1.1 = primitiveLine p ∧ q.2.1 = primitiveLine p ∧
      q.1.2 ∈ Ioo (primitiveLower p) (primitiveUpper p) ∧
      q.2.2 ∈ Ioo (primitiveLower p) (primitiveUpper p)}

private theorem samePrimitiveSet_eq_image {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    samePrimitiveSet Gamma =
      primitivePairEvaluation ''
        (((Gamma ∩ offDiagonal) ×ˢ Ioo (0 : Real) 1) ×ˢ
          Ioo (0 : Real) 1) := by
  ext q
  constructor
  · rintro ⟨p, hpGamma, hpne, hline, hline', ht, ht'⟩
    have hlu := primitiveLower_lt_upper hpne
    rw [← openSegment_eq_Ioo hlu,
      openSegment_eq_image_lineMap] at ht ht'
    obtain ⟨s, hs, hst⟩ := ht
    obtain ⟨s', hs', hst'⟩ := ht'
    refine ⟨((p, s), s'), ⟨⟨⟨hpGamma, hpne⟩, hs⟩, hs'⟩, ?_⟩
    apply Prod.ext
    · exact Prod.ext hline.symm hst
    · exact Prod.ext hline'.symm hst'
  · rintro ⟨⟨⟨p, s⟩, s'⟩,
      ⟨⟨⟨hpGamma, hpne⟩, hs⟩, hs'⟩, rfl⟩
    refine ⟨p, hpGamma, hpne, rfl, rfl, ?_, ?_⟩
    · rw [← openSegment_eq_Ioo (primitiveLower_lt_upper hpne)]
      exact lineMap_mem_openSegment Real _ _ hs
    · rw [← openSegment_eq_Ioo (primitiveLower_lt_upper hpne)]
      exact lineMap_mem_openSegment Real _ _ hs'

private theorem samePrimitiveSet_isSigmaCompact {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : IsSigmaCompact Gamma) :
    IsSigmaCompact (samePrimitiveSet Gamma) := by
  rw [samePrimitiveSet_eq_image]
  apply IsSigmaCompact.image_of_continuousOn
  · exact isSigmaCompact_prod
      (isSigmaCompact_prod
        (isSigmaCompact_inter_isOpen hGamma isOpen_offDiagonal)
        (isSigmaCompact_Ioo_real 0 1))
      (isSigmaCompact_Ioo_real 0 1)
  · exact ContinuousOn.mono continuousOn_primitivePairEvaluation
      (fun _ hq => ⟨⟨hq.1.1.2, mem_univ _⟩, mem_univ _⟩)

private theorem samePrimitiveSet_spec {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {q : TransportLinePoint n × TransportLinePoint n}
    (hq : q ∈ samePrimitiveSet Gamma) :
    q.1 ∈ orientedLineIncidenceSet Gamma ∧
      q.2 ∈ orientedLineIncidenceSet Gamma ∧
      q.1.1 = q.2.1 := by
  obtain ⟨p, hpGamma, hpne, hline, hline', ht, ht'⟩ := hq
  exact
    ⟨⟨p, hpGamma, hpne, hline, ht⟩,
      ⟨p, hpGamma, hpne, hline', ht'⟩,
      hline.trans hline'.symm⟩

private theorem samePrimitiveSet_symm {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c d : TransportLinePoint n}
    (h : (c, d) ∈ samePrimitiveSet Gamma) :
    (d, c) ∈ samePrimitiveSet Gamma := by
  obtain ⟨p, hpGamma, hpne, hline, hline', ht, ht'⟩ := h
  exact ⟨p, hpGamma, hpne, hline', hline, ht', ht⟩

private theorem samePrimitiveSet_mem_component {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c d : TransportLinePoint n}
    (h : (c, d) ∈ samePrimitiveSet Gamma) :
    d.2 ∈
      ordConnectedComponent (orientedLineSection Gamma c.1) c.2 := by
  obtain ⟨p, hpGamma, hpne, hline, hline', ht, ht'⟩ := h
  rw [mem_ordConnectedComponent]
  intro r hr
  exact
    ⟨p, hpGamma, hpne, hline,
      ordConnected_Ioo.uIcc_subset ht ht' hr⟩

private def relationComp {X : Type*}
    (r s : Set (X × X)) : Set (X × X) :=
  {q | ∃ b, (q.1, b) ∈ r ∧ (b, q.2) ∈ s}

private def relationCompEvaluation {X : Type*}
    (q : (X × X) × (X × X)) : X × X :=
  (q.1.1, q.2.2)

private theorem continuous_relationCompEvaluation
    {X : Type*} [TopologicalSpace X] :
    Continuous (relationCompEvaluation :
      ((X × X) × (X × X)) → X × X) := by
  unfold relationCompEvaluation
  fun_prop

private theorem relationComp_eq_image
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (r s : Set (X × X)) :
    relationComp r s =
      relationCompEvaluation ''
        ((r ×ˢ s) ∩ {q : (X × X) × (X × X) | q.1.2 = q.2.1}) := by
  ext q
  constructor
  · rintro ⟨b, hab, hbc⟩
    exact
      ⟨((q.1, b), (b, q.2)), ⟨⟨hab, hbc⟩, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨⟨hw, hw'⟩, hmiddle⟩, rfl⟩
    refine ⟨w.1.2, hw, ?_⟩
    change (w.1.2, w.2.2) ∈ s
    rw [hmiddle]
    exact hw'

private theorem relationComp_isSigmaCompact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {r s : Set (X × X)}
    (hr : IsSigmaCompact r) (hs : IsSigmaCompact s) :
    IsSigmaCompact (relationComp r s) := by
  rw [relationComp_eq_image]
  apply IsSigmaCompact.image continuous_relationCompEvaluation
  apply isSigmaCompact_inter_isClosed (isSigmaCompact_prod hr hs)
  exact isClosed_eq
    (continuous_snd.comp continuous_fst)
    (continuous_fst.comp continuous_snd)

private def lineChain {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Nat → Set (TransportLinePoint n × TransportLinePoint n)
  | 0 => {q | q.1 = q.2 ∧ q.1 ∈ orientedLineIncidenceSet Gamma}
  | k + 1 => relationComp (lineChain Gamma k) (samePrimitiveSet Gamma)

private theorem lineChain_isSigmaCompact {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : IsSigmaCompact Gamma) :
    ∀ k, IsSigmaCompact (lineChain Gamma k) := by
  intro k
  induction k with
  | zero =>
      have heq :
          lineChain Gamma 0 =
            (fun c : TransportLinePoint n => (c, c)) ''
              orientedLineIncidenceSet Gamma := by
        ext q
        simp only [lineChain, mem_setOf_eq, mem_image]
        constructor
        · rintro ⟨heq, hq⟩
          exact ⟨q.1, hq, Prod.ext rfl heq⟩
        · rintro ⟨c, hc, rfl⟩
          exact ⟨rfl, hc⟩
      rw [heq]
      exact (orientedLineIncidence_isSigmaCompact hGamma).image (by fun_prop)
  | succ k ih =>
      exact relationComp_isSigmaCompact ih
        (samePrimitiveSet_isSigmaCompact hGamma)

private def reachableSet {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Set (TransportLinePoint n × TransportLinePoint n) :=
  ⋃ k, lineChain Gamma k

private theorem reachableSet_isSigmaCompact {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : IsSigmaCompact Gamma) :
    IsSigmaCompact (reachableSet Gamma) := by
  exact isSigmaCompact_iUnion _ (lineChain_isSigmaCompact hGamma)

private theorem lineChain_spec {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {q : TransportLinePoint n × TransportLinePoint n} {k : Nat}
    (hq : q ∈ lineChain Gamma k) :
    q.1 ∈ orientedLineIncidenceSet Gamma ∧
      q.2 ∈ orientedLineIncidenceSet Gamma ∧
      q.1.1 = q.2.1 := by
  induction k generalizing q with
  | zero =>
      exact ⟨hq.2, hq.1 ▸ hq.2, congrArg Prod.fst hq.1⟩
  | succ k ih =>
      obtain ⟨b, hqb, hbq⟩ := hq
      have hleft := ih hqb
      have hright := samePrimitiveSet_spec hbq
      exact
        ⟨hleft.1, hright.2.1,
          hleft.2.2.trans hright.2.2⟩

private theorem lineChain_mem_component {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {c d : TransportLinePoint n} {k : Nat}
    (h : (c, d) ∈ lineChain Gamma k) :
    d.2 ∈
      ordConnectedComponent (orientedLineSection Gamma c.1) c.2 := by
  induction k generalizing d with
  | zero =>
      change c = d ∧ c ∈ orientedLineIncidenceSet Gamma at h
      rcases h with ⟨rfl, hc⟩
      exact self_mem_ordConnectedComponent.mpr hc
  | succ k ih =>
      obtain ⟨b, hcb, hbd⟩ := h
      have hb := ih hcb
      have hd := samePrimitiveSet_mem_component hbd
      have hline : c.1 = b.1 := (lineChain_spec hcb).2.2
      have hd' :
          d.2 ∈
            ordConnectedComponent
              (orientedLineSection Gamma c.1) b.2 := by
        simpa only [hline] using hd
      exact mem_ordConnectedComponent_trans hb hd'

private def reachableParameters {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (c : TransportLinePoint n) : Set Real :=
  {r | ∃ k, (c, (c.1, r)) ∈ lineChain Gamma k}

private theorem isOpen_reachableParameters {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (c : TransportLinePoint n) :
    IsOpen (reachableParameters Gamma c) := by
  rw [isOpen_iff_mem_nhds]
  intro r hr
  obtain ⟨k, hk⟩ := hr
  have hrA := (lineChain_spec hk).2.1
  obtain ⟨p, hpGamma, hpne, hline, hrp⟩ := hrA
  apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hrp)
  intro s hs
  refine ⟨k + 1, ?_⟩
  exact
    ⟨(c.1, r), hk,
      ⟨p, hpGamma, hpne, hline, hline, hrp, hs⟩⟩

private theorem isOpen_section_diff_reachableParameters {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (c : TransportLinePoint n) :
    IsOpen
      (orientedLineSection Gamma c.1 \ reachableParameters Gamma c) := by
  rw [isOpen_iff_mem_nhds]
  intro r hr
  obtain ⟨p, hpGamma, hpne, hline, hrp⟩ := hr.1
  apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hrp)
  intro s hs
  refine ⟨⟨p, hpGamma, hpne, hline, hs⟩, ?_⟩
  rintro ⟨k, hk⟩
  apply hr.2
  refine ⟨k + 1, ?_⟩
  exact
    ⟨(c.1, s), hk,
      ⟨p, hpGamma, hpne, hline, hline, hs, hrp⟩⟩

private theorem reachableParameters_iff_component {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (c : TransportLinePoint n)
    (hc : c ∈ orientedLineIncidenceSet Gamma)
    (r : Real) :
    r ∈ reachableParameters Gamma c ↔
      r ∈
        ordConnectedComponent
          (orientedLineSection Gamma c.1) c.2 := by
  constructor
  · rintro ⟨k, hk⟩
    exact lineChain_mem_component hk
  · intro hr
    let C :=
      ordConnectedComponent (orientedLineSection Gamma c.1) c.2
    let U := reachableParameters Gamma c
    let V := orientedLineSection Gamma c.1 \ U
    have hCpre : IsPreconnected C :=
      (show C.OrdConnected from inferInstance).isPreconnected
    have hUopen : IsOpen U := isOpen_reachableParameters Gamma c
    have hVopen : IsOpen V :=
      isOpen_section_diff_reachableParameters Gamma c
    have hdisjoint : Disjoint U V := by
      rw [Set.disjoint_left]
      intro x hxU hxV
      exact hxV.2 hxU
    have hcover : C ⊆ U ∪ V := by
      intro x hx
      have hxA :
          x ∈ orientedLineSection Gamma c.1 :=
        ordConnectedComponent_subset hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr ⟨hxA, hxU⟩
    have hbaseU : c.2 ∈ U := by
      exact ⟨0, rfl, hc⟩
    have hmeet : (C ∩ U).Nonempty :=
      ⟨c.2, self_mem_ordConnectedComponent.mpr hc, hbaseU⟩
    exact
      (hCpre.subset_left_of_subset_union
        hUopen hVopen hdisjoint hcover hmeet) hr

private def incidenceLine {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (xi : OrientedLineIncidence Gamma) : Euclidean n × Euclidean n :=
  xi.1.1

private def incidenceCoordinate {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (xi : OrientedLineIncidence Gamma) : Real :=
  xi.1.2

private def incidenceComponentRelation {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    Set (OrientedLineIncidence Gamma × Real) :=
  {p | p.2 ∈
    ordConnectedComponent
      (orientedLineSection Gamma (incidenceLine p.1))
      (incidenceCoordinate p.1)}

private def incidenceReachabilityMap {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (p : OrientedLineIncidence Gamma × Real) :
    TransportLinePoint n × TransportLinePoint n :=
  (p.1.1, (p.1.1.1, p.2))

private theorem measurable_incidenceReachabilityMap {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)} :
    Measurable (incidenceReachabilityMap (Gamma := Gamma)) := by
  have hxi :
      Measurable
        (fun p : OrientedLineIncidence Gamma × Real => p.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  exact hxi.prodMk ((measurable_fst.comp hxi).prodMk measurable_snd)

private theorem incidenceComponentRelation_eq_preimage_reachableSet {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n)) :
    incidenceComponentRelation Gamma =
      incidenceReachabilityMap ⁻¹' reachableSet Gamma := by
  ext p
  simp only [incidenceComponentRelation, incidenceReachabilityMap,
    reachableSet, incidenceLine, incidenceCoordinate, mem_setOf_eq,
    mem_preimage, mem_iUnion]
  exact (reachableParameters_iff_component Gamma p.1.1 p.1.property p.2).symm

private theorem measurable_incidenceComponentRelation {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : IsSigmaCompact Gamma) :
    MeasurableSet (incidenceComponentRelation Gamma) := by
  rw [incidenceComponentRelation_eq_preimage_reachableSet]
  exact
    (measurableSet_of_isSigmaCompact
      (reachableSet_isSigmaCompact hGamma)).preimage
      measurable_incidenceReachabilityMap

/-! ## Measurable extended-real endpoints -/

private def componentRelation {X : Type*}
    (fibers : X → Set Real) (base : X → Real) : Set (X × Real) :=
  {p | p.2 ∈ ordConnectedComponent (fibers p.1) (base p.1)}

private def componentLower {X : Type*}
    (fibers : X → Set Real) (base : X → Real) (x : X) : EReal := by
  classical
  exact ⨅ q : Rat,
    if (q : Real) ∈ ordConnectedComponent (fibers x) (base x)
    then ((q : Real) : EReal)
    else ⊤

private def componentUpper {X : Type*}
    (fibers : X → Set Real) (base : X → Real) (x : X) : EReal := by
  classical
  exact ⨆ q : Rat,
    if (q : Real) ∈ ordConnectedComponent (fibers x) (base x)
    then ((q : Real) : EReal)
    else ⊥

private theorem measurable_componentLower {X : Type*} [MeasurableSpace X]
    (fibers : X → Set Real) (base : X → Real)
    (hconn : MeasurableSet (componentRelation fibers base)) :
    Measurable (componentLower fibers base) := by
  classical
  unfold componentLower
  apply Measurable.iInf
  intro q
  apply Measurable.ite
  · exact hconn.preimage (measurable_id.prodMk measurable_const)
  · exact measurable_const
  · exact measurable_const

private theorem measurable_componentUpper {X : Type*} [MeasurableSpace X]
    (fibers : X → Set Real) (base : X → Real)
    (hconn : MeasurableSet (componentRelation fibers base)) :
    Measurable (componentUpper fibers base) := by
  classical
  unfold componentUpper
  apply Measurable.iSup
  intro q
  apply Measurable.ite
  · exact hconn.preimage (measurable_id.prodMk measurable_const)
  · exact measurable_const
  · exact measurable_const

private theorem isOpen_ordConnectedComponent_of_isOpen
    {s : Set Real} (hs : IsOpen s) (t : Real) :
    IsOpen (ordConnectedComponent s t) := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  have hu_s : u ∈ s := ordConnectedComponent_subset hu
  rw [ordConnectedComponent_eq hu]
  exact ordConnectedComponent_mem_nhds.mpr (hs.mem_nhds hu_s)

private theorem componentLower_le_rat {X : Type*}
    (fibers : X → Set Real) (base : X → Real)
    {x : X} {q : Rat}
    (hq : (q : Real) ∈
      ordConnectedComponent (fibers x) (base x)) :
    componentLower fibers base x ≤ ((q : Real) : EReal) := by
  classical
  unfold componentLower
  exact iInf_le_of_le q (by simp [hq])

private theorem rat_le_componentUpper {X : Type*}
    (fibers : X → Set Real) (base : X → Real)
    {x : X} {q : Rat}
    (hq : (q : Real) ∈
      ordConnectedComponent (fibers x) (base x)) :
    ((q : Real) : EReal) ≤ componentUpper fibers base x := by
  classical
  unfold componentUpper
  exact le_iSup_of_le q (by simp [hq])

private theorem componentLower_lt_upper_of_isOpen_of_mem {X : Type*}
    (fibers : X → Set Real) (base : X → Real) (x : X)
    (hopen : IsOpen (fibers x)) (hbase : base x ∈ fibers x) :
    componentLower fibers base x < componentUpper fibers base x := by
  let C := ordConnectedComponent (fibers x) (base x)
  have hCopen : IsOpen C :=
    isOpen_ordConnectedComponent_of_isOpen hopen _
  have hCnonempty : C.Nonempty :=
    ⟨base x, self_mem_ordConnectedComponent.mpr hbase⟩
  obtain ⟨a, b, hab, hIoo⟩ := hCopen.exists_Ioo_subset hCnonempty
  obtain ⟨m, ham, hmb⟩ := exists_between hab
  obtain ⟨q₁, haq₁, hq₁m⟩ := exists_rat_btwn ham
  obtain ⟨q₂, hmq₂, hq₂b⟩ := exists_rat_btwn hmb
  have hq₁C : (q₁ : Real) ∈ C :=
    hIoo ⟨haq₁, hq₁m.trans hmb⟩
  have hq₂C : (q₂ : Real) ∈ C :=
    hIoo ⟨ham.trans hmq₂, hq₂b⟩
  calc
    componentLower fibers base x ≤ ((q₁ : Real) : EReal) :=
      componentLower_le_rat fibers base hq₁C
    _ < ((q₂ : Real) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (hq₁m.trans hmq₂)
    _ ≤ componentUpper fibers base x :=
      rat_le_componentUpper fibers base hq₂C

private theorem componentParameterSet_eq {X : Type*}
    (fibers : X → Set Real) (base : X → Real) (x : X)
    (hopen : IsOpen (fibers x)) (hbase : base x ∈ fibers x) :
    {r : Real |
        componentLower fibers base x < (r : EReal) ∧
          (r : EReal) < componentUpper fibers base x} =
      ordConnectedComponent (fibers x) (base x) := by
  let C := ordConnectedComponent (fibers x) (base x)
  have hCopen : IsOpen C :=
    isOpen_ordConnectedComponent_of_isOpen hopen _
  have hbaseC : base x ∈ C :=
    self_mem_ordConnectedComponent.mpr hbase
  ext r
  constructor
  · rintro ⟨hlower, hupper⟩
    by_contra hrC
    rcases lt_trichotomy r (base x) with hrbase | hre | hbaser
    · have hall : ∀ q : Rat, (q : Real) ∈ C → r < (q : Real) := by
        intro q hqC
        by_contra hnlt
        have hqr : (q : Real) ≤ r := le_of_not_gt hnlt
        have hr_mem : r ∈ C :=
          (show C.OrdConnected from inferInstance).uIcc_subset
            hqC hbaseC (mem_uIcc_of_le hqr hrbase.le)
        exact hrC hr_mem
      have hr_le_lower :
          (r : EReal) ≤ componentLower fibers base x := by
        classical
        unfold componentLower
        apply le_iInf
        intro q
        by_cases hqC : (q : Real) ∈
            ordConnectedComponent (fibers x) (base x)
        · rw [if_pos hqC]
          exact EReal.coe_le_coe_iff.mpr
            (hall q (show (q : Real) ∈ C from hqC)).le
        · rw [if_neg hqC]
          exact le_top
      exact (not_lt_of_ge hr_le_lower) hlower
    · subst r
      exact hrC hbaseC
    · have hall : ∀ q : Rat, (q : Real) ∈ C → (q : Real) < r := by
        intro q hqC
        by_contra hnlt
        have hrq : r ≤ (q : Real) := le_of_not_gt hnlt
        have hr_mem : r ∈ C :=
          (show C.OrdConnected from inferInstance).uIcc_subset
            hbaseC hqC (mem_uIcc_of_le hbaser.le hrq)
        exact hrC hr_mem
      have hupper_le_r :
          componentUpper fibers base x ≤ (r : EReal) := by
        classical
        unfold componentUpper
        apply iSup_le
        intro q
        by_cases hqC : (q : Real) ∈
            ordConnectedComponent (fibers x) (base x)
        · rw [if_pos hqC]
          exact EReal.coe_le_coe_iff.mpr
            (hall q (show (q : Real) ∈ C from hqC)).le
        · rw [if_neg hqC]
          exact bot_le
      exact (not_lt_of_ge hupper_le_r) hupper
  · intro hrC
    obtain ⟨l, u, hrlu, hIoo⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hCopen.mem_nhds hrC)
    obtain ⟨q₁, hlq₁, hq₁r⟩ := exists_rat_btwn hrlu.1
    obtain ⟨q₂, hrq₂, hq₂u⟩ := exists_rat_btwn hrlu.2
    have hq₁C : (q₁ : Real) ∈ C :=
      hIoo ⟨hlq₁, hq₁r.trans hrlu.2⟩
    have hq₂C : (q₂ : Real) ∈ C :=
      hIoo ⟨hrlu.1.trans hrq₂, hq₂u⟩
    exact
      ⟨(componentLower_le_rat fibers base hq₁C).trans_lt
          (EReal.coe_lt_coe_iff.mpr hq₁r),
        (EReal.coe_lt_coe_iff.mpr hrq₂).trans_le
          (rat_le_componentUpper fibers base hq₂C)⟩

/-! ## The canonical component ray -/

private def incidenceComponentLower {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) : EReal :=
  componentLower
    (fun eta => orientedLineSection Gamma (incidenceLine eta))
    incidenceCoordinate xi

private def incidenceComponentUpper {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) : EReal :=
  componentUpper
    (fun eta => orientedLineSection Gamma (incidenceLine eta))
    incidenceCoordinate xi

private theorem measurable_incidenceComponentLower {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (hconn : MeasurableSet (incidenceComponentRelation Gamma)) :
    Measurable (incidenceComponentLower Gamma) :=
  measurable_componentLower _ _ hconn

private theorem measurable_incidenceComponentUpper {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (hconn : MeasurableSet (incidenceComponentRelation Gamma)) :
    Measurable (incidenceComponentUpper Gamma) :=
  measurable_componentUpper _ _ hconn

private theorem incidenceCoordinate_mem_section {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) :
    incidenceCoordinate xi ∈
      orientedLineSection Gamma (incidenceLine xi) :=
  xi.property

private theorem incidenceComponentLower_lt_upper {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) :
    incidenceComponentLower Gamma xi <
      incidenceComponentUpper Gamma xi :=
  componentLower_lt_upper_of_isOpen_of_mem
    (fun eta => orientedLineSection Gamma (incidenceLine eta))
    incidenceCoordinate xi
    (isOpen_orientedLineSection Gamma _)
    (incidenceCoordinate_mem_section Gamma xi)

private def incidenceComponentRawRayCode {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) : RawRayCode n :=
  (((incidenceLine xi).2, (incidenceLine xi).1),
    (incidenceComponentLower Gamma xi,
      incidenceComponentUpper Gamma xi))

private theorem incidenceComponentRawRayCode_isRayCode {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) :
    IsRayCode (incidenceComponentRawRayCode Gamma xi) := by
  refine ⟨?_, ?_, incidenceComponentLower_lt_upper Gamma xi⟩
  · exact orientedLineIncidence_direction_norm xi.property
  · exact orientedLineIncidence_anchor_orthogonal xi.property

private def incidenceComponentRay {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) : OrientedOpenRay n :=
  ⟨incidenceComponentRawRayCode Gamma xi,
    incidenceComponentRawRayCode_isRayCode Gamma xi⟩

private theorem measurable_incidenceComponentRawRayCode {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (hconn : MeasurableSet (incidenceComponentRelation Gamma)) :
    Measurable (incidenceComponentRawRayCode Gamma) := by
  have hline : Measurable (incidenceLine :
      OrientedLineIncidence Gamma → Euclidean n × Euclidean n) :=
    measurable_fst.comp measurable_subtype_coe
  exact
    ((measurable_snd.comp hline).prodMk (measurable_fst.comp hline)).prodMk
      ((measurable_incidenceComponentLower Gamma hconn).prodMk
        (measurable_incidenceComponentUpper Gamma hconn))

private theorem measurable_incidenceComponentRay {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (hconn : MeasurableSet (incidenceComponentRelation Gamma)) :
    Measurable (incidenceComponentRay Gamma) :=
  Measurable.subtype_mk
    (measurable_incidenceComponentRawRayCode Gamma hconn)

private theorem incidenceComponentRay_parameterSet {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) :
    {s : Real |
        (incidenceComponentRay Gamma xi).lower < (s : EReal) ∧
          (s : EReal) < (incidenceComponentRay Gamma xi).upper} =
      ordConnectedComponent
        (orientedLineSection Gamma (incidenceLine xi))
        (incidenceCoordinate xi) := by
  simpa [incidenceComponentRay, incidenceComponentRawRayCode,
    incidenceComponentLower, incidenceComponentUpper,
    OrientedOpenRay.lower, OrientedOpenRay.upper] using
    componentParameterSet_eq
      (fun eta : OrientedLineIncidence Gamma =>
        orientedLineSection Gamma (incidenceLine eta))
      incidenceCoordinate xi
      (isOpen_orientedLineSection Gamma _)
      (incidenceCoordinate_mem_section Gamma xi)

private theorem incidenceComponentRay_point {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) (s : Real) :
    (incidenceComponentRay Gamma xi).point s =
      linePointEvaluation (incidenceLine xi, s) :=
  rfl

private theorem linePointEvaluation_mem_primitiveOpenSegment {n : Nat}
    {line : Euclidean n × Euclidean n} {s : Real}
    {p : Euclidean n × Euclidean n}
    (hpne : p.1 ≠ p.2) (hline : line = primitiveLine p)
    (hs : s ∈ Ioo (primitiveLower p) (primitiveUpper p)) :
    linePointEvaluation (line, s) ∈ openSegment Real p.1 p.2 := by
  rw [← openSegment_eq_Ioo (primitiveLower_lt_upper hpne),
    openSegment_eq_image_lineMap] at hs
  obtain ⟨r, hr, hrs⟩ := hs
  have hcode :
      primitiveIncidenceEvaluation (p, r) = (line, s) :=
    Prod.ext hline.symm hrs
  rw [← hcode, linePointEvaluation_primitiveIncidenceEvaluation hpne]
  exact lineMap_mem_openSegment Real _ _ hr

private theorem incidenceComponentRay_coveredBy {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) :
    (incidenceComponentRay Gamma xi).CoveredBy Gamma := by
  intro z hz
  obtain ⟨s, hsl, hsu, hpoint⟩ := hz
  have hscomp : s ∈
      ordConnectedComponent
        (orientedLineSection Gamma (incidenceLine xi))
        (incidenceCoordinate xi) := by
    rw [← incidenceComponentRay_parameterSet Gamma xi]
    exact ⟨hsl, hsu⟩
  have hssection :
      s ∈ orientedLineSection Gamma (incidenceLine xi) :=
    ordConnectedComponent_subset hscomp
  obtain ⟨p, hpGamma, hpne, hline, hs⟩ := hssection
  refine ⟨p.1, p.2, hpGamma, hpne, ?_, ?_⟩
  · rw [← hpoint, incidenceComponentRay_point]
    exact linePointEvaluation_mem_primitiveOpenSegment hpne hline hs
  · change primitiveDirection p =
      (incidenceComponentRay Gamma xi).direction
    exact (congrArg Prod.fst hline).symm

private theorem incidencePoint_mem_componentRay_carrier {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (xi : OrientedLineIncidence Gamma) :
    linePointEvaluation xi.1 ∈
      (incidenceComponentRay Gamma xi).carrier := by
  let t := incidenceCoordinate xi
  have htcomponent :
      t ∈ ordConnectedComponent
        (orientedLineSection Gamma (incidenceLine xi)) t :=
    self_mem_ordConnectedComponent.mpr
      (incidenceCoordinate_mem_section Gamma xi)
  have ht :
      (incidenceComponentRay Gamma xi).lower < (t : EReal) ∧
        (t : EReal) < (incidenceComponentRay Gamma xi).upper := by
    change t ∈ {s : Real |
      (incidenceComponentRay Gamma xi).lower < (s : EReal) ∧
        (s : EReal) < (incidenceComponentRay Gamma xi).upper}
    rw [incidenceComponentRay_parameterSet Gamma xi]
    exact htcomponent
  exact ⟨t, ht.1, ht.2, rfl⟩

private theorem rayPoint_injective {n : Nat} (R : OrientedOpenRay n) :
    Function.Injective R.point := by
  intro s t hst
  have hcoord := congrArg (lineCoordinate R.direction) hst
  change
    lineCoordinate R.direction
        (R.anchor + s • R.direction) =
      lineCoordinate R.direction
        (R.anchor + t • R.direction) at hcoord
  unfold OrientedOpenRay.direction OrientedOpenRay.anchor at hcoord
  rw [
    lineCoordinate_point (t := s) R.property.1 R.property.2.1,
    lineCoordinate_point (t := t) R.property.1 R.property.2.1] at hcoord
  exact hcoord

private theorem rayParameter_mem_of_point_mem_carrier {n : Nat}
    (R : OrientedOpenRay n) {t : Real}
    (ht : R.point t ∈ R.carrier) :
    R.lower < (t : EReal) ∧ (t : EReal) < R.upper := by
  obtain ⟨s, hsl, hsu, hs⟩ := ht
  have hst : s = t := rayPoint_injective R hs
  subst s
  exact ⟨hsl, hsu⟩

private theorem ray_anchor_eq_lineAnchor_of_mem {n : Nat}
    (R : OrientedOpenRay n) {z : Euclidean n}
    (hz : z ∈ R.carrier) :
    R.anchor = lineAnchor R.direction z := by
  obtain ⟨t, _htl, _htu, rfl⟩ := hz
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  have horth : inner Real R.anchor R.direction = 0 := R.property.2.1
  unfold lineAnchor OrientedOpenRay.point
  rw [inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, horth, hnorm]
  norm_num

private theorem primitiveLine_eq_ray_of_mem_openSegment {n : Nat}
    {R : OrientedOpenRay n} {x y : Euclidean n} {r : Real}
    (hne : x ≠ y)
    (hr : R.point r ∈ openSegment Real x y)
    (hdir : rayDirection x y = R.direction) :
    primitiveLine (x, y) = (R.direction, R.anchor) := by
  rw [openSegment_eq_image'] at hr
  obtain ⟨t, ht, hpoint⟩ := hr
  have hdir' :
      primitiveDirection (x, y) = R.direction := by
    simpa only [primitiveDirection] using hdir
  have hsub :
      y - x = ‖y - x‖ • primitiveDirection (x, y) := by
    unfold primitiveDirection rayDirection
    exact (NormedSpace.norm_smul_normalize (y - x)).symm
  have hz :
      R.point r =
        x + (t * ‖y - x‖) • primitiveDirection (x, y) := by
    calc
      R.point r = x + t • (y - x) := hpoint.symm
      _ = x + t •
          (‖y - x‖ • primitiveDirection (x, y)) :=
        congrArg (fun v => x + t • v) hsub
      _ = x + (t * ‖y - x‖) • primitiveDirection (x, y) := by
        module
  have hanchorR :
      lineAnchor R.direction (R.point r) = R.anchor := by
    unfold OrientedOpenRay.point
    exact lineAnchor_point R.property.1 R.property.2.1
  apply Prod.ext
  · exact hdir'
  · change lineAnchor (primitiveDirection (x, y)) x = R.anchor
    calc
      lineAnchor (primitiveDirection (x, y)) x =
          lineAnchor (primitiveDirection (x, y))
            (x + (t * ‖y - x‖) • primitiveDirection (x, y)) :=
        (lineAnchor_add_smul (primitiveDirection_norm hne) _).symm
      _ = lineAnchor R.direction (R.point r) := by rw [hz, hdir']
      _ = R.anchor := hanchorR

private theorem rayParameter_mem_primitiveInterval {n : Nat}
    {R : OrientedOpenRay n} {x y : Euclidean n} {r : Real}
    (hne : x ≠ y)
    (hr : R.point r ∈ openSegment Real x y)
    (hdir : rayDirection x y = R.direction) :
    r ∈ Ioo (primitiveLower (x, y)) (primitiveUpper (x, y)) := by
  let p : Euclidean n × Euclidean n := (x, y)
  have hline :
      primitiveLine p = (R.direction, R.anchor) :=
    primitiveLine_eq_ray_of_mem_openSegment hne hr hdir
  have hx : x = R.point (primitiveLower p) := by
    calc
      x = (primitiveLine p).2 +
          primitiveLower p • (primitiveLine p).1 :=
        (primitive_first_point p).symm
      _ = R.point (primitiveLower p) := by
        rw [hline]
        rfl
  have hy : y = R.point (primitiveUpper p) := by
    calc
      y = (primitiveLine p).2 +
          primitiveUpper p • (primitiveLine p).1 :=
        (primitive_second_point (p := p) hne).symm
      _ = R.point (primitiveUpper p) := by
        rw [hline]
        rfl
  rw [← openSegment_eq_Ioo (primitiveLower_lt_upper hne),
    openSegment_eq_image_lineMap]
  rw [openSegment_eq_image_lineMap] at hr
  obtain ⟨theta, htheta, hthetaPoint⟩ := hr
  refine ⟨theta, htheta, ?_⟩
  apply rayPoint_injective R
  calc
    R.point
        (AffineMap.lineMap
          (primitiveLower p) (primitiveUpper p) theta) =
        AffineMap.lineMap
          (R.point (primitiveLower p))
          (R.point (primitiveUpper p)) theta := by
      unfold OrientedOpenRay.point
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      module
    _ = AffineMap.lineMap x y theta :=
      congrArg₂
        (fun a b => AffineMap.lineMap a b theta) hx.symm hy.symm
    _ = R.point r := hthetaPoint

private theorem coveredBy_parameter_mem_orientedLineSection {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {R : OrientedOpenRay n} (hR : R.CoveredBy Gamma)
    {line : Euclidean n × Euclidean n}
    (hline : line = (R.direction, R.anchor))
    {r : Real} (hr : R.lower < (r : EReal) ∧ (r : EReal) < R.upper) :
    r ∈ orientedLineSection Gamma line := by
  obtain ⟨x, y, hxy, hne, hrxy, hdir⟩ :=
    hR (R.point r) ⟨r, hr.1, hr.2, rfl⟩
  refine ⟨(x, y), hxy, hne, ?_, ?_⟩
  · exact hline.trans
      (primitiveLine_eq_ray_of_mem_openSegment hne hrxy hdir).symm
  · exact rayParameter_mem_primitiveInterval hne hrxy hdir

private theorem incidenceComponentRay_isMaximalTransportRay {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (xi : OrientedLineIncidence Gamma) :
    (incidenceComponentRay Gamma xi).IsMaximalTransportRay Gamma := by
  have hcovered := incidenceComponentRay_coveredBy Gamma xi
  refine ⟨hcovered, ?_⟩
  intro S hsub hS
  let R := incidenceComponentRay Gamma xi
  let t := incidenceCoordinate xi
  have htcomponent :
      t ∈ ordConnectedComponent
        (orientedLineSection Gamma (incidenceLine xi)) t :=
    self_mem_ordConnectedComponent.mpr
      (incidenceCoordinate_mem_section Gamma xi)
  have htR :
      R.lower < (t : EReal) ∧ (t : EReal) < R.upper := by
    change t ∈ {s : Real |
      R.lower < (s : EReal) ∧ (s : EReal) < R.upper}
    rw [incidenceComponentRay_parameterSet Gamma xi]
    exact htcomponent
  have hzR : R.point t ∈ R.carrier :=
    ⟨t, htR.1, htR.2, rfl⟩
  have hzS : R.point t ∈ S.carrier := hsub hzR
  obtain ⟨x, y, hxy, hne, hzxy, hdirR⟩ :=
    hcovered (R.point t) hzR
  obtain ⟨x', y', hxy', hne', hzxy', hdirS⟩ :=
    hS (R.point t) hzS
  have hdir : S.direction = R.direction := by
    calc
      S.direction = rayDirection x' y' := hdirS.symm
      _ = rayDirection x y :=
        direction_eq_of_mem_openSegments hNoCrossing
          hxy' hxy hne' hne hzxy' hzxy
      _ = R.direction := hdirR
  have hanchor : S.anchor = R.anchor := by
    calc
      S.anchor = lineAnchor S.direction (R.point t) :=
        ray_anchor_eq_lineAnchor_of_mem S hzS
      _ = lineAnchor R.direction (R.point t) := by rw [hdir]
      _ = R.anchor :=
        (ray_anchor_eq_lineAnchor_of_mem R hzR).symm
  have hlineS :
      incidenceLine xi = (S.direction, S.anchor) := by
    apply Prod.ext
    · change (incidenceLine xi).1 = S.direction
      rw [hdir]
      rfl
    · change (incidenceLine xi).2 = S.anchor
      rw [hanchor]
      rfl
  have hpoint_t : S.point t = R.point t := by
    unfold OrientedOpenRay.point
    rw [hdir, hanchor]
  have htS :
      S.lower < (t : EReal) ∧ (t : EReal) < S.upper :=
    rayParameter_mem_of_point_mem_carrier S (hpoint_t ▸ hzS)
  let J : Set Real :=
    {r | S.lower < (r : EReal) ∧ (r : EReal) < S.upper}
  have htJ : t ∈ J := htS
  have hJsection :
      J ⊆ orientedLineSection Gamma (incidenceLine xi) := by
    intro r hr
    exact coveredBy_parameter_mem_orientedLineSection hS hlineS hr
  have hJord : OrdConnected J := by
    rw [ordConnected_def]
    intro a ha b hb r hr
    exact
      ⟨ha.1.trans_le (EReal.coe_le_coe_iff.mpr hr.1),
        (EReal.coe_le_coe_iff.mpr hr.2).trans_lt hb.2⟩
  letI : OrdConnected J := hJord
  have hJcomponent :
      J ⊆ ordConnectedComponent
        (orientedLineSection Gamma (incidenceLine xi)) t :=
    subset_ordConnectedComponent htJ hJsection
  intro z hz
  obtain ⟨r, hrl, hru, hpoint⟩ := hz
  have hrcomponent :
      r ∈ ordConnectedComponent
        (orientedLineSection Gamma (incidenceLine xi)) t :=
    hJcomponent ⟨hrl, hru⟩
  have hrR :
      R.lower < (r : EReal) ∧ (r : EReal) < R.upper := by
    change r ∈ {s : Real |
      R.lower < (s : EReal) ∧ (s : EReal) < R.upper}
    rw [incidenceComponentRay_parameterSet Gamma xi]
    exact hrcomponent
  refine ⟨r, hrR.1, hrR.2, ?_⟩
  calc
    R.point r = S.point r := by
      unfold OrientedOpenRay.point
      rw [hdir, hanchor]
    _ = z := hpoint

end BorelMaximalRay

/-- Paper Lemma 1: the maximal oriented transport ray through a point is a
Borel function of that point. -/
theorem solution
    (n : Nat)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hNoCrossing : NoCrossing Gamma) :
    MeasurableSet (transportSet Gamma) /\
      exists pi : transportSet Gamma -> OrientedOpenRay n,
        Measurable pi /\ IsMaximalRayAssignment Gamma pi := by
  classical
  have _hDiagonal := hDiagonal
  clear _hDiagonal hDiagonal
  have hTransportMeasurable :
      MeasurableSet (transportSet Gamma) :=
    BorelMaximalRay.transportSet_measurable hSigma
  refine ⟨hTransportMeasurable, ?_⟩
  by_cases hTransportNonempty : Nonempty (transportSet Gamma)
  · have hIncidenceMeasurable :
        MeasurableSet
          (BorelMaximalRay.orientedLineIncidenceSet Gamma) :=
      BorelMaximalRay.orientedLineIncidence_measurable hSigma
    letI : StandardBorelSpace (transportSet Gamma) :=
      hTransportMeasurable.standardBorel
    letI : StandardBorelSpace
        (BorelMaximalRay.OrientedLineIncidence Gamma) :=
      hIncidenceMeasurable.standardBorel
    let f :
        BorelMaximalRay.OrientedLineIncidence Gamma →
          transportSet Gamma :=
      BorelMaximalRay.lineIncidenceToTransport Gamma
    have hfSurjective : Function.Surjective f := by
      simpa only [f] using
        BorelMaximalRay.surjective_lineIncidenceToTransport Gamma
    letI : Nonempty
        (BorelMaximalRay.OrientedLineIncidence Gamma) :=
      ⟨(hfSurjective hTransportNonempty.some).choose⟩
    have hfMeasurable : Measurable f := by
      simpa only [f] using
        BorelMaximalRay.measurable_lineIncidenceToTransport Gamma
    have hfInjective : Function.Injective f := by
      simpa only [f] using
        BorelMaximalRay.injective_lineIncidenceToTransport hNoCrossing
    let hfEmbedding : MeasurableEmbedding f :=
      hfMeasurable.measurableEmbedding hfInjective
    let xi :
        transportSet Gamma →
          BorelMaximalRay.OrientedLineIncidence Gamma :=
      hfEmbedding.invFun
    have hxiMeasurable : Measurable xi := by
      exact hfEmbedding.measurable_invFun
    have hxiLeft : Function.LeftInverse xi f := by
      exact hfEmbedding.leftInverse_invFun
    have hxiRight : Function.RightInverse xi f := by
      intro z
      obtain ⟨c, rfl⟩ := hfSurjective z
      rw [hxiLeft c]
    have hComponentMeasurable :
        MeasurableSet
          (BorelMaximalRay.incidenceComponentRelation Gamma) :=
      BorelMaximalRay.measurable_incidenceComponentRelation hSigma
    let pi : transportSet Gamma → OrientedOpenRay n :=
      fun z => BorelMaximalRay.incidenceComponentRay Gamma (xi z)
    have hpiMeasurable : Measurable pi :=
      (BorelMaximalRay.measurable_incidenceComponentRay
        Gamma hComponentMeasurable).comp hxiMeasurable
    refine ⟨pi, hpiMeasurable, ?_⟩
    intro z
    refine
      ⟨BorelMaximalRay.incidenceComponentRay_isMaximalTransportRay
        hNoCrossing (xi z), ?_⟩
    have hz :=
      BorelMaximalRay.incidencePoint_mem_componentRay_carrier
        Gamma (xi z)
    have heval :
        BorelMaximalRay.linePointEvaluation (xi z).1 = z.1 :=
      congrArg Subtype.val (hxiRight z)
    rw [← heval]
    exact hz
  · let pi : transportSet Gamma → OrientedOpenRay n :=
      fun z => False.elim (hTransportNonempty ⟨z⟩)
    have hpiMeasurable : Measurable pi := by
      intro s hs
      have hempty : pi ⁻¹' s = ∅ := by
        ext z
        exact False.elim (hTransportNonempty ⟨z⟩)
      rw [hempty]
      exact MeasurableSet.empty
    refine ⟨pi, hpiMeasurable, ?_⟩
    intro z
    exact False.elim (hTransportNonempty ⟨z⟩)
