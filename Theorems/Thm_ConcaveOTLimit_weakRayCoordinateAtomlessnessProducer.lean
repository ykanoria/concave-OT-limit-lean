import Theorems.Thm_ConcaveOTLimit_rayCoarea
import Mathlib.Geometry.Euclidean.Volume.Measure

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-! ## A wandering-section nullity criterion -/

/-- An antilipschitz self-map of Euclidean space cannot decrease
full-dimensional volume by more than its Hausdorff distortion factor. -/
theorem volume_le_image_of_antilipschitz
    {n : Nat} {f : Euclidean n -> Euclidean n} {K : NNReal}
    (hf : AntilipschitzWith K f) (s : Set (Euclidean n)) :
    (volume : Measure (Euclidean n)) s <=
      (K : ENNReal) ^ (n : Real) *
        (volume : Measure (Euclidean n)) (f '' s) := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  simp only [finrank_euclideanSpace_fin,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  have h := hf.le_hausdorffMeasure_image
    (d := (n : Real)) (by positivity) s
  exact (mul_le_mul_right h _).trans_eq (by ac_rfl)

/-- A measurable set is volume-null if it has countably many pairwise
disjoint images in one finite-volume set and every image has a common
positive lower volume-distortion bound. -/
theorem volume_eq_zero_of_wandering_images
    {n : Nat} (A B : Set (Euclidean n))
    (T : Nat -> Euclidean n -> Euclidean n)
    (himage : forall j, MeasurableSet (T j '' A))
    (hdisjoint : forall ⦃i j : Nat⦄, i ≠ j ->
      Disjoint (T i '' A) (T j '' A))
    (hinside : forall j, T j '' A ⊆ B)
    (hBfinite : (volume : Measure (Euclidean n)) B < ∞)
    (D : ENNReal) (hD0 : D ≠ 0) (hDtop : D ≠ ∞)
    (hdistort : forall j,
      (volume : Measure (Euclidean n)) A <=
        D * (volume : Measure (Euclidean n)) (T j '' A)) :
    (volume : Measure (Euclidean n)) A = 0 := by
  by_contra hA0
  let c : ENNReal := (volume : Measure (Euclidean n)) A / D
  have hc0 : c ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hA0, hDtop⟩
  have hc_le :
      forall j, c <=
        (volume : Measure (Euclidean n)) (T j '' A) := by
    intro j
    rw [ENNReal.div_le_iff hD0 hDtop]
    simpa only [mul_comm] using hdistort j
  have hsum_top : (∑' _j : Nat, c) = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero hc0
  let nu : Measure (Euclidean n) :=
    (volume : Measure (Euclidean n)).restrict B
  have hsum_le :
      (∑' j : Nat,
          (volume : Measure (Euclidean n)) (T j '' A)) <=
        (volume : Measure (Euclidean n)) B := by
    have hnu := tsum_measure_le_measure_univ (μ := nu)
      (s := fun j => T j '' A)
      (fun j => (himage j).nullMeasurableSet)
      (fun i j hij => (hdisjoint hij).aedisjoint)
    simpa only [nu, Measure.restrict_apply_univ,
      Measure.restrict_apply (himage _),
      inter_eq_left.mpr (hinside _)] using hnu
  have htop :
      (∞ : ENNReal) <=
        (volume : Measure (Euclidean n)) B := by
    rw [← hsum_top]
    exact (ENNReal.tsum_le_tsum hc_le).trans hsum_le
  exact (not_lt_of_ge htop) hBfinite

private def raySectionShiftRadius
    (M : NNReal) (m : Nat) : Real :=
  min (1 / (2 * ((m : Real) + 1)))
    (1 / (4 * ((M : Real) + 1)))

private def raySectionShiftTime
    (M : NNReal) (m j : Nat) : Real :=
  raySectionShiftRadius M m / ((j : Real) + 1)

private theorem raySectionShiftRadius_pos
    (M : NNReal) (m : Nat) :
    0 < raySectionShiftRadius M m := by
  rw [raySectionShiftRadius]
  exact lt_min (by positivity) (by positivity)

private theorem raySectionShiftTime_pos
    (M : NNReal) (m j : Nat) :
    0 < raySectionShiftTime M m j := by
  unfold raySectionShiftTime
  exact div_pos (raySectionShiftRadius_pos M m) (by positivity)

private theorem raySectionShiftTime_le_radius
    (M : NNReal) (m j : Nat) :
    raySectionShiftTime M m j <= raySectionShiftRadius M m := by
  have hj0 : (0 : Real) <= (j : Real) := Nat.cast_nonneg j
  have hjpos : (0 : Real) < (j : Real) + 1 := by linarith
  have hj : (1 : Real) <= (j : Real) + 1 := by linarith
  rw [raySectionShiftTime]
  apply (div_le_iff₀ hjpos).2
  nlinarith [raySectionShiftRadius_pos M m]

private theorem raySectionShiftTime_lt_gap
    (M : NNReal) (m j : Nat) :
    raySectionShiftTime M m j < 1 / ((m : Real) + 1) := by
  have hr_le :
      raySectionShiftRadius M m <=
        1 / (2 * ((m : Real) + 1)) :=
    min_le_left _ _
  have hhalf_lt :
      1 / (2 * ((m : Real) + 1)) <
        1 / ((m : Real) + 1) := by
    have hm : (0 : Real) < (m : Real) + 1 := by positivity
    field_simp
    linarith
  exact (raySectionShiftTime_le_radius M m j).trans_lt
    (hr_le.trans_lt hhalf_lt)

private theorem raySectionShiftTime_lipschitz_bound
    (M : NNReal) (m j : Nat) :
    ‖raySectionShiftTime M m j‖₊ * M <=
      (1 / 2 : NNReal) := by
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_mul, coe_nnnorm, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat]
  rw [Real.norm_of_nonneg
    (raySectionShiftTime_pos M m j).le]
  have hr_le :
      raySectionShiftRadius M m <=
        1 / (4 * ((M : Real) + 1)) :=
    min_le_right _ _
  have hM : (0 : Real) <= M := NNReal.coe_nonneg M
  calc
    raySectionShiftTime M m j * (M : Real) <=
        (1 / (4 * ((M : Real) + 1))) * (M : Real) := by
      exact mul_le_mul_of_nonneg_right
        ((raySectionShiftTime_le_radius M m j).trans hr_le) hM
    _ <= 1 / 2 := by
      rw [div_mul_eq_mul_div,
        div_le_iff₀
          (by positivity :
            (0 : Real) < 4 * ((M : Real) + 1))]
      nlinarith

private theorem raySectionShiftTime_injective
    (M : NNReal) (m : Nat) :
    Function.Injective (raySectionShiftTime M m) := by
  intro i j hij
  rw [raySectionShiftTime, raySectionShiftTime] at hij
  have hi0 : (i : Real) + 1 ≠ 0 := by positivity
  have hj0 : (j : Real) + 1 ≠ 0 := by positivity
  rw [div_eq_div_iff hi0 hj0] at hij
  have hcast : (i : Real) = (j : Real) := by
    nlinarith [raySectionShiftRadius_pos M m]
  exact_mod_cast hcast

private theorem exists_nat_add_inv_lt_ereal
    {t : Real} {u : EReal} (h : (t : EReal) < u) :
    ∃ m : Nat,
      ((t + 1 / ((m : Real) + 1) : Real) : EReal) < u := by
  induction u using EReal.rec with
  | bot => simp at h
  | top => exact ⟨0, EReal.coe_lt_top _⟩
  | coe u =>
      have htu : t < u := EReal.coe_lt_coe_iff.mp h
      obtain ⟨m, hm⟩ :=
        exists_nat_one_div_lt (sub_pos.mpr htu)
      refine ⟨m, EReal.coe_lt_coe_iff.mpr ?_⟩
      norm_num at hm ⊢
      linarith

private theorem point_rayCoordinate_eq_of_mem_carrier
    {n : Nat} (R : OrientedOpenRay n) {x : Euclidean n}
    (hx : x ∈ R.carrier) :
    R.point (rayCoordinate R x) = x := by
  obtain ⟨t, _htl, _htu, ht⟩ := hx
  rw [← ht, rayCoordinate_point_apply]

private theorem rayCoordinate_bounds_of_mem_carrier
    {n : Nat} (R : OrientedOpenRay n) {x : Euclidean n}
    (hx : x ∈ R.carrier) :
    R.lower < (rayCoordinate R x : EReal) ∧
      (rayCoordinate R x : EReal) < R.upper := by
  obtain ⟨t, htl, htu, ht⟩ := hx
  rw [← ht, rayCoordinate_point_apply]
  exact ⟨htl, htu⟩

private theorem rayShift_eq_point
    {n : Nat} (R : OrientedOpenRay n) {x : Euclidean n}
    (hx : x ∈ R.carrier) (s : Real) :
    x + s • R.direction =
      R.point (rayCoordinate R x + s) := by
  nth_rw 1 [← point_rayCoordinate_eq_of_mem_carrier R hx]
  simp only [OrientedOpenRay.point, add_smul]
  abel

private theorem rayShift_mem_carrier
    {n : Nat} (R : OrientedOpenRay n) {x : Euclidean n}
    (hx : x ∈ R.carrier) {s : Real} (hs : 0 <= s)
    (hupper :
      ((rayCoordinate R x + s : Real) : EReal) < R.upper) :
    x + s • R.direction ∈ R.carrier := by
  refine ⟨rayCoordinate R x + s, ?_, hupper, ?_⟩
  · exact (rayCoordinate_bounds_of_mem_carrier R hx).1.trans_le
      (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right hs))
  · exact (rayShift_eq_point R hx s).symm

/-! ## Measurable enumeration of the atoms of a real kernel -/

/-- A countable family of measurable sections which contains every atom of
every measure in a real-valued kernel. This is automatic for finite kernels
on a standard Borel space, but that general measurable-enumeration theorem
is not currently available in Mathlib. -/
def HasMeasurableAtomEnumeration
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) : Prop :=
  ∃ atom : Nat -> A -> Real,
    (∀ j, Measurable (atom j)) ∧
      ∀ a t, kappa a {t} ≠ 0 -> ∃ j, atom j a = t

/-- The graph of a measurable real-valued section. -/
def measurableSectionGraph
    {A : Type*} [MeasurableSpace A]
    (atom : A -> Real) : Set (A × Real) :=
  {p | p.2 = atom p.1}

theorem measurableSet_measurableSectionGraph
    {A : Type*} [MeasurableSpace A]
    {atom : A -> Real} (hatom : Measurable atom) :
    MeasurableSet (measurableSectionGraph atom) := by
  exact measurableSet_eq_fun measurable_snd
    (hatom.comp measurable_fst)

@[simp]
theorem prodMk_preimage_measurableSectionGraph
    {A : Type*} [MeasurableSpace A]
    (atom : A -> Real) (a : A) :
    Prod.mk a ⁻¹' measurableSectionGraph atom = {atom a} := by
  ext t
  simp [measurableSectionGraph]

/-- If every graph in a countable measurable enumeration of the atoms has
zero composition-product mass, then almost every kernel measure is
atomless. -/
theorem kernel_ae_atomless_of_measurableAtomEnumeration
    {A : Type*} [MeasurableSpace A]
    (sigma : Measure A) [SFinite sigma]
    (kappa : Kernel A Real) [IsFiniteKernel kappa]
    (henum : HasMeasurableAtomEnumeration kappa)
    (hgraph :
      ∀ atom : A -> Real, Measurable atom ->
        (sigma ⊗ₘ kappa) (measurableSectionGraph atom) = 0) :
    ∀ᵐ a ∂sigma, ∀ t, kappa a {t} = 0 := by
  obtain ⟨atom, hatom, hcover⟩ := henum
  have hzero :
      ∀ j, ∀ᵐ a ∂sigma, kappa a {atom j a} = 0 := by
    intro j
    have hGraphMeasurable :
        MeasurableSet (measurableSectionGraph (atom j)) :=
      measurableSet_measurableSectionGraph (hatom j)
    have hIntegral :
        ∫⁻ a, kappa a {atom j a} ∂sigma = 0 := by
      have h := hgraph (atom j) (hatom j)
      rw [Measure.compProd_apply hGraphMeasurable] at h
      simpa only [prodMk_preimage_measurableSectionGraph] using h
    have hMeasurable :
        Measurable fun a => kappa a {atom j a} := by
      simpa only [prodMk_preimage_measurableSectionGraph] using
        Kernel.measurable_kernel_prodMk_left hGraphMeasurable
    exact (lintegral_eq_zero_iff hMeasurable).mp hIntegral
  have hzeroAll :
      ∀ᵐ a ∂sigma, ∀ j, kappa a {atom j a} = 0 :=
    ae_all_iff.mpr hzero
  filter_upwards [hzeroAll] with a ha
  intro t
  by_contra ht
  obtain ⟨j, hj⟩ := hcover a t ht
  exact ht (by simpa only [hj] using ha j)

/-! ## From null coordinate sections to conditional atomlessness -/

/-- The graph-like ambient section which chooses one scalar coordinate on
each labeled ray. -/
def rayCoordinateSection
    {n : Nat} (pointLabel : Euclidean n -> OrientedOpenRay n)
    (atom : OrientedOpenRay n -> Real) : Set (Euclidean n) :=
  {x | rayCoordinateAlongLabel pointLabel x =
    atom (pointLabel x)}

/-- A ray-coordinate section localized to one compact direction piece and
to points whose upper endpoint is at least `1 / (m + 1)` farther along the
ray. -/
def rayCoordinateUpperGapSection
    {n : Nat} (pointLabel : Euclidean n -> OrientedOpenRay n)
    (atom : OrientedOpenRay n -> Real) (piece : Set (Euclidean n))
    (m : Nat) : Set (Euclidean n) :=
  (rayCoordinateSection pointLabel atom ∩ piece) ∩
    {x |
      ((rayCoordinateAlongLabel pointLabel x +
          1 / ((m : Real) + 1) : Real) : EReal) <
        (pointLabel x).upper}

theorem measurableSet_rayCoordinateSection
    {n : Nat} {pointLabel : Euclidean n -> OrientedOpenRay n}
    {atom : OrientedOpenRay n -> Real}
    (hpointLabel : Measurable pointLabel) (hatom : Measurable atom) :
    MeasurableSet (rayCoordinateSection pointLabel atom) := by
  exact measurableSet_eq_fun
    (measurable_rayCoordinateAlongLabel hpointLabel)
    (hatom.comp hpointLabel)

theorem measurableSet_rayCoordinateUpperGapSection
    {n : Nat} {pointLabel : Euclidean n -> OrientedOpenRay n}
    {atom : OrientedOpenRay n -> Real} {piece : Set (Euclidean n)}
    (hpointLabel : Measurable pointLabel) (hatom : Measurable atom)
    (hpiece : MeasurableSet piece) (m : Nat) :
    MeasurableSet
      (rayCoordinateUpperGapSection pointLabel atom piece m) := by
  apply (measurableSet_rayCoordinateSection hpointLabel hatom).inter
    hpiece |>.inter
  exact measurableSet_lt
    ((measurable_rayCoordinateAlongLabel hpointLabel).add_const
      (1 / ((m : Real) + 1))).coe_real_ereal
    (OrientedOpenRay.measurable_upper.comp hpointLabel)

/-- On one compact Lipschitz direction piece and one uniform upper-endpoint
gap class, every measurable ray-coordinate section has zero ambient
volume. The proof uses countably many small shifts along the rays. -/
theorem volume_rayCoordinateUpperGapSection_eq_zero
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (hpointLabel :
      Measurable
        (RayLabelGeometry.pointRay Gamma pi defaultRay))
    (atom : OrientedOpenRay n -> Real) (hatom : Measurable atom)
    (k m : Nat) :
    (volume : Measure (Euclidean n))
      (rayCoordinateUpperGapSection
        (RayLabelGeometry.pointRay Gamma pi defaultRay)
        atom (hRegularity.compactPiece k) m) = 0 := by
  let pointLabel : Euclidean n -> OrientedOpenRay n :=
    RayLabelGeometry.pointRay Gamma pi defaultRay
  let A : Set (Euclidean n) :=
    rayCoordinateUpperGapSection pointLabel atom
      (hRegularity.compactPiece k) m
  obtain ⟨L, hL⟩ := hRegularity.directionLipschitz k
  obtain ⟨g, hg, hgOn⟩ := hL.extend_finite_dimension
  let M : NNReal :=
    lipschitzExtensionConstant (Euclidean n) * L
  have hgM : LipschitzWith M g := by
    simpa only [M] using hg
  let T : Nat -> Euclidean n -> Euclidean n :=
    fun j x => x + raySectionShiftTime M m j • g x
  have hAmeasurable : MeasurableSet A := by
    simpa only [A, pointLabel] using
      measurableSet_rayCoordinateUpperGapSection
        hpointLabel hatom
        (hRegularity.compactPieceIsCompact k).measurableSet m
  have hPiece :
      forall ⦃x⦄, x ∈ A ->
        x ∈ hRegularity.compactPiece k := by
    intro x hx
    exact hx.1.2
  have hTransport :
      forall ⦃x⦄, x ∈ A -> x ∈ transportSet Gamma := by
    intro x hx
    exact mem_transportSet_of_mem_compactPiece hRegularity
      ⟨k, hPiece hx⟩
  have hCarrier :
      forall ⦃x⦄, x ∈ A -> x ∈ (pointLabel x).carrier := by
    intro x hx
    have hxT := hTransport hx
    change x ∈
      (RayLabelGeometry.pointRay Gamma pi defaultRay x).carrier
    rw [RayLabelGeometry.pointRay_of_mem pi defaultRay hxT]
    exact (hpi ⟨x, hxT⟩).2
  have hMaximal :
      forall ⦃x⦄, x ∈ A ->
        (pointLabel x).IsMaximalTransportRay Gamma := by
    intro x hx
    have hxT := hTransport hx
    change
      (RayLabelGeometry.pointRay Gamma pi defaultRay x)
        |>.IsMaximalTransportRay Gamma
    rw [RayLabelGeometry.pointRay_of_mem pi defaultRay hxT]
    exact (hpi ⟨x, hxT⟩).1
  have hDirection :
      forall ⦃x⦄, x ∈ A -> g x = (pointLabel x).direction := by
    intro x hx
    have hxT := hTransport hx
    exact (hgOn (hPiece hx)).symm.trans
      (pointRay_direction_eq_directionField_of_mem
        hRegularity pi hpi defaultRay hxT).symm
  have hShiftCarrier :
      forall (j : Nat) ⦃x⦄, x ∈ A ->
        T j x ∈ (pointLabel x).carrier := by
    intro j x hx
    have hxGap := hx.2
    change
      ((rayCoordinate (pointLabel x) x +
          1 / ((m : Real) + 1) : Real) : EReal) <
        (pointLabel x).upper at hxGap
    have hupper :
        ((rayCoordinate (pointLabel x) x +
            raySectionShiftTime M m j : Real) : EReal) <
          (pointLabel x).upper := by
      have hreal :
          rayCoordinate (pointLabel x) x +
              raySectionShiftTime M m j <
            rayCoordinate (pointLabel x) x +
              1 / ((m : Real) + 1) :=
        add_lt_add_right
          (raySectionShiftTime_lt_gap M m j) _
      exact (EReal.coe_lt_coe_iff.mpr hreal).trans hxGap
    have hmem := rayShift_mem_carrier
      (pointLabel x) (hCarrier hx)
      (raySectionShiftTime_pos M m j).le hupper
    change
      x + raySectionShiftTime M m j • g x ∈
        (pointLabel x).carrier
    rw [hDirection hx]
    exact hmem
  have hHalfLipschitz :
      forall j,
        LipschitzWith (1 / 2 : NNReal)
          (fun x : Euclidean n =>
            raySectionShiftTime M m j • g x) := by
    intro j
    have hsmul :
        LipschitzWith (‖raySectionShiftTime M m j‖₊ * M)
          (fun x : Euclidean n =>
            raySectionShiftTime M m j • g x) := by
      simpa only [Function.comp_apply] using
        (lipschitzWith_smul
          (raySectionShiftTime M m j)).comp hgM
    exact hsmul.weaken
      (raySectionShiftTime_lipschitz_bound M m j)
  have hTLipschitz :
      forall j, LipschitzWith (1 + 1 / 2 : NNReal) (T j) := by
    intro j
    simpa only [T, id_eq] using
      LipschitzWith.id.add (hHalfLipschitz j)
  have hTAntilipschitz :
      forall j, AntilipschitzWith 2 (T j) := by
    intro j
    have hanti :=
      AntilipschitzWith.id.add_lipschitzWith
        (hHalfLipschitz j) (by norm_num)
    have hconstant :
        (((1 : NNReal)⁻¹ - 1 / 2)⁻¹ : NNReal) = 2 := by
      apply NNReal.eq
      norm_num [NNReal.coe_sub]
    rw [hconstant] at hanti
    simpa only [T, id_eq] using hanti
  have hImageMeasurable :
      forall j, MeasurableSet (T j '' A) := by
    intro j
    exact ((hTLipschitz j).continuous.measurableEmbedding
      (hTAntilipschitz j).injective).measurableSet_image'
        hAmeasurable
  have hDisjoint :
      forall ⦃i j : Nat⦄, i ≠ j ->
        Disjoint (T i '' A) (T j '' A) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    obtain ⟨x, hxA, hxz⟩ := hzi
    obtain ⟨y, hyA, hyz⟩ := hzj
    have hzX : z ∈ (pointLabel x).carrier := by
      rw [← hxz]
      exact hShiftCarrier i hxA
    have hzY : z ∈ (pointLabel y).carrier := by
      rw [← hyz]
      exact hShiftCarrier j hyA
    have hLabel : pointLabel x = pointLabel y := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (disjoint_maximalRay_carriers_of_ne
          hRegularity (hMaximal hxA) (hMaximal hyA) hne))
        hzX hzY
    have hxCoordinate := hxA.1.1
    have hyCoordinate := hyA.1.1
    change
      rayCoordinate (pointLabel x) x = atom (pointLabel x)
        at hxCoordinate
    change
      rayCoordinate (pointLabel y) y = atom (pointLabel y)
        at hyCoordinate
    have hCoordinate :
        rayCoordinate (pointLabel x) x =
          rayCoordinate (pointLabel x) y := by
      calc
        rayCoordinate (pointLabel x) x =
            atom (pointLabel x) := hxCoordinate
        _ = atom (pointLabel y) := congrArg atom hLabel
        _ = rayCoordinate (pointLabel y) y := hyCoordinate.symm
        _ = rayCoordinate (pointLabel x) y := by rw [hLabel]
    have hyCarrier :
        y ∈ (pointLabel x).carrier := by
      rw [hLabel]
      exact hCarrier hyA
    have hxy : x = y :=
      rayCoordinate_injOn_carrier (pointLabel x)
        (hCarrier hxA) hyCarrier hCoordinate
    subst y
    have hTij : T i x = T j x := hxz.trans hyz.symm
    have hsmul :
        raySectionShiftTime M m i • (pointLabel x).direction =
          raySectionShiftTime M m j • (pointLabel x).direction := by
      apply add_left_cancel (a := x)
      simpa only [T, hDirection hxA] using hTij
    have hDirectionNe : (pointLabel x).direction ≠ 0 := by
      apply norm_ne_zero_iff.mp
      have hnorm : ‖(pointLabel x).direction‖ = 1 := by
        simpa only [OrientedOpenRay.direction] using
          (pointLabel x).property.1
      rw [hnorm]
      norm_num
    have htime :
        raySectionShiftTime M m i =
          raySectionShiftTime M m j :=
      smul_left_injective Real hDirectionNe hsmul
    exact hij (raySectionShiftTime_injective M m htime)
  obtain ⟨r, hr⟩ :=
    (hRegularity.compactPieceIsCompact k).isBounded
      |>.subset_closedBall (0 : Euclidean n)
  let B : Set (Euclidean n) :=
    Metric.closedBall (0 : Euclidean n)
      (r + raySectionShiftRadius M m)
  have hInside : forall j, T j '' A ⊆ B := by
    intro j z hz
    obtain ⟨x, hxA, rfl⟩ := hz
    have hxBound :
        dist x (0 : Euclidean n) <= r := by
      simpa only [dist_comm] using
        (Metric.mem_closedBall.mp (hr (hPiece hxA)))
    have hgNorm : ‖g x‖ = 1 := by
      rw [hDirection hxA]
      simpa only [OrientedOpenRay.direction] using
        (pointLabel x).property.1
    have hshiftNorm :
        ‖raySectionShiftTime M m j • g x‖ <=
          raySectionShiftRadius M m := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (raySectionShiftTime_pos M m j), hgNorm,
        mul_one]
      exact raySectionShiftTime_le_radius M m j
    rw [Metric.mem_closedBall]
    calc
      dist (T j x) 0 <= dist (T j x) x + dist x 0 :=
        dist_triangle _ _ _
      _ = ‖raySectionShiftTime M m j • g x‖ + dist x 0 := by
        congr 1
        simp only [T, dist_eq_norm, add_sub_cancel_left]
      _ <= raySectionShiftRadius M m + r :=
        add_le_add hshiftNorm hxBound
      _ = r + raySectionShiftRadius M m := add_comm _ _
  change (volume : Measure (Euclidean n)) A = 0
  apply volume_eq_zero_of_wandering_images A B T
    hImageMeasurable hDisjoint hInside
    (by
      exact measure_closedBall_lt_top)
    ((2 : ENNReal) ^ (n : Real))
  · simp
  · simp
  · intro j
    exact volume_le_image_of_antilipschitz
      (hTAntilipschitz j) A

/-- Every measurable ray-coordinate section is volume-null on each compact
piece of the countably Lipschitz direction exhaustion. -/
theorem volume_rayCoordinateSection_inter_compactPiece_eq_zero
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (hpointLabel :
      Measurable
        (RayLabelGeometry.pointRay Gamma pi defaultRay))
    (atom : OrientedOpenRay n -> Real) (hatom : Measurable atom)
    (k : Nat) :
    (volume : Measure (Euclidean n))
      (rayCoordinateSection
          (RayLabelGeometry.pointRay Gamma pi defaultRay) atom ∩
        hRegularity.compactPiece k) = 0 := by
  let pointLabel : Euclidean n -> OrientedOpenRay n :=
    RayLabelGeometry.pointRay Gamma pi defaultRay
  let coordSection : Set (Euclidean n) :=
    rayCoordinateSection pointLabel atom
  let gapSection : Nat -> Set (Euclidean n) :=
    fun m =>
      rayCoordinateUpperGapSection pointLabel atom
        (hRegularity.compactPiece k) m
  have hSubset :
      coordSection ∩ hRegularity.compactPiece k ⊆
        iUnion gapSection := by
    intro x hx
    have hxTransport :
        x ∈ transportSet Gamma :=
      mem_transportSet_of_mem_compactPiece hRegularity
        ⟨k, hx.2⟩
    have hxCarrier : x ∈ (pointLabel x).carrier := by
      change x ∈
        (RayLabelGeometry.pointRay Gamma pi defaultRay x).carrier
      rw [RayLabelGeometry.pointRay_of_mem
        pi defaultRay hxTransport]
      exact (hpi ⟨x, hxTransport⟩).2
    obtain ⟨m, hm⟩ :=
      exists_nat_add_inv_lt_ereal
        (rayCoordinate_bounds_of_mem_carrier
          (pointLabel x) hxCarrier).2
    apply mem_iUnion_of_mem m
    exact ⟨⟨hx.1, hx.2⟩, hm⟩
  have hEach : forall m,
      (volume : Measure (Euclidean n)) (gapSection m) = 0 := by
    intro m
    simpa only [gapSection, pointLabel] using
      volume_rayCoordinateUpperGapSection_eq_zero
        mu hRegularity pi hpi defaultRay hpointLabel atom hatom k m
  have hUnion :
      (volume : Measure (Euclidean n)) (iUnion gapSection) = 0 := by
    apply le_zero_iff.mp
    calc
      (volume : Measure (Euclidean n)) (iUnion gapSection) <=
          ∑' m, (volume : Measure (Euclidean n)) (gapSection m) :=
        measure_iUnion_le _
      _ = 0 := by simp only [hEach, tsum_zero]
  change
    (volume : Measure (Euclidean n))
      (coordSection ∩ hRegularity.compactPiece k) = 0
  exact measure_mono_null hSubset hUnion

/-- A source measure gives zero mass to every measurable section of the
label-coordinate map. -/
def RayCoordinateSectionsNull
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n) : Prop :=
  ∀ atom : OrientedOpenRay n -> Real, Measurable atom ->
    (mu : Measure (Euclidean n))
      (rayCoordinateSection pointLabel atom) = 0

/-- Absolute continuity of the source and its almost-everywhere compact
Lipschitz-ray exhaustion make every measurable ray-coordinate section
source-null. -/
theorem rayCoordinateSectionsNull_of_countablyLipschitz
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (hpi : IsMaximalRayAssignment Gamma pi)
    (defaultRay : OrientedOpenRay n)
    (hpointLabel :
      Measurable
        (RayLabelGeometry.pointRay Gamma pi defaultRay))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hCompact :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∃ k, x ∈ hRegularity.compactPiece k) :
    RayCoordinateSectionsNull mu
      (RayLabelGeometry.pointRay Gamma pi defaultRay) := by
  let pointLabel : Euclidean n -> OrientedOpenRay n :=
    RayLabelGeometry.pointRay Gamma pi defaultRay
  intro atom hatom
  let coordSection : Set (Euclidean n) :=
    rayCoordinateSection pointLabel atom
  have hEach : forall k,
      (volume : Measure (Euclidean n))
        (coordSection ∩ hRegularity.compactPiece k) = 0 := by
    intro k
    simpa only [coordSection, pointLabel] using
      volume_rayCoordinateSection_inter_compactPiece_eq_zero
        mu hRegularity pi hpi defaultRay hpointLabel atom hatom k
  have hUnionVolume :
      (volume : Measure (Euclidean n))
        (coordSection ∩ iUnion hRegularity.compactPiece) = 0 := by
    rw [inter_iUnion]
    apply le_zero_iff.mp
    calc
      (volume : Measure (Euclidean n))
          (⋃ k, coordSection ∩ hRegularity.compactPiece k) <=
        ∑' k, (volume : Measure (Euclidean n))
          (coordSection ∩ hRegularity.compactPiece k) :=
        measure_iUnion_le _
      _ = 0 := by simp only [hEach, tsum_zero]
  have hFull :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ iUnion hRegularity.compactPiece := by
    filter_upwards [hCompact] with x hx
    obtain ⟨k, hxk⟩ := hx
    exact mem_iUnion_of_mem k hxk
  have hSectionMembership :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∈ coordSection ↔
          x ∈ coordSection ∩ iUnion hRegularity.compactPiece := by
    filter_upwards [hFull] with x hx
    simp only [mem_inter_iff, hx, and_true]
  change
    (mu : Measure (Euclidean n)) coordSection = 0
  rw [measure_congr (eventuallyEq_set.mpr hSectionMembership)]
  exact hmuAC hUnionVolume

/-- The composition-product mass of a measurable coordinate section is its
source mass under the joint label-coordinate map. -/
theorem compProd_condDistrib_measurableSectionGraph
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (atom : OrientedOpenRay n -> Real)
    (hatom : Measurable atom) :
    ((Measure.map pointLabel (mu : Measure (Euclidean n))) ⊗ₘ
        condDistrib (rayCoordinateAlongLabel pointLabel) pointLabel
          (mu : Measure (Euclidean n)))
        (measurableSectionGraph atom) =
      (mu : Measure (Euclidean n))
        {x | rayCoordinateAlongLabel pointLabel x =
          atom (pointLabel x)} := by
  let coordinate := rayCoordinateAlongLabel pointLabel
  have hcoordinate : Measurable coordinate :=
    measurable_rayCoordinateAlongLabel hpointLabel
  rw [compProd_map_condDistrib hcoordinate.aemeasurable]
  rw [Measure.map_apply
    (hpointLabel.prodMk hcoordinate)
    (measurableSet_measurableSectionGraph hatom)]
  rfl

/-- Nullity of every measurable label-coordinate section, together with a
measurable enumeration of atoms of the real conditional kernel, implies the
exact coordinate-atomlessness conclusion used downstream. -/
theorem rayConditionalCoordinateAtomless_of_sectionsNull
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (pointLabel : Euclidean n -> OrientedOpenRay n)
    (hpointLabel : Measurable pointLabel)
    (henum :
      HasMeasurableAtomEnumeration
        (condDistrib (rayCoordinateAlongLabel pointLabel) pointLabel
          (mu : Measure (Euclidean n))))
    (hsections : RayCoordinateSectionsNull mu pointLabel) :
    RayConditionalCoordinateAtomless mu pointLabel := by
  let coordinate := rayCoordinateAlongLabel pointLabel
  let sigma :=
    Measure.map pointLabel (mu : Measure (Euclidean n))
  let kappa :=
    condDistrib coordinate pointLabel
      (mu : Measure (Euclidean n))
  have hkappaAtomless :
      ∀ᵐ R ∂sigma, ∀ t, kappa R {t} = 0 := by
    apply kernel_ae_atomless_of_measurableAtomEnumeration
      sigma kappa henum
    intro atom hatom
    rw [compProd_condDistrib_measurableSectionGraph
      mu pointLabel hpointLabel atom hatom]
    exact hsections atom hatom
  have hCoordinateEq :=
    canonicalRayCoordinateMeasure_eq_condDistrib
      mu pointLabel hpointLabel
  filter_upwards [hkappaAtomless, hCoordinateEq] with
      R hRAtomless hREq
  intro t
  change
    Measure.map (rayCoordinate R)
      (canonicalRaySourceKernel mu pointLabel R) {t} = 0
  rw [hREq]
  exact hRAtomless t

/-- The countably Lipschitz maximal-ray geometry proves the exact weak
atomlessness premise once the atoms of the real conditional kernel admit a
countable measurable enumeration. No coarea or conditional Hausdorff
absolute continuity is needed. -/
theorem countablyLipschitzRayCoordinateAtomlessPremise_of_atomEnumeration
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n)
    (henum :
      HasMeasurableAtomEnumeration
        (condDistrib
          (rayCoordinateAlongLabel
            (RayLabelGeometry.pointRay Gamma pi defaultRay))
          (RayLabelGeometry.pointRay Gamma pi defaultRay)
          (mu : Measure (Euclidean n)))) :
    CountablyLipschitzRayCoordinateAtomlessPremise
      mu Gamma hRegularity pi defaultRay := by
  intro hpi hpointLabel hmuAC hCompact
  apply rayConditionalCoordinateAtomless_of_sectionsNull
    mu (RayLabelGeometry.pointRay Gamma pi defaultRay)
    hpointLabel henum
  exact rayCoordinateSectionsNull_of_countablyLipschitz
    mu hRegularity pi hpi defaultRay hpointLabel hmuAC hCompact

end ConcaveOTLimit
