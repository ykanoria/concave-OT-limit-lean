import Theorems.Thm_ConcaveOTLimit_contactDirectionCompactExhaustion
import Theorems.Thm_ConcaveOTLimit_existsSegmentwiseLipschitzDirectionField
import Theorems.Thm_ConcaveOTLimit_distanceContactSubsetNoCrossing
import Theorems.Thm_ConcaveOTLimit_transportSetIsSigmaCompact
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Geometry.Euclidean.Volume.Measure

open MeasureTheory Set
open scoped ENNReal

namespace ConcaveOTLimit

noncomputable section

/-- The forward direction selected at differentiability points of the
one-Lipschitz contact potential. -/
def contactEndpointDirection {n : Nat}
    (u : Euclidean n -> Real) (x : Euclidean n) : Euclidean n :=
  -gradient u x

theorem measurable_contactEndpointDirection {n : Nat}
    (u : Euclidean n -> Real) :
    Measurable (contactEndpointDirection u) := by
  apply Measurable.neg
  change Measurable fun x =>
    (InnerProductSpace.toDual Real (Euclidean n)).symm
      (fderiv Real u x)
  exact
    (InnerProductSpace.toDual Real (Euclidean n)).symm.continuous.measurable.comp
      (measurable_fderiv Real u)

theorem fderiv_apply_rayDirection_eq_neg_one
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hne : x ≠ y)
    (hDiff : DifferentiableAt Real u x) :
    fderiv Real u x (rayDirection x y) = -1 := by
  let g : Real -> Real := fun t => u (AffineMap.lineMap x y t)
  have hg :
      HasDerivAt g (fderiv Real u x (y - x)) 0 := by
    have hcomp :=
      hDiff.hasFDerivAt.comp_hasDerivAt_of_eq
        (x := (0 : Real))
        (AffineMap.hasDerivAt_lineMap (𝕜 := Real)
          (a := x) (b := y) (x := (0 : Real)))
        (by simp)
    simpa only [g, Function.comp_apply] using hcomp
  have hline :
      ∀ t ∈ Icc (0 : Real) 1,
        g t = u x - t * dist x y := by
    intro t ht
    have hz :
        AffineMap.lineMap x y t ∈ segment Real x y :=
      lineMap_mem_segment (𝕜 := Real) x y ht
    have hcontact :=
      (distanceContactSegmentSaturation u hu hxy hz).1
    change
      dist x (AffineMap.lineMap x y t) =
        u x - u (AffineMap.lineMap x y t) at hcontact
    rw [dist_left_lineMap, Real.norm_eq_abs,
      abs_of_nonneg ht.1] at hcontact
    dsimp [g]
    linarith
  have haffine :
      HasDerivWithinAt
        (fun t : Real => u x - t * dist x y)
        (-dist x y) (Icc (0 : Real) 1) 0 := by
    convert
      (hasDerivWithinAt_const (x := (0 : Real))
        (s := Icc (0 : Real) 1) (c := u x)).sub
        ((hasDerivWithinAt_id (x := (0 : Real))
          (s := Icc (0 : Real) 1)).mul_const (dist x y)) using 1 <;>
      ring
  have hgWithin :
      HasDerivWithinAt g (-dist x y)
        (Icc (0 : Real) 1) 0 :=
    haffine.congr_of_mem
      hline ⟨le_rfl, zero_le_one⟩
  have hscaled :
      fderiv Real u x (y - x) = -dist x y :=
    ((uniqueDiffOn_Icc_zero_one (0 : Real)
      ⟨le_rfl, zero_le_one⟩).eq_deriv
      (Icc (0 : Real) 1)
      hg.hasDerivWithinAt hgWithin)
  have hdistPos : 0 < dist x y := dist_pos.mpr hne
  rw [dist_eq_norm'] at hscaled
  have hnormNe : ‖y - x‖ ≠ 0 :=
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm))
  rw [rayDirection, NormedSpace.normalize,
    map_smul, hscaled]
  simp only [smul_eq_mul]
  field_simp

theorem contactEndpointDirection_eq_rayDirection
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hne : x ≠ y)
    (hDiff : DifferentiableAt Real u x) :
    contactEndpointDirection u x = rayDirection x y := by
  let g := gradient u x
  let d := rayDirection x y
  have hdNorm : ‖d‖ = 1 := by
    dsimp [d, rayDirection]
    exact NormedSpace.norm_normalize (sub_ne_zero.mpr hne.symm)
  have hinner : inner Real g d = -1 := by
    dsimp [g, d]
    rw [inner_gradient_left hDiff]
    exact fderiv_apply_rayDirection_eq_neg_one u hu hxy hne hDiff
  have hgNorm : ‖g‖ <= 1 := by
    dsimp [g, gradient]
    rw [(InnerProductSpace.toDual Real (Euclidean n)).symm.norm_map]
    exact norm_fderiv_le_of_lipschitz Real hu
  have hgNormSq : ‖g‖ ^ 2 <= 1 := by
    nlinarith [norm_nonneg g]
  have hsumSq := norm_add_sq_real g d
  rw [hdNorm, hinner] at hsumSq
  have hsumZero : ‖g + d‖ = 0 := by
    nlinarith [sq_nonneg ‖g + d‖]
  have hsum : g + d = 0 := norm_eq_zero.mp hsumZero
  change -g = d
  exact neg_eq_iff_add_eq_zero.mpr hsum

theorem add_smul_rayDirection_mem_openSegment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y : E} (hne : x ≠ y) {s : Real}
    (hs : 0 < s) (hslt : s < dist x y) :
    x + s • rayDirection x y ∈ openSegment Real x y := by
  rw [openSegment_eq_image_lineMap]
  let t := s / dist x y
  have hdistPos : 0 < dist x y := dist_pos.mpr hne
  have ht : t ∈ Ioo (0 : Real) 1 := by
    exact ⟨div_pos hs hdistPos, (div_lt_one hdistPos).2 hslt⟩
  refine ⟨t, ht, ?_⟩
  have hscale : s • rayDirection x y = t • (y - x) := by
    have hsEq : s = t * dist x y := by
      dsimp [t]
      field_simp
    rw [hsEq, rayDirection, mul_smul, dist_eq_norm',
      NormedSpace.norm_smul_normalize]
  rw [AffineMap.lineMap_apply_module', hscale, add_comm]

theorem contactEndpointForwardSupport
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {x y : Euclidean n}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hne : x ≠ y)
    (hDiff : DifferentiableAt Real u x)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltaLength : delta <= dist x y) :
    let d := contactEndpointDirection u x
    ‖d‖ = 1 /\
      u (x + delta • d) = u x - delta := by
  let d := contactEndpointDirection u x
  have hd : d = rayDirection x y :=
    contactEndpointDirection_eq_rayDirection u hu hxy hne hDiff
  have hdNorm : ‖d‖ = 1 := by
    rw [hd]
    exact NormedSpace.norm_normalize (sub_ne_zero.mpr hne.symm)
  have hmem : x + delta • d ∈ segment Real x y := by
    by_cases hdeltaLt : delta < dist x y
    · exact openSegment_subset_segment Real x y <| by
        rw [hd]
        exact add_smul_rayDirection_mem_openSegment hne hdelta hdeltaLt
    · have heq : delta = dist x y :=
        le_antisymm hdeltaLength (le_of_not_gt hdeltaLt)
      have hpoint : x + delta • d = y := by
        rw [heq, hd, rayDirection, dist_eq_norm',
          NormedSpace.norm_smul_normalize]
        abel
      rw [hpoint]
      exact right_mem_segment (𝕜 := Real) x y
  have hcontact :=
    (distanceContactSegmentSaturation u hu hxy hmem).1
  have hdist : dist x (x + delta • d) = delta := by
    have hvec : x - (x + delta • d) = -(delta • d) := by
      module
    rw [dist_eq_norm]
    rw [hvec, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hdelta, hdNorm, mul_one]
  change dist x (x + delta • d) = u x - u (x + delta • d) at hcontact
  exact ⟨hdNorm, by linarith⟩

theorem contactEndpointDirection_inner_sub_le
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {x y x' y' : Euclidean n}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hxy' : (x', y') ∈ distanceContactSet u)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hDiff : DifferentiableAt Real u x)
    (hDiff' : DifferentiableAt Real u x')
    {delta : Real} (hdelta : 0 < delta)
    (hdeltaLength : delta <= dist x y)
    (hdeltaLength' : delta <= dist x' y') :
    inner Real
        (contactEndpointDirection u x -
          contactEndpointDirection u x')
        (x' - x) <=
      (2 * delta⁻¹) * ‖x' - x‖ ^ 2 := by
  let d := contactEndpointDirection u x
  let e := contactEndpointDirection u x'
  let h := x' - x
  let q := u x' - u x
  obtain ⟨hdNorm, hdSupport⟩ :=
    contactEndpointForwardSupport
      u hu hxy hne hDiff hdelta hdeltaLength
  obtain ⟨heNorm, heSupport⟩ :=
    contactEndpointForwardSupport
      u hu hxy' hne' hDiff' hdelta hdeltaLength'
  have hqAbs : |q| <= ‖h‖ := by
    have hLip := hu.dist_le_mul x x'
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hLip
    simpa only [q, h, abs_sub_comm, dist_eq_norm, norm_sub_rev] using hLip
  by_cases hfar : delta <= ‖h‖
  · have hdeNorm : ‖d - e‖ <= 2 := by
      calc
        ‖d - e‖ <= ‖d‖ + ‖e‖ := norm_sub_le _ _
        _ = 2 := by rw [hdNorm, heNorm]; norm_num
    have hinnerNorm :
        inner Real (d - e) h <= 2 * ‖h‖ := by
      exact (real_inner_le_norm (d - e) h).trans <| by
        gcongr
    change inner Real (d - e) h <= (2 * delta⁻¹) * ‖h‖ ^ 2
    rw [show (2 * delta⁻¹) * ‖h‖ ^ 2 =
      (2 * ‖h‖ ^ 2) / delta by field_simp]
    apply (le_div_iff₀ hdelta).2
    calc
      inner Real (d - e) h * delta <=
          (2 * ‖h‖) * delta :=
        mul_le_mul_of_nonneg_right hinnerNorm hdelta.le
      _ <= 2 * ‖h‖ ^ 2 := by
        nlinarith [norm_nonneg h]
  · have hnear : ‖h‖ < delta := lt_of_not_ge hfar
    have hqLower : -‖h‖ <= q := (abs_le.mp hqAbs).1
    have hqUpper : q <= ‖h‖ := (abs_le.mp hqAbs).2
    have hcrossD :
        delta + q <= ‖h - delta • d‖ := by
      have hLip := hu.le_add_mul x' (x + delta • d)
      rw [hdSupport] at hLip
      simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hLip
      have hvec : x' - (x + delta • d) = h - delta • d := by
        dsimp [h]
        module
      rw [hvec] at hLip
      dsimp [q]
      linarith
    have hcrossE :
        delta - q <= ‖h + delta • e‖ := by
      have hLip := hu.le_add_mul x (x' + delta • e)
      rw [heSupport] at hLip
      simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hLip
      have hvec : x - (x' + delta • e) = -(h + delta • e) := by
        dsimp [h]
        module
      rw [hvec, norm_neg] at hLip
      dsimp [q]
      linarith
    have hcrossDNonneg : 0 <= delta + q := by
      linarith
    have hcrossENonneg : 0 <= delta - q := by
      linarith
    have hcrossDSq :
        (delta + q) ^ 2 <= ‖h - delta • d‖ ^ 2 :=
      (sq_le_sq₀ hcrossDNonneg (norm_nonneg _)).2 hcrossD
    have hcrossESq :
        (delta - q) ^ 2 <= ‖h + delta • e‖ ^ 2 :=
      (sq_le_sq₀ hcrossENonneg (norm_nonneg _)).2 hcrossE
    have hnormD :
        ‖h - delta • d‖ ^ 2 =
          ‖h‖ ^ 2 - 2 * delta * inner Real h d + delta ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
        abs_of_pos hdelta, real_inner_smul_right, hdNorm]
      ring
    have hnormE :
        ‖h + delta • e‖ ^ 2 =
          ‖h‖ ^ 2 + 2 * delta * inner Real h e + delta ^ 2 := by
      rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
        abs_of_pos hdelta, real_inner_smul_right, heNorm]
      ring
    rw [hnormD] at hcrossDSq
    rw [hnormE] at hcrossESq
    have hstrong :
        inner Real (d - e) h <= delta⁻¹ * ‖h‖ ^ 2 := by
      rw [inner_sub_left]
      rw [show delta⁻¹ * ‖h‖ ^ 2 = ‖h‖ ^ 2 / delta by
        field_simp]
      apply (le_div_iff₀ hdelta).2
      nlinarith [sq_nonneg q, real_inner_comm d h,
        real_inner_comm e h]
    change inner Real (d - e) h <= (2 * delta⁻¹) * ‖h‖ ^ 2
    calc
      inner Real (d - e) h <= delta⁻¹ * ‖h‖ ^ 2 := hstrong
      _ <= (2 * delta⁻¹) * ‖h‖ ^ 2 := by
        have hinv : 0 <= delta⁻¹ := inv_nonneg.mpr hdelta.le
        nlinarith [sq_nonneg ‖h‖]

/-- Positive times tending to zero and staying below one eighth of the
uniform contact length. -/
def contactEndpointShiftTime (delta : Real) (j : Nat) : Real :=
  delta / (8 * ((j : Real) + 1))

theorem contactEndpointShiftTime_pos
    {delta : Real} (hdelta : 0 < delta) (j : Nat) :
    0 < contactEndpointShiftTime delta j := by
  exact div_pos hdelta (by positivity)

theorem contactEndpointShiftTime_le
    {delta : Real} (hdelta : 0 < delta) (j : Nat) :
    contactEndpointShiftTime delta j <= delta / 8 := by
  rw [contactEndpointShiftTime]
  have hj0 : (0 : Real) <= (j : Real) := Nat.cast_nonneg j
  have hj : (1 : Real) <= (j : Real) + 1 := by linarith
  apply (div_le_iff₀ (by positivity : (0 : Real) < 8 * ((j : Real) + 1))).2
  nlinarith

theorem contactEndpointShiftTime_lt_delta
    {delta : Real} (hdelta : 0 < delta) (j : Nat) :
    contactEndpointShiftTime delta j < delta := by
  exact
    (contactEndpointShiftTime_le hdelta j).trans_lt
      (by linarith)

theorem contactEndpointShiftTime_injective
    {delta : Real} (hdelta : 0 < delta) :
    Function.Injective (contactEndpointShiftTime delta) := by
  intro i j hij
  rw [contactEndpointShiftTime, contactEndpointShiftTime] at hij
  have hi : (8 * ((i : Real) + 1)) ≠ 0 := by positivity
  have hj : (8 * ((j : Real) + 1)) ≠ 0 := by positivity
  rw [div_eq_div_iff hi hj] at hij
  have hcast : (i : Real) = (j : Real) := by
    nlinarith
  exact_mod_cast hcast

theorem contactEndpointShift_pairwise_antilipschitz
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {delta : Real} (hdelta : 0 < delta)
    {x x' y y' : Euclidean n}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hxy' : (x', y') ∈ distanceContactSet u)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hDiff : DifferentiableAt Real u x)
    (hDiff' : DifferentiableAt Real u x')
    (hdeltaLength : delta <= dist x y)
    (hdeltaLength' : delta <= dist x' y')
    (j : Nat) :
    dist x x' <=
      2 * dist
        (x + contactEndpointShiftTime delta j •
          contactEndpointDirection u x)
        (x' + contactEndpointShiftTime delta j •
          contactEndpointDirection u x') := by
  let d := contactEndpointDirection u x
  let e := contactEndpointDirection u x'
  let h := x' - x
  let s := contactEndpointShiftTime delta j
  have hInner :=
    contactEndpointDirection_inner_sub_le
      u hu hxy hxy' hne hne' hDiff hDiff'
      hdelta hdeltaLength hdeltaLength'
  change inner Real (d - e) h <=
    (2 * delta⁻¹) * ‖h‖ ^ 2 at hInner
  have hsPos : 0 < s :=
    contactEndpointShiftTime_pos hdelta j
  have hsLe : s <= delta / 8 :=
    contactEndpointShiftTime_le hdelta j
  let q := h + s • (e - d)
  have hqNormSq :
      ‖q‖ ^ 2 =
        ‖h‖ ^ 2 -
          2 * s * inner Real (d - e) h +
          s ^ 2 * ‖e - d‖ ^ 2 := by
    dsimp [q]
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos hsPos, real_inner_smul_right]
    have hinner :
        inner Real h (e - d) = -inner Real (d - e) h := by
      calc
        inner Real h (e - d) =
            inner Real h e - inner Real h d := inner_sub_right _ _ _
        _ = inner Real e h - inner Real d h := by
          rw [real_inner_comm h e, real_inner_comm h d]
        _ = -(inner Real d h - inner Real e h) := by ring
        _ = -inner Real (d - e) h := by rw [inner_sub_left]
    rw [hinner]
    ring
  have hqLower :
      (1 / 2 : Real) * ‖h‖ ^ 2 <= ‖q‖ ^ 2 := by
    rw [hqNormSq]
    have hinvPos : 0 <= delta⁻¹ := inv_nonneg.mpr hdelta.le
    have hscale : 4 * s * delta⁻¹ <= 1 / 2 := by
      rw [show (1 / 2 : Real) = 4 * (delta / 8) * delta⁻¹ by
        field_simp [hdelta.ne']; norm_num]
      have hmul :=
        mul_le_mul_of_nonneg_right hsLe
          (mul_nonneg (by norm_num : (0 : Real) <= 4) hinvPos)
      convert hmul using 1 <;> ring
    have hinnerScaled :
        2 * s * inner Real (d - e) h <=
          4 * s * delta⁻¹ * ‖h‖ ^ 2 := by
      have hsNonneg : 0 <= 2 * s := by positivity
      convert mul_le_mul_of_nonneg_left hInner hsNonneg using 1 <;> ring
    nlinarith [sq_nonneg (s * ‖e - d‖),
      sq_nonneg ‖h‖,
      mul_nonneg (sub_nonneg.mpr hscale) (sq_nonneg ‖h‖)]
  have hnorm : ‖h‖ <= 2 * ‖q‖ := by
    apply (sq_le_sq₀ (norm_nonneg h)
      (mul_nonneg (by norm_num) (norm_nonneg q))).mp
    nlinarith [sq_nonneg ‖q‖, sq_nonneg ‖h‖]
  have hdist :
      dist
          (x + s • d)
          (x' + s • e) =
        ‖q‖ := by
    rw [dist_eq_norm]
    have hvec :
        (x + s • d) - (x' + s • e) = -q := by
      dsimp [q, h]
      module
    rw [hvec, norm_neg]
  change dist x x' <=
    2 * dist (x + s • d) (x' + s • e)
  rw [dist_eq_norm]
  have hxx' : ‖x - x'‖ = ‖h‖ := by
    dsimp [h]
    exact norm_sub_rev x x'
  rw [hxx', hdist]
  exact hnorm

theorem volume_le_image_of_pairwiseAntilipschitz
    {n : Nat} {f : Euclidean n -> Euclidean n}
    {A : Set (Euclidean n)} {K : NNReal}
    (hf : ∀ ⦃x⦄, x ∈ A -> ∀ ⦃y⦄, y ∈ A ->
      dist x y <= (K : Real) * dist (f x) (f y)) :
    (volume : Measure (Euclidean n)) A <=
      (K : ENNReal) ^ (n : Real) *
        (volume : Measure (Euclidean n)) (f '' A) := by
  classical
  let g : Euclidean n -> Euclidean n := fun z =>
    if hz : z ∈ f '' A then Classical.choose hz else 0
  have hg_mem : ∀ ⦃z⦄, z ∈ f '' A -> g z ∈ A := by
    intro z hz
    simpa only [g, dif_pos hz] using (Classical.choose_spec hz).1
  have hf_g : ∀ ⦃z⦄, z ∈ f '' A -> f (g z) = z := by
    intro z hz
    simpa only [g, dif_pos hz] using (Classical.choose_spec hz).2
  have hgLip : LipschitzOnWith K g (f '' A) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hf_g hz, hf_g hw] using hf (hg_mem hz) (hg_mem hw)
  have hgImage : g '' (f '' A) = A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hg_mem hz
    · intro hx
      refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
      have hfx : f x ∈ f '' A := ⟨x, hx, rfl⟩
      have hzero := hf (hg_mem hfx) hx
      rw [hf_g hfx, dist_self, mul_zero] at hzero
      exact dist_le_zero.mp hzero
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  simp only [finrank_euclideanSpace_fin,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  have h := hgLip.hausdorffMeasure_image_le
    (d := (n : Real)) (by positivity)
  rw [hgImage] at h
  exact (mul_le_mul_right h _).trans_eq (by ac_rfl)

theorem volume_eq_zero_of_wandering_pairwiseAntilipschitz
    {n : Nat} (A B : Set (Euclidean n))
    (T : Nat -> Euclidean n -> Euclidean n)
    (hAmeasurable : MeasurableSet A)
    (hTmeasurable : ∀ j, Measurable (T j))
    (hanti : ∀ j, ∀ ⦃x⦄, x ∈ A -> ∀ ⦃y⦄, y ∈ A ->
      dist x y <= 2 * dist (T j x) (T j y))
    (hdisjoint : ∀ ⦃i j : Nat⦄, i ≠ j ->
      Disjoint (T i '' A) (T j '' A))
    (hinside : ∀ j, T j '' A ⊆ B)
    (hBfinite : (volume : Measure (Euclidean n)) B < ∞) :
    (volume : Measure (Euclidean n)) A = 0 := by
  have hInjective :
      ∀ j, Set.InjOn (T j) A := by
    intro j x hx y hy hxy
    apply dist_le_zero.mp
    simpa only [hxy, dist_self, mul_zero] using hanti j hx hy
  have hImageMeasurable :
      ∀ j, MeasurableSet (T j '' A) := by
    intro j
    exact
      hAmeasurable.image_of_measurable_injOn
        (hTmeasurable j) (hInjective j)
  let D : ENNReal := (2 : ENNReal) ^ (n : Real)
  by_contra hA0
  let c : ENNReal := (volume : Measure (Euclidean n)) A / D
  have hD0 : D ≠ 0 := by simp [D]
  have hDtop : D ≠ ∞ := by simp [D]
  have hc0 : c ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hA0, hDtop⟩
  have hc_le :
      ∀ j, c <=
        (volume : Measure (Euclidean n)) (T j '' A) := by
    intro j
    rw [ENNReal.div_le_iff hD0 hDtop]
    simpa only [mul_comm, D] using
      volume_le_image_of_pairwiseAntilipschitz
        (K := (2 : NNReal)) (hanti j)
  have hsum_top : (∑' _j : Nat, c) = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero hc0
  let restrictedVolume : Measure (Euclidean n) :=
    (volume : Measure (Euclidean n)).restrict B
  have hsum_le :
      (∑' j : Nat,
          (volume : Measure (Euclidean n)) (T j '' A)) <=
        (volume : Measure (Euclidean n)) B := by
    have hmeasure := tsum_measure_le_measure_univ
      (μ := restrictedVolume)
      (s := fun j => T j '' A)
      (fun j => (hImageMeasurable j).nullMeasurableSet)
      (fun i j hij => (hdisjoint hij).aedisjoint)
    simpa only [restrictedVolume, Measure.restrict_apply_univ,
      Measure.restrict_apply (hImageMeasurable _),
      inter_eq_left.mpr (hinside _)] using hmeasure
  have htop :
      (∞ : ENNReal) <=
        (volume : Measure (Euclidean n)) B := by
    rw [← hsum_top]
    exact (ENNReal.tsum_le_tsum hc_le).trans hsum_le
  exact (not_lt_of_ge htop) hBfinite

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
  rcases hGamma x y x' y' hxy hxy' hne hne' hdir hinter with
      hleft | hright
  · subst x'
    exact hdir (rayDirection_eq_of_common_left hz hz')
  · subst y'
    exact hdir (rayDirection_eq_of_common_right hz hz')

theorem contactEndpointShifts_ne
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    {x x' y y' : Euclidean n}
    (hxy : (x, y) ∈ Gamma)
    (hxy' : (x', y') ∈ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hxOut : x ∉ transportSet Gamma)
    (hxOut' : x' ∉ transportSet Gamma)
    (hDiff : DifferentiableAt Real u x)
    (hDiff' : DifferentiableAt Real u x')
    {s t : Real}
    (hs : 0 < s) (ht : 0 < t)
    (hsLength : s < dist x y)
    (htLength : t < dist x' y')
    (hst : s ≠ t) :
    x + s • contactEndpointDirection u x ≠
      x' + t • contactEndpointDirection u x' := by
  intro heq
  have hd :
      contactEndpointDirection u x = rayDirection x y :=
    contactEndpointDirection_eq_rayDirection
      u hu (hContact hxy) hne hDiff
  have hd' :
      contactEndpointDirection u x' = rayDirection x' y' :=
    contactEndpointDirection_eq_rayDirection
      u hu (hContact hxy') hne' hDiff'
  have hz : x + s • rayDirection x y ∈ openSegment Real x y :=
    add_smul_rayDirection_mem_openSegment hne hs hsLength
  have hz' :
      x + s • rayDirection x y ∈ openSegment Real x' y' := by
    rw [← hd, heq, hd']
    exact add_smul_rayDirection_mem_openSegment
      hne' ht htLength
  have hdir : rayDirection x y = rayDirection x' y' :=
    direction_eq_of_mem_openSegments
      hNoCrossing hxy hxy' hne hne' hz hz'
  have heq' :
      x + s • rayDirection x' y' =
        x' + t • rayDirection x' y' := by
    simpa only [hd, hd', hdir] using heq
  rcases lt_or_gt_of_ne hst with hstLt | htsLt
  · have hpoint :
        x = x' + (t - s) • rayDirection x' y' := by
      calc
        x = (x + s • rayDirection x' y') -
            s • rayDirection x' y' := by module
        _ = (x' + t • rayDirection x' y') -
            s • rayDirection x' y' := by rw [heq']
        _ = x' + (t - s) • rayDirection x' y' := by module
    have hpos : 0 < t - s := sub_pos.mpr hstLt
    have hlength : t - s < dist x' y' := by
      linarith
    exact hxOut
      ⟨(x', y'), hxy', hne',
        hpoint ▸
          add_smul_rayDirection_mem_openSegment
            hne' hpos hlength⟩
  · have hpoint :
        x' = x + (s - t) • rayDirection x y := by
      calc
        x' = (x' + t • rayDirection x' y') -
            t • rayDirection x' y' := by module
        _ = (x + s • rayDirection x' y') -
            t • rayDirection x' y' := by rw [← heq']
        _ = x + (s - t) • rayDirection x' y' := by module
        _ = x + (s - t) • rayDirection x y := by rw [hdir]
    have hpos : 0 < s - t := sub_pos.mpr htsLt
    have hlength : s - t < dist x y := by
      linarith
    exact hxOut'
      ⟨(x, y), hxy, hne,
        hpoint ▸
          add_smul_rayDirection_mem_openSegment
            hne hpos hlength⟩

def compactEndpointSource {n : Nat}
    (K : Set (Euclidean n × Euclidean n)) (delta : Real) :
    Set (Euclidean n) :=
  Prod.fst '' (K ∩ {p | delta <= dist p.1 p.2})

theorem isCompact_compactEndpointSource
    {n : Nat} {K : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (delta : Real) :
    IsCompact (compactEndpointSource K delta) := by
  exact
    (hK.inter_right
      (isClosed_le continuous_const
        (continuous_fst.dist continuous_snd))).image continuous_fst

def contactEndpointPiece {n : Nat}
    (u : Euclidean n -> Real)
    (Gamma : Set (Euclidean n × Euclidean n))
    (K : Set (Euclidean n × Euclidean n))
    (delta R : Real) : Set (Euclidean n) :=
  ((compactEndpointSource K delta ∩ Metric.closedBall 0 R) ∩
      {x | DifferentiableAt Real u x}) \
    transportSet Gamma

theorem volume_contactEndpointPiece_eq_zero
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    {Gamma K : Set (Euclidean n × Euclidean n)}
    (hSigma : IsSigmaCompact Gamma)
    (hNoCrossing : NoCrossing Gamma)
    (hContact : Gamma ⊆ distanceContactSet u)
    (hK : IsCompact K)
    (hKsubset : K ⊆ Gamma)
    {delta R : Real}
    (hdelta : 0 < delta)
    (hdeltaOne : delta <= 1) :
    (volume : Measure (Euclidean n))
        (contactEndpointPiece u Gamma K delta R) = 0 := by
  let A := contactEndpointPiece u Gamma K delta R
  let B : Set (Euclidean n) := Metric.ball 0 (R + 1)
  let T : Nat -> Euclidean n -> Euclidean n :=
    fun j x =>
      x + contactEndpointShiftTime delta j •
        contactEndpointDirection u x
  have hAmeasurable : MeasurableSet A := by
    have hTransportMeasurable :
        MeasurableSet (transportSet Gamma) := by
      obtain ⟨L, hL, hLcover⟩ := transportSetIsSigmaCompact hSigma
      rw [← hLcover]
      exact MeasurableSet.iUnion fun i => (hL i).measurableSet
    apply MeasurableSet.diff
    · apply MeasurableSet.inter
      · exact
          (isCompact_compactEndpointSource hK delta).measurableSet.inter
            measurableSet_closedBall
      · exact measurableSet_of_differentiableAt Real u
    · exact hTransportMeasurable
  have hPiece :
      ∀ ⦃x⦄, x ∈ A ->
        DifferentiableAt Real u x /\
          x ∉ transportSet Gamma /\
          x ∈ Metric.closedBall (0 : Euclidean n) R /\
          ∃ y, (x, y) ∈ Gamma /\ x ≠ y /\
            delta <= dist x y := by
    intro x hx
    rcases hx.1.1.1 with ⟨p, hp, hpx⟩
    subst x
    have hpGamma : (p.1, p.2) ∈ Gamma := by
      simpa only [Prod.mk.eta] using hKsubset hp.1
    have hpNe : p.1 ≠ p.2 :=
      dist_pos.mp (hdelta.trans_le hp.2)
    exact
      ⟨hx.1.2, hx.2, hx.1.1.2, p.2,
        hpGamma, hpNe, hp.2⟩
  have hTmeasurable : ∀ j, Measurable (T j) := by
    intro j
    exact measurable_id.add
      (measurable_const.smul
        (measurable_contactEndpointDirection u))
  have hanti :
      ∀ j, ∀ ⦃x⦄, x ∈ A -> ∀ ⦃x'⦄, x' ∈ A ->
        dist x x' <= 2 * dist (T j x) (T j x') := by
    intro j x hx x' hx'
    obtain ⟨hDiff, _hxOut, _hxBall, y, hxy, hne, hLength⟩ :=
      hPiece hx
    obtain ⟨hDiff', _hxOut', _hxBall', y', hxy', hne', hLength'⟩ :=
      hPiece hx'
    simpa only [T] using
      contactEndpointShift_pairwise_antilipschitz
        u hu hdelta (hContact hxy) (hContact hxy')
        hne hne' hDiff hDiff' hLength hLength' j
  have hdisjoint :
      ∀ ⦃i j : Nat⦄, i ≠ j ->
        Disjoint (T i '' A) (T j '' A) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases hzi with ⟨x, hx, hxz⟩
    rcases hzj with ⟨x', hx', hxz'⟩
    obtain ⟨hDiff, hxOut, _hxBall, y, hxy, hne, hLength⟩ :=
      hPiece hx
    obtain ⟨hDiff', hxOut', _hxBall', y', hxy', hne', hLength'⟩ :=
      hPiece hx'
    have hsLength :
        contactEndpointShiftTime delta i < dist x y :=
      (contactEndpointShiftTime_lt_delta hdelta i).trans_le hLength
    have htLength :
        contactEndpointShiftTime delta j < dist x' y' :=
      (contactEndpointShiftTime_lt_delta hdelta j).trans_le hLength'
    have hneShift :=
      contactEndpointShifts_ne
        u hu hNoCrossing hxy hxy' hContact hne hne'
        hxOut hxOut' hDiff hDiff'
        (contactEndpointShiftTime_pos hdelta i)
        (contactEndpointShiftTime_pos hdelta j)
        hsLength htLength
        ((contactEndpointShiftTime_injective hdelta).ne hij)
    apply hneShift
    exact hxz.trans hxz'.symm
  have hinside : ∀ j, T j '' A ⊆ B := by
    intro j z hz
    rcases hz with ⟨x, hx, rfl⟩
    obtain ⟨hDiff, _hxOut, hxBall, y, hxy, hne, hLength⟩ :=
      hPiece hx
    have hdNorm :
        ‖contactEndpointDirection u x‖ = 1 :=
      (contactEndpointForwardSupport
        u hu (hContact hxy) hne hDiff hdelta hLength).1
    have hsPos :=
      contactEndpointShiftTime_pos hdelta j
    have hsLe :=
      contactEndpointShiftTime_le hdelta j
    have hxNorm : ‖x‖ <= R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxBall
    change dist
      (x + contactEndpointShiftTime delta j •
        contactEndpointDirection u x) 0 < R + 1
    rw [dist_zero_right]
    calc
      ‖x + contactEndpointShiftTime delta j •
          contactEndpointDirection u x‖ <=
          ‖x‖ + ‖contactEndpointShiftTime delta j •
            contactEndpointDirection u x‖ :=
        norm_add_le _ _
      _ = ‖x‖ + contactEndpointShiftTime delta j := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsPos, hdNorm, mul_one]
      _ <= R + delta / 8 := add_le_add hxNorm hsLe
      _ < R + 1 := by linarith
  exact
    volume_eq_zero_of_wandering_pairwiseAntilipschitz
      A B T hAmeasurable hTmeasurable hanti hdisjoint hinside
      measure_ball_lt_top

theorem mem_leftTransportSet_diff_transportSet_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} {x : E} :
    x ∈ leftTransportSet Gamma \ transportSet Gamma ↔
      x ∉ transportSet Gamma ∧
        ∃ y, (x, y) ∈ Gamma ∧ x ≠ y := by
  constructor
  · rintro ⟨hxLeft, hxNotTransport⟩
    rcases hxLeft with
      ⟨p, hpGamma, hpNe, hxSegment, hxNeRight⟩
    have hxEqLeft : x = p.1 := by
      rw [← insert_endpoints_openSegment] at hxSegment
      rcases hxSegment with
        (rfl | rfl | hxOpen)
      · rfl
      · exact (hxNeRight rfl).elim
      · exact
          (hxNotTransport
            ⟨p, hpGamma, hpNe, hxOpen⟩).elim
    subst x
    exact ⟨hxNotTransport, p.2, hpGamma, hpNe⟩
  · rintro ⟨hxNotTransport, y, hxy, hne⟩
    refine ⟨?_, hxNotTransport⟩
    exact
      ⟨(x, y), hxy, hne,
        left_mem_segment (𝕜 := Real) x y, hne⟩

theorem contactLeftEndpointNegligible
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hContact : Gamma ⊆ distanceContactSet u) :
    (volume : Measure (Euclidean n))
        (leftTransportSet Gamma \ transportSet Gamma) = 0 := by
  have hSigma' : IsSigmaCompact Gamma := hSigma
  obtain ⟨K, hK, hKcover⟩ := hSigma
  let P : Nat -> Nat -> Nat -> Set (Euclidean n) :=
    fun m k r =>
      contactEndpointPiece u Gamma (K m)
        (((k : Real) + 1)⁻¹) (r : Real)
  have hKsubset : ∀ m, K m ⊆ Gamma := by
    intro m
    rw [← hKcover]
    exact subset_iUnion K m
  have hPzero :
      ∀ m k r,
        (volume : Measure (Euclidean n)) (P m k r) = 0 := by
    intro m k r
    have hdenom : (0 : Real) < (k : Real) + 1 := by positivity
    have hdenomOne : (1 : Real) <= (k : Real) + 1 := by
      have hk : (0 : Real) <= (k : Real) := Nat.cast_nonneg k
      linarith
    exact
      volume_contactEndpointPiece_eq_zero
        u hu hSigma'
        (distanceContactSubsetNoCrossing u hu hContact)
        hContact (hK m) (hKsubset m)
        (inv_pos.mpr hdenom)
        (inv_le_one_of_one_le₀ hdenomOne)
  have hUnionZero :
      (volume : Measure (Euclidean n))
        (⋃ m, ⋃ k, ⋃ r, P m k r) = 0 := by
    apply measure_iUnion_null
    intro m
    apply measure_iUnion_null
    intro k
    apply measure_iUnion_null
    exact hPzero m k
  have hNonDiffZero :
      (volume : Measure (Euclidean n))
        {x | ¬ DifferentiableAt Real u x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hu.ae_differentiableAt] with x hx
    simpa only [mem_setOf_eq, not_not] using hx
  apply measure_mono_null
    (t := {x | ¬ DifferentiableAt Real u x} ∪
      (⋃ m, ⋃ k, ⋃ r, P m k r))
  · intro x hx
    by_cases hDiff : DifferentiableAt Real u x
    · right
      obtain ⟨hxOut, y, hxy, hne⟩ :=
        mem_leftTransportSet_diff_transportSet_iff.mp hx
      have hxyUnion : (x, y) ∈ ⋃ m, K m := by
        rw [hKcover]
        exact hxy
      obtain ⟨m, hm⟩ := mem_iUnion.mp hxyUnion
      obtain ⟨k, hk⟩ :=
        exists_nat_one_div_lt (dist_pos.mpr hne)
      obtain ⟨r, hr⟩ := exists_nat_ge ‖x‖
      apply mem_iUnion.mpr
      refine ⟨m, mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨r, ?_⟩⟩⟩
      refine ⟨⟨⟨?_, ?_⟩, hDiff⟩, hxOut⟩
      · exact
          ⟨(x, y), ⟨hm, by simpa only [one_div] using hk.le⟩, rfl⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hr
    · exact Or.inl hDiff
  · exact measure_union_null hNonDiffZero hUnionZero

end
end ConcaveOTLimit
