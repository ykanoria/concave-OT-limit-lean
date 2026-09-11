import Theorems.Thm_ConcaveOTLimit_distanceContactSegmentSaturation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

open Set

namespace ConcaveOTLimit

noncomputable section

/-- Two contact lines with symmetric contact neighborhoods of radii bounded
below by `epsilon` have directions separated by at most
`dist z w / epsilon`. -/
theorem contactUnitDirectionDist_le_of_radii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {z w d e : E} {a b epsilon : Real}
    (hepsilon : 0 < epsilon)
    (ha : epsilon <= a) (hb : epsilon <= b)
    (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hzLeft : u (z - a • d) = u z + a)
    (hzRight : u (z + a • d) = u z - a)
    (hwLeft : u (w - b • e) = u w + b)
    (hwRight : u (w + b • e) = u w - b) :
    dist d e <= epsilon⁻¹ * dist z w := by
  have haPos : 0 < a := hepsilon.trans_le ha
  have hbPos : 0 < b := hepsilon.trans_le hb
  by_cases hfar : 2 * epsilon <= dist z w
  · calc
      dist d e <= dist d 0 + dist 0 e := dist_triangle d 0 e
      _ = 2 := by simp [dist_eq_norm, hd, he]; norm_num
      _ <= epsilon⁻¹ * dist z w := by
        rw [inv_mul_eq_div, le_div_iff₀ hepsilon]
        exact hfar
  · have hnear : dist z w < 2 * epsilon := lt_of_not_ge hfar
    let delta : Real := u w - u z
    let h : E := w - z
    let v : E := a • d + b • e
    have hdeltaAbs : |delta| <= dist z w := by
      dsimp [delta]
      simpa only [Real.dist_eq, abs_sub_comm, NNReal.coe_one, one_mul] using
        hu.dist_le_mul z w
    have hdeltaLower : -dist z w <= delta := (abs_le.mp hdeltaAbs).1
    have hdeltaUpper : delta <= dist z w := (abs_le.mp hdeltaAbs).2
    have hcrossAdd :
        a + b - delta <= ‖h + v‖ := by
      have hcross := hu.le_add_mul (z - a • d) (w + b • e)
      rw [hzLeft, hwRight] at hcross
      simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hcross
      have hvec :
          (z - a • d) - (w + b • e) = -(h + v) := by
        dsimp [h, v]
        module
      rw [hvec, norm_neg] at hcross
      dsimp [delta]
      linarith
    have hcrossSub :
        a + b + delta <= ‖h - v‖ := by
      have hcross := hu.le_add_mul (w - b • e) (z + a • d)
      rw [hwLeft, hzRight] at hcross
      simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hcross
      have hvec :
          (w - b • e) - (z + a • d) = h - v := by
        dsimp [h, v]
        module
      rw [hvec] at hcross
      dsimp [delta]
      linarith
    have hcrossAddNonneg : 0 <= a + b - delta := by
      have hab : 2 * epsilon <= a + b := by linarith
      linarith [show 0 <= dist z w from dist_nonneg]
    have hcrossSubNonneg : 0 <= a + b + delta := by
      have hab : 2 * epsilon <= a + b := by linarith
      linarith [show 0 <= dist z w from dist_nonneg]
    have hcrossAddSq :
        (a + b - delta) ^ 2 <= ‖h + v‖ ^ 2 :=
      (sq_le_sq₀ hcrossAddNonneg (norm_nonneg _)).2 hcrossAdd
    have hcrossSubSq :
        (a + b + delta) ^ 2 <= ‖h - v‖ ^ 2 :=
      (sq_le_sq₀ hcrossSubNonneg (norm_nonneg _)).2 hcrossSub
    have hparHV := parallelogram_law_with_norm Real h v
    have henergy :
        (a + b) ^ 2 + delta ^ 2 <= ‖h‖ ^ 2 + ‖v‖ ^ 2 := by
      nlinarith [add_le_add hcrossAddSq hcrossSubSq]
    have hvNormSq :
        ‖v‖ ^ 2 =
          a ^ 2 + 2 * a * b * inner Real d e + b ^ 2 := by
      dsimp [v]
      rw [norm_add_sq_real, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos haPos,
        abs_of_pos hbPos, real_inner_smul_left, real_inner_smul_right,
        hd, he]
      ring
    have hdeNormSq :
        ‖d - e‖ ^ 2 = 2 - 2 * inner Real d e := by
      rw [norm_sub_sq_real, hd, he]
      ring
    have habMain :
        a * b * ‖d - e‖ ^ 2 <= ‖h‖ ^ 2 := by
      nlinarith [sq_nonneg delta]
    have hepsilonMul : epsilon ^ 2 <= a * b := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    have hmainSq :
        epsilon ^ 2 * ‖d - e‖ ^ 2 <= ‖h‖ ^ 2 := by
      have hnormSqNonneg : 0 <= ‖d - e‖ ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr hepsilonMul) hnormSqNonneg]
    have hmul :
        epsilon * ‖d - e‖ <= ‖h‖ := by
      apply
        (sq_le_sq₀
          (mul_nonneg hepsilon.le (norm_nonneg _))
          (norm_nonneg _)).mp
      simpa [mul_pow] using hmainSq
    rw [dist_eq_norm, dist_eq_norm, inv_mul_eq_div,
      le_div_iff₀ hepsilon]
    simpa [h, mul_comm, norm_sub_rev] using hmul

/-- A centered subinterval of a contact segment gives exact symmetric
contact equalities around its center. -/
theorem distanceContactLineMapSymmetricSupport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {x y : E} (hxy : (x, y) ∈ distanceContactSet u)
    (hne : x ≠ y)
    {t q : Real} (hq : 0 < q) (ht : q <= t ∧ t <= 1 - q) :
    let z := AffineMap.lineMap x y t
    let d := rayDirection x y
    let a := q * dist x y
    ‖d‖ = 1 ∧
      0 < a ∧
      u (z - a • d) = u z + a ∧
      u (z + a • d) = u z - a := by
  let z := AffineMap.lineMap x y t
  let d := rayDirection x y
  let a := q * dist x y
  have hdistPos : 0 < dist x y := dist_pos.mpr hne
  have haPos : 0 < a := mul_pos hq hdistPos
  have hdNorm : ‖d‖ = 1 := by
    exact NormedSpace.norm_normalize (sub_ne_zero.mpr hne.symm)
  have htLower : 0 <= t - q := sub_nonneg.mpr ht.1
  have htUpper : t + q <= 1 := by linarith
  have htNonneg : 0 <= t := le_trans hq.le ht.1
  have htLe : t <= 1 := by linarith
  have hleftMem :
      AffineMap.lineMap x y (t - q) ∈ segment Real x y :=
    lineMap_mem_segment (𝕜 := Real) x y ⟨htLower, by linarith⟩
  have hzMem : z ∈ segment Real x y :=
    lineMap_mem_segment (𝕜 := Real) x y ⟨htNonneg, htLe⟩
  have hrightMem :
      AffineMap.lineMap x y (t + q) ∈ segment Real x y :=
    lineMap_mem_segment (𝕜 := Real) x y ⟨by linarith, htUpper⟩
  have hleftContact :=
    (distanceContactSegmentSaturation u hu hxy hleftMem).1
  have hzLeftContact :=
    (distanceContactSegmentSaturation u hu hxy hzMem).1
  have hzRightContact :=
    (distanceContactSegmentSaturation u hu hxy hzMem).2
  have hrightContact :=
    (distanceContactSegmentSaturation u hu hxy hrightMem).2
  have hscale :
      a • d = q • (y - x) := by
    dsimp [a, d, rayDirection]
    rw [mul_smul, dist_eq_norm',
      NormedSpace.norm_smul_normalize]
  have hleftPoint :
      z - a • d = AffineMap.lineMap x y (t - q) := by
    dsimp [z]
    rw [hscale, AffineMap.lineMap_apply_module',
      AffineMap.lineMap_apply_module']
    module
  have hrightPoint :
      z + a • d = AffineMap.lineMap x y (t + q) := by
    dsimp [z]
    rw [hscale, AffineMap.lineMap_apply_module',
      AffineMap.lineMap_apply_module']
    module
  have hdistLeft :
      dist x z = t * dist x y := by
    dsimp [z]
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg htNonneg]
  have hdistEarlier :
      dist x (AffineMap.lineMap x y (t - q)) =
        (t - q) * dist x y := by
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg htLower]
  have hdistRight :
      dist z y = (1 - t) * dist x y := by
    dsimp [z]
    rw [dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr htLe)]
  have hdistLater :
      dist (AffineMap.lineMap x y (t + q)) y =
        (1 - (t + q)) * dist x y := by
    rw [dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr htUpper)]
  change dist x (AffineMap.lineMap x y (t - q)) =
    u x - u (AffineMap.lineMap x y (t - q)) at hleftContact
  change dist x z = u x - u z at hzLeftContact
  change dist z y = u z - u y at hzRightContact
  change dist (AffineMap.lineMap x y (t + q)) y =
    u (AffineMap.lineMap x y (t + q)) - u y at hrightContact
  refine ⟨hdNorm, haPos, ?_, ?_⟩
  · rw [hleftPoint]
    nlinarith
  · rw [hrightPoint]
    nlinarith

/-- Reciprocal scales used to keep segment centers and endpoints uniformly
apart. -/
def contactCoreScale (k : Nat) : Real :=
  1 / ((k : Real) + 1)

theorem contactCoreScale_pos (k : Nat) :
    0 < contactCoreScale k := by
  exact one_div_pos.mpr (by positivity)

theorem contactCoreScale_antitone :
    Antitone contactCoreScale := by
  intro i j hij
  apply one_div_le_one_div_of_le
    (show 0 < (i : Real) + 1 by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

/-- The image of the part of a compact endpoint family having a fixed
minimum segment length and a fixed relative distance from both endpoints. -/
def contactSegmentCore
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (K : Set (E × E)) (lengthIndex centerIndex : Nat) : Set E :=
  let evaluation : (E × E) × Real -> E :=
    fun q => AffineMap.lineMap q.1.1 q.1.2 q.2
  evaluation ''
    ((K ∩ {p | contactCoreScale lengthIndex <= dist p.1 p.2}) ×ˢ
      Icc (contactCoreScale centerIndex) (1 - contactCoreScale centerIndex))

theorem contactSegmentCore_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {K : Set (E × E)} (hK : IsCompact K)
    (lengthIndex centerIndex : Nat) :
    IsCompact (contactSegmentCore K lengthIndex centerIndex) := by
  let evaluation : (E × E) × Real -> E :=
    fun q => AffineMap.lineMap q.1.1 q.1.2 q.2
  have hLengthClosed :
      IsClosed {p : E × E |
        contactCoreScale lengthIndex <= dist p.1 p.2} := by
    exact isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have hDomainCompact :
      IsCompact
        ((K ∩ {p : E × E |
            contactCoreScale lengthIndex <= dist p.1 p.2}) ×ˢ
          Icc (contactCoreScale centerIndex)
            (1 - contactCoreScale centerIndex)) :=
    (hK.inter_right hLengthClosed).prod isCompact_Icc
  exact hDomainCompact.image (by fun_prop)

/-- Increasing finite unions of segment cores associated to a compact
exhaustion of the endpoint relation. -/
def contactCompactPiece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (K : Nat -> Set (E × E)) (k : Nat) : Set E :=
  ⋃ endpointIndex ∈ Iic k,
    ⋃ lengthIndex ∈ Iic k,
      ⋃ centerIndex ∈ Iic k,
        contactSegmentCore (K endpointIndex) lengthIndex centerIndex

theorem contactCompactPiece_monotone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (K : Nat -> Set (E × E)) :
    Monotone (contactCompactPiece K) := by
  intro k l hkl z hz
  simp only [contactCompactPiece, mem_iUnion, mem_Iic] at hz ⊢
  obtain ⟨i, hi, j, hj, m, hm, hz⟩ := hz
  exact ⟨i, hi.trans hkl, j, hj.trans hkl, m, hm.trans hkl, hz⟩

theorem contactCompactPiece_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {K : Nat -> Set (E × E)}
    (hK : ∀ i, IsCompact (K i)) (k : Nat) :
    IsCompact (contactCompactPiece K k) := by
  simpa only [contactCompactPiece] using
    (Set.finite_le_nat k).isCompact_biUnion fun i _ =>
      (Set.finite_le_nat k).isCompact_biUnion fun j _ =>
        (Set.finite_le_nat k).isCompact_biUnion fun m _ =>
          contactSegmentCore_isCompact (hK i) j m

theorem iUnion_contactCompactPiece_eq_transportSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)} {K : Nat -> Set (E × E)}
    (hKCover : (⋃ i, K i) = Gamma) :
    (⋃ k, contactCompactPiece K k) = transportSet Gamma := by
  ext z
  constructor
  · intro hz
    rw [mem_iUnion] at hz
    obtain ⟨k, hk⟩ := hz
    simp only [contactCompactPiece, mem_iUnion, mem_Iic] at hk
    obtain ⟨i, hi, j, hj, m, hm, hzCore⟩ := hk
    rcases hzCore with ⟨⟨p, t⟩, ⟨⟨hpK, hpLength⟩, ht⟩, rfl⟩
    have hpGamma : p ∈ Gamma := by
      rw [← hKCover]
      exact mem_iUnion.2 ⟨i, hpK⟩
    have hdistPos : 0 < dist p.1 p.2 :=
      (contactCoreScale_pos j).trans_le hpLength
    have hpNe : p.1 ≠ p.2 := dist_pos.mp hdistPos
    have htOpen : t ∈ Ioo (0 : Real) 1 := by
      exact
        ⟨(contactCoreScale_pos m).trans_le ht.1,
          ht.2.trans_lt (sub_lt_self 1 (contactCoreScale_pos m))⟩
    exact
      ⟨p, hpGamma, hpNe,
        lineMap_mem_openSegment (𝕜 := Real) p.1 p.2 htOpen⟩
  · rintro ⟨p, hpGamma, hpNe, hzSegment⟩
    rw [openSegment_eq_image_lineMap] at hzSegment
    obtain ⟨t, ht, rfl⟩ := hzSegment
    have hpUnion : p ∈ ⋃ i, K i := by
      rw [hKCover]
      exact hpGamma
    obtain ⟨i, hpK⟩ := mem_iUnion.1 hpUnion
    have hdistPos : 0 < dist p.1 p.2 := dist_pos.mpr hpNe
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hdistPos
    have hjLength : contactCoreScale j <= dist p.1 p.2 := by
      exact (by simpa only [contactCoreScale] using hj.le)
    have htMargin : 0 < min t (1 - t) := by
      exact lt_min ht.1 (sub_pos.mpr ht.2)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt htMargin
    have hmScale : contactCoreScale m <= min t (1 - t) := by
      exact (by simpa only [contactCoreScale] using hm.le)
    have htCore :
        t ∈ Icc (contactCoreScale m) (1 - contactCoreScale m) := by
      exact
        ⟨hmScale.trans (min_le_left t (1 - t)),
          by linarith [hmScale.trans (min_le_right t (1 - t))]⟩
    let k := max i (max j m)
    rw [mem_iUnion]
    refine ⟨k, ?_⟩
    simp only [contactCompactPiece, mem_iUnion, mem_Iic]
    refine ⟨i, le_max_left _ _, j, ?_, m, ?_, ?_⟩
    · exact (le_max_left j m).trans (le_max_right i (max j m))
    · exact (le_max_right j m).trans (le_max_right i (max j m))
    · exact ⟨(p, t), ⟨⟨hpK, hjLength⟩, htCore⟩, rfl⟩

theorem contactSegmentCore_direction_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {Gamma : Set (E × E)}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hContact : Gamma ⊆ distanceContactSet u)
    (directionField : E -> E)
    (hDirectionAgrees :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y)
    {K : Set (E × E)} (hKGamma : K ⊆ Gamma)
    {lengthIndex centerIndex : Nat} {z : E}
    (hz : z ∈ contactSegmentCore K lengthIndex centerIndex) :
    ∃ a : Real,
      contactCoreScale centerIndex * contactCoreScale lengthIndex <= a ∧
      ‖directionField z‖ = 1 ∧
      u (z - a • directionField z) = u z + a ∧
      u (z + a • directionField z) = u z - a := by
  rcases hz with ⟨⟨p, t⟩, ⟨⟨hpK, hpLength⟩, ht⟩, rfl⟩
  have hpGamma : p ∈ Gamma := hKGamma hpK
  have hdistPos : 0 < dist p.1 p.2 :=
    (contactCoreScale_pos lengthIndex).trans_le hpLength
  have hpNe : p.1 ≠ p.2 := dist_pos.mp hdistPos
  have htOpen : t ∈ Ioo (0 : Real) 1 := by
    exact
      ⟨(contactCoreScale_pos centerIndex).trans_le ht.1,
        ht.2.trans_lt
          (sub_lt_self 1 (contactCoreScale_pos centerIndex))⟩
  have hzTransport :
      AffineMap.lineMap p.1 p.2 t ∈ transportSet Gamma :=
    ⟨p, hpGamma, hpNe,
      lineMap_mem_openSegment (𝕜 := Real) p.1 p.2 htOpen⟩
  have hDirection :
      directionField (AffineMap.lineMap p.1 p.2 t) =
        rayDirection p.1 p.2 :=
    hDirectionAgrees _ hzTransport p.1 p.2 hpGamma
      (lineMap_mem_openSegment (𝕜 := Real) p.1 p.2 htOpen)
  have hSupport :=
    distanceContactLineMapSymmetricSupport
      u hu (hContact hpGamma) hpNe
      (contactCoreScale_pos centerIndex) ht
  let a := contactCoreScale centerIndex * dist p.1 p.2
  have haLower :
      contactCoreScale centerIndex * contactCoreScale lengthIndex <= a := by
    exact mul_le_mul_of_nonneg_left hpLength
      (contactCoreScale_pos centerIndex).le
  refine ⟨a, haLower, ?_, ?_, ?_⟩
  · simpa only [hDirection] using hSupport.1
  · simpa only [a, hDirection] using hSupport.2.2.1
  · simpa only [a, hDirection] using hSupport.2.2.2

theorem contactCompactPiece_direction_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {Gamma : Set (E × E)}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hContact : Gamma ⊆ distanceContactSet u)
    (directionField : E -> E)
    (hDirectionAgrees :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y)
    {K : Nat -> Set (E × E)}
    (hKGamma : ∀ i, K i ⊆ Gamma)
    (k : Nat) :
    ∃ L : NNReal,
      LipschitzOnWith L directionField (contactCompactPiece K k) := by
  let epsilon := contactCoreScale k * contactCoreScale k
  have hepsilon : 0 < epsilon :=
    mul_pos (contactCoreScale_pos k) (contactCoreScale_pos k)
  let L : NNReal := Real.toNNReal epsilon⁻¹
  refine ⟨L, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro z hz w hw
  simp only [contactCompactPiece, mem_iUnion, mem_Iic] at hz hw
  obtain ⟨i, hi, j, hj, m, hm, hzCore⟩ := hz
  obtain ⟨i', hi', j', hj', m', hm', hwCore⟩ := hw
  obtain ⟨a, haCore, hzaNorm, hzaLeft, hzaRight⟩ :=
    contactSegmentCore_direction_support
      u hu hContact directionField hDirectionAgrees
      (hKGamma i) hzCore
  obtain ⟨b, hbCore, hwbNorm, hwbLeft, hwbRight⟩ :=
    contactSegmentCore_direction_support
      u hu hContact directionField hDirectionAgrees
      (hKGamma i') hwCore
  have haScale :
      epsilon <=
        contactCoreScale m * contactCoreScale j := by
    dsimp [epsilon]
    exact mul_le_mul
      (contactCoreScale_antitone hm)
      (contactCoreScale_antitone hj)
      (contactCoreScale_pos k).le
      (contactCoreScale_pos m).le
  have hbScale :
      epsilon <=
        contactCoreScale m' * contactCoreScale j' := by
    dsimp [epsilon]
    exact mul_le_mul
      (contactCoreScale_antitone hm')
      (contactCoreScale_antitone hj')
      (contactCoreScale_pos k).le
      (contactCoreScale_pos m').le
  have hdist :=
    contactUnitDirectionDist_le_of_radii
      u hu hepsilon (haScale.trans haCore) (hbScale.trans hbCore)
      hzaNorm hwbNorm hzaLeft hzaRight hwbLeft hwbRight
  change dist (directionField z) (directionField w) <=
    (L : Real) * dist z w
  rw [Real.coe_toNNReal epsilon⁻¹ (inv_nonneg.mpr hepsilon.le)]
  exact hdist

/-- A sigma-compact distance-contact relation has an increasing compact
exhaustion of its whole open transport set on which any agreeing direction
field is Lipschitz. No exceptional set is needed. -/
theorem existsContactDirectionCompactExhaustion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {Gamma : Set (E × E)}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hSigma : IsSigmaCompact Gamma)
    (hContact : Gamma ⊆ distanceContactSet u)
    (directionField : E -> E)
    (hDirectionAgrees :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y) :
    ∃ compactPiece : Nat -> Set E,
      Monotone compactPiece ∧
      (∀ k, IsCompact (compactPiece k)) ∧
      (⋃ k, compactPiece k) = transportSet Gamma ∧
      ∀ k, ∃ L : NNReal,
        LipschitzOnWith L directionField (compactPiece k) := by
  obtain ⟨K, hKCompact, hKCover⟩ := hSigma
  have hKGamma : ∀ i, K i ⊆ Gamma := by
    intro i p hp
    rw [← hKCover]
    exact mem_iUnion.2 ⟨i, hp⟩
  refine
    ⟨contactCompactPiece K,
      contactCompactPiece_monotone K,
      contactCompactPiece_isCompact hKCompact,
      iUnion_contactCompactPiece_eq_transportSet hKCover,
      ?_⟩
  intro k
  exact
    contactCompactPiece_direction_lipschitz
      u hu hContact directionField hDirectionAgrees hKGamma k

end

end ConcaveOTLimit
