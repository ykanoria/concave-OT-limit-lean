import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue

open Set
open ConcaveOTLimit

private def rayParameters {n : Nat} (R : OrientedOpenRay n) : Set Real :=
  {t | R.lower < (t : EReal) /\ (t : EReal) < R.upper}

private theorem rayParameters_ordConnected {n : Nat}
    (R : OrientedOpenRay n) :
    (rayParameters R).OrdConnected := by
  change (Real.toEReal ⁻¹' Ioo R.lower R.upper).OrdConnected
  exact
    ordConnected_Ioo.preimage_mono EReal.coe_strictMono.monotone

private theorem ray_dist_point_point {n : Nat}
    (R : OrientedOpenRay n) (s t : Real) :
    dist (R.point s) (R.point t) = dist s t := by
  have hnorm : ‖R.direction‖ = 1 := R.property.1
  rw [dist_eq_norm, Real.dist_eq]
  simp only [OrientedOpenRay.point, add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs]

private theorem ray_point_injective {n : Nat}
    (R : OrientedOpenRay n) :
    Function.Injective R.point := by
  intro s t hst
  apply dist_eq_zero.mp
  rw [← ray_dist_point_point R, hst, dist_self]

private theorem rayParameter_mem_of_point_mem_carrier {n : Nat}
    (R : OrientedOpenRay n) {t : Real}
    (ht : R.point t ∈ R.carrier) :
    t ∈ rayParameters R := by
  obtain ⟨s, hslow, hsup, hs⟩ := ht
  have hst : s = t := ray_point_injective R hs
  subst s
  exact ⟨hslow, hsup⟩

private theorem coveredBy_rayParameters {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (R : OrientedOpenRay n) (hcovered : R.CoveredBy Gamma) :
    ∀ t, t ∈ rayParameters R ->
      ∃ a b : Real, a < t /\ t < b /\
        (R.point a, R.point b) ∈ Gamma := by
  intro t ht
  have hpoint : R.point t ∈ R.carrier :=
    ⟨t, ht.1, ht.2, rfl⟩
  obtain ⟨x, y, hxy, hne, hmid, hdir⟩ :=
    hcovered (R.point t) hpoint
  rw [openSegment_eq_image_lineMap] at hmid
  obtain ⟨c, hc, hcpoint⟩ := hmid
  have hnorm : 0 < ‖y - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hdir' :
      NormedSpace.normalize (y - x) = R.direction := by
    simpa only [rayDirection] using hdir
  have hdiff : y - x = ‖y - x‖ • R.direction := by
    calc
      y - x = ‖y - x‖ • NormedSpace.normalize (y - x) :=
        (NormedSpace.norm_smul_normalize (y - x)).symm
      _ = ‖y - x‖ • R.direction := congrArg _ hdir'
  have hcenter :
      R.point t = x + (c * ‖y - x‖) • R.direction := by
    calc
      R.point t = AffineMap.lineMap x y c := hcpoint.symm
      _ = c • (y - x) + x := AffineMap.lineMap_apply_module' x y c
      _ = c • (‖y - x‖ • R.direction) + x :=
        congrArg (fun v => c • v + x) hdiff
      _ = x + (c * ‖y - x‖) • R.direction := by
        rw [smul_smul]
        abel
  let a : Real := t - c * ‖y - x‖
  let b : Real := t + (1 - c) * ‖y - x‖
  have ha : R.point a = x := by
    calc
      R.point a =
          R.point t - (c * ‖y - x‖) • R.direction := by
        dsimp [a, OrientedOpenRay.point]
        module
      _ = x := by
        rw [hcenter]
        module
  have hb : R.point b = y := by
    calc
      R.point b =
          R.point t + ((1 - c) * ‖y - x‖) • R.direction := by
        dsimp [b, OrientedOpenRay.point]
        module
      _ = x + ‖y - x‖ • R.direction := by
        rw [hcenter]
        module
      _ = y := by
        rw [← hdiff]
        abel
  have hat : a < t := by
    dsimp [a]
    exact sub_lt_self t (mul_pos hc.1 hnorm)
  have htb : t < b := by
    dsimp [b]
    exact lt_add_of_pos_right t (mul_pos (sub_pos.mpr hc.2) hnorm)
  exact ⟨a, b, hat, htb, by simpa only [ha, hb] using hxy⟩

private theorem correctedPotential_eq_left {n : Nat}
    (R : OrientedOpenRay n)
    {u : Euclidean n -> Real} (hu : LipschitzWith 1 u)
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : Gamma ⊆ distanceContactSet u)
    {a b t : Real} (hat : a < t) (htb : t < b)
    (hab : (R.point a, R.point b) ∈ Gamma) :
    u (R.point t) + t = u (R.point a) + a := by
  have hcontact := hGamma hab
  have hleft : u (R.point a) - u (R.point t) <=
      dist (R.point a) (R.point t) := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul (R.point a) (R.point t)
  have hright : u (R.point t) - u (R.point b) <=
      dist (R.point t) (R.point b) := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul (R.point t) (R.point b)
  change dist (R.point a) (R.point b) =
    u (R.point a) - u (R.point b) at hcontact
  rw [ray_dist_point_point R, Real.dist_eq,
    abs_of_neg (sub_neg.mpr hat)] at hleft
  rw [ray_dist_point_point R, Real.dist_eq,
    abs_of_neg (sub_neg.mpr htb)] at hright
  rw [ray_dist_point_point R, Real.dist_eq,
    abs_of_neg (sub_neg.mpr (hat.trans htb))] at hcontact
  linarith

private theorem correctedPotential_isLocallyConstant {n : Nat}
    (R : OrientedOpenRay n)
    {u : Euclidean n -> Real} (hu : LipschitzWith 1 u)
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : Gamma ⊆ distanceContactSet u)
    (hcovered : R.CoveredBy Gamma) :
    IsLocallyConstant
      (fun t : rayParameters R => u (R.point t.1) + t.1) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro t
  obtain ⟨a, b, hat, htb, hab⟩ :=
    coveredBy_rayParameters R hcovered t.1 t.2
  let U : Set (rayParameters R) := Subtype.val ⁻¹' Ioo a b
  refine ⟨U, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.isOpen_preimage _ isOpen_Ioo
  · exact ⟨hat, htb⟩
  · intro s hs
    exact
      (correctedPotential_eq_left R hu hGamma hs.1 hs.2 hab).trans
        (correctedPotential_eq_left R hu hGamma hat htb hab).symm

theorem solution
    {n : Nat}
    (u : Euclidean n -> Real) (hu : LipschitzWith 1 u)
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGamma : Gamma ⊆ distanceContactSet u)
    (R : OrientedOpenRay n) (hcovered : R.CoveredBy Gamma)
    {x y : Euclidean n}
    (hx : x ∈ R.carrier) (hy : y ∈ R.carrier)
    (hxy : OrientedBefore R x y) :
    u x - u y = dist x y := by
  obtain ⟨s, t, hst, hsx, hty⟩ := hxy
  subst x
  subst y
  have hs : s ∈ rayParameters R :=
    rayParameter_mem_of_point_mem_carrier R hx
  have ht : t ∈ rayParameters R :=
    rayParameter_mem_of_point_mem_carrier R hy
  letI : PreconnectedSpace (rayParameters R) :=
    Subtype.preconnectedSpace
      (rayParameters_ordConnected R).isPreconnected
  have hconstant :
      u (R.point s) + s = u (R.point t) + t :=
    IsLocallyConstant.apply_eq_of_preconnectedSpace
      (correctedPotential_isLocallyConstant R hu hGamma hcovered)
      ⟨s, hs⟩ ⟨t, ht⟩
  rw [ray_dist_point_point R, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst)]
  linarith
