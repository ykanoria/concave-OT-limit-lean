import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.Linarith

open Set
open ConcaveOTLimit

private theorem normalize_eq_of_sameRay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {v w : E} (h : SameRay Real v w) (hv : v ≠ 0) (hw : w ≠ 0) :
    NormedSpace.normalize v = NormedSpace.normalize w := by
  simpa [NormedSpace.normalize] using h.inv_norm_smul_eq hv hw

private theorem direction_eq_first_cross
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y x' y' z : E}
    (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hzxy : z ∈ segment Real x y)
    (hzxy' : z ∈ segment Real x' y')
    (hcross : Wbtw Real x z y')
    (hzx : z ≠ x) (hzy' : z ≠ y') :
    rayDirection x y = rayDirection x' y' := by
  have hfirst : Wbtw Real x z y := mem_segment_iff_wbtw.mp hzxy
  have hsecond : Wbtw Real x' z y' := mem_segment_iff_wbtw.mp hzxy'
  have hn_zx : z - x ≠ 0 := sub_ne_zero.mpr hzx
  have hn_yz' : y' - z ≠ 0 := sub_ne_zero.mpr hzy'.symm
  have hn_yx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hn_yx' : y' - x' ≠ 0 := sub_ne_zero.mpr hxy'.symm
  have h1 :
      NormedSpace.normalize (z - x) = NormedSpace.normalize (y - x) :=
    normalize_eq_of_sameRay hfirst.sameRay_vsub_left hn_zx hn_yx
  have h2 :
      NormedSpace.normalize (z - x) = NormedSpace.normalize (y' - z) :=
    normalize_eq_of_sameRay hcross.sameRay_vsub hn_zx hn_yz'
  have h3 :
      NormedSpace.normalize (y' - x') = NormedSpace.normalize (y' - z) :=
    normalize_eq_of_sameRay hsecond.sameRay_vsub_right hn_yx' hn_yz'
  unfold rayDirection
  exact h1.symm.trans (h2.trans h3.symm)

private theorem direction_eq_second_cross
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {x y x' y' z : E}
    (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hzxy : z ∈ segment Real x y)
    (hzxy' : z ∈ segment Real x' y')
    (hcross : Wbtw Real x' z y)
    (hzx' : z ≠ x') (hzy : z ≠ y) :
    rayDirection x y = rayDirection x' y' := by
  have hfirst : Wbtw Real x z y := mem_segment_iff_wbtw.mp hzxy
  have hsecond : Wbtw Real x' z y' := mem_segment_iff_wbtw.mp hzxy'
  have hn_zx' : z - x' ≠ 0 := sub_ne_zero.mpr hzx'
  have hn_yz : y - z ≠ 0 := sub_ne_zero.mpr hzy.symm
  have hn_yx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hn_yx' : y' - x' ≠ 0 := sub_ne_zero.mpr hxy'.symm
  have h1 :
      NormedSpace.normalize (z - x') = NormedSpace.normalize (y' - x') :=
    normalize_eq_of_sameRay hsecond.sameRay_vsub_left hn_zx' hn_yx'
  have h2 :
      NormedSpace.normalize (z - x') = NormedSpace.normalize (y - z) :=
    normalize_eq_of_sameRay hcross.sameRay_vsub hn_zx' hn_yz
  have h3 :
      NormedSpace.normalize (y - x) = NormedSpace.normalize (y - z) :=
    normalize_eq_of_sameRay hfirst.sameRay_vsub_right hn_yx hn_yz
  unfold rayDirection
  exact h3.trans (h2.symm.trans h1)

private theorem contact_directions_eq_of_segments_inter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {x y x' y' z : E}
    (hxy : (x, y) ∈ distanceContactSet u)
    (hxy' : (x', y') ∈ distanceContactSet u)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hzxy : z ∈ segment Real x y)
    (hzxy' : z ∈ segment Real x' y')
    (hleft : x ≠ x') (hright : y ≠ y') :
    rayDirection x y = rayDirection x' y' := by
  have hdiff (a b : E) : u a - u b <= dist a b := by
    apply sub_le_iff_le_add'.2
    simpa using hu.le_add_mul a b
  change dist x y = u x - u y at hxy
  change dist x' y' = u x' - u y' at hxy'
  have hcycle :
      dist x y + dist x' y' <= dist x y' + dist x' y := by
    linarith [hdiff x y', hdiff x' y]
  have hseg := dist_add_dist_of_mem_segment hzxy
  have hseg' := dist_add_dist_of_mem_segment hzxy'
  have htri : dist x y' <= dist x z + dist z y' := dist_triangle x z y'
  have htri' : dist x' y <= dist x' z + dist z y := dist_triangle x' z y
  have hcrossSum :
      dist x y' + dist x' y =
        (dist x z + dist z y') + (dist x' z + dist z y) := by
    linarith
  have hcross : dist x z + dist z y' = dist x y' := by
    linarith
  have hcross' : dist x' z + dist z y = dist x' y := by
    linarith
  have hw : Wbtw Real x z y' := dist_add_dist_eq_iff.mp hcross
  have hw' : Wbtw Real x' z y := dist_add_dist_eq_iff.mp hcross'
  by_cases hzx : z = x
  · apply direction_eq_second_cross hne hne' hzxy hzxy' hw'
    · simpa [hzx] using hleft
    · simpa [hzx] using hne
  · by_cases hzy' : z = y'
    · apply direction_eq_second_cross hne hne' hzxy hzxy' hw'
      · simpa [hzy'] using hne'.symm
      · simpa [hzy'] using hright.symm
    · exact direction_eq_first_cross hne hne' hzxy hzxy' hw hzx hzy'

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {Gamma : Set (E × E)}
    (hGamma : Gamma ⊆ distanceContactSet u) :
    NoCrossing Gamma := by
  intro x y x' y' hxyG hxyG' hne hne' hdir hinter
  obtain ⟨z, hz, hz'⟩ := hinter
  by_cases hleft : x = x'
  · exact Or.inl hleft
  by_cases hright : y = y'
  · exact Or.inr hright
  exact False.elim <| hdir <|
    contact_directions_eq_of_segments_inter u hu
      (hGamma hxyG) (hGamma hxyG') hne hne' hz hz' hleft hright
