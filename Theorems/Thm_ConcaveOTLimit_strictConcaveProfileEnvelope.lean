import Theorems.Thm_ConcaveOTLimit_sInfLipschitzFamily
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialSubgradient

open Set
open scoped NNReal

noncomputable section

namespace ConcaveOTLimit

/-- The increment of a radial profile relative to its value at the origin. -/
def concaveProfileRadialIncrement
    (profile : Real -> Real) (r : Real) : Real :=
  profile r - profile 0

/-- Targets outside the localization ball centered at `a`. -/
def concaveProfileEnvelopeOuterTargets {n : Nat}
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  {y | r <= dist a y}

/-- The concentric inner ball on which every outer target stays uniformly
away from the source point. -/
def concaveProfileEnvelopeInnerBall {n : Nat}
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  Metric.ball a (r / 2)

/-- The localized infimum envelope of translates of a radial profile
increment, indexed by targets outside a ball. -/
def strictConcaveProfileEnvelope {n : Nat}
    (profile : Real -> Real) (u : Euclidean n -> Real)
    (a : Euclidean n) (r : Real) (x : Euclidean n) : Real :=
  sInf
    (Set.range fun
      y : concaveProfileEnvelopeOuterTargets a r =>
        u y + concaveProfileRadialIncrement profile (dist x y))

/-- A radial-increment Holder bound gives the one-sided potential
inequality used to bound all envelope values from below. -/
theorem concaveProfilePotential_le_add
    {n : Nat} {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      forall x y,
        dist (u x) (u y) <=
          concaveProfileRadialIncrement profile ‖x - y‖)
    (x y : Euclidean n) :
    u x <=
      u y + concaveProfileRadialIncrement profile (dist x y) := by
  have hSub :
      u x - u y <=
        concaveProfileRadialIncrement profile (dist x y) := by
    calc
      u x - u y <= |u x - u y| := le_abs_self _
      _ = dist (u x) (u y) := by rw [Real.dist_eq]
      _ <= concaveProfileRadialIncrement profile ‖x - y‖ := hu x y
      _ = concaveProfileRadialIncrement profile (dist x y) := by
        rw [dist_eq_norm]
  linarith

/-- The family defining a localized envelope is nonempty whenever its outer
target set is nonempty. -/
theorem strictConcaveProfileEnvelope_values_nonempty
    {n : Nat} {profile : Real -> Real} {u : Euclidean n -> Real}
    {a : Euclidean n} {r : Real}
    (hOuter : (concaveProfileEnvelopeOuterTargets a r).Nonempty)
    (x : Euclidean n) :
    (Set.range fun
      y : concaveProfileEnvelopeOuterTargets a r =>
        u y + concaveProfileRadialIncrement profile (dist x y)).Nonempty := by
  obtain ⟨y, hy⟩ := hOuter
  exact ⟨u y + concaveProfileRadialIncrement profile (dist x y),
    ⟨⟨y, hy⟩, rfl⟩⟩

/-- The family defining a localized envelope is pointwise bounded below by
the original potential. -/
theorem strictConcaveProfileEnvelope_values_bddBelow
    {n : Nat} {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      forall x y,
        dist (u x) (u y) <=
          concaveProfileRadialIncrement profile ‖x - y‖)
    (a : Euclidean n) (r : Real) (x : Euclidean n) :
    BddBelow
      (Set.range fun
        y : concaveProfileEnvelopeOuterTargets a r =>
          u y + concaveProfileRadialIncrement profile (dist x y)) := by
  refine ⟨u x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact concaveProfilePotential_le_add hu x y

/-- The right supergradient at `d / 2` is a Lipschitz constant for an
increasing strictly concave profile on all radii at least `d`. -/
theorem lipschitzOnWith_strictConcaveProfile_Ici
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {d : Real} (hd : 0 < d) :
    LipschitzOnWith
      ⟨concaveProfileRightSupergradient profile (d / 2),
        (concaveProfileRightSupergradient_pos
          hMono hStrict (half_pos hd)).le⟩
      profile (Ici d) := by
  let K : NNReal :=
    ⟨concaveProfileRightSupergradient profile (d / 2),
      (concaveProfileRightSupergradient_pos
        hMono hStrict (half_pos hd)).le⟩
  apply LipschitzOnWith.of_le_add_mul K
  intro a ha b hb
  by_cases hab : a <= b
  · have hProfile : profile a <= profile b :=
      hMono (hd.le.trans ha) (hd.le.trans hb) hab
    exact hProfile.trans
      (le_add_of_nonneg_right (mul_nonneg K.property dist_nonneg))
  · have hba : b < a := lt_of_not_ge hab
    have hbPos : 0 < b := hd.trans_le hb
    have hHalfLtB : d / 2 < b := (half_lt_self hd).trans_le hb
    have hSupergradientLe :
        concaveProfileRightSupergradient profile b <=
          concaveProfileRightSupergradient profile (d / 2) :=
      (concaveProfileRightSupergradient_strictAnti
        hStrict (half_pos hd) hHalfLtB).le
    have hTangent :=
      concaveProfile_le_rightSupergradient_tangent
        hStrict.concaveOn hbPos (hbPos.le.trans hba.le)
    change
      profile a <= profile b +
        concaveProfileRightSupergradient profile (d / 2) * dist a b
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hba)]
    calc
      profile a <=
          profile b +
            concaveProfileRightSupergradient profile b * (a - b) :=
        hTangent
      _ <=
          profile b +
            concaveProfileRightSupergradient profile (d / 2) *
              (a - b) := by
        gcongr

/-- Every radial cost centered at an outer target has the same Lipschitz
constant on the inner source ball. -/
theorem lipschitzOnWith_strictConcaveProfileCost_of_outerTarget
    {n : Nat} {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {r : Real} (hr : 0 < r) {a y : Euclidean n}
    (hy : y ∈ concaveProfileEnvelopeOuterTargets a r) :
    LipschitzOnWith
      ⟨concaveProfileRightSupergradient profile ((r / 2) / 2),
        (concaveProfileRightSupergradient_pos
          hMono hStrict (half_pos (half_pos hr))).le⟩
      (fun x : Euclidean n =>
        concaveProfileRadialIncrement profile (dist x y))
      (concaveProfileEnvelopeInnerBall a r) := by
  let C : NNReal :=
    ⟨concaveProfileRightSupergradient profile ((r / 2) / 2),
      (concaveProfileRightSupergradient_pos
        hMono hStrict (half_pos (half_pos hr))).le⟩
  have hProfile :
      LipschitzOnWith C profile (Ici (r / 2)) := by
    simpa only [C] using
      lipschitzOnWith_strictConcaveProfile_Ici
        hMono hStrict (half_pos hr)
  have hDistanceLower
      {x : Euclidean n}
      (hx : x ∈ concaveProfileEnvelopeInnerBall a r) :
      r / 2 <= dist x y := by
    have hx' : dist x a < r / 2 := by
      simpa only [concaveProfileEnvelopeInnerBall, Metric.mem_ball] using hx
    have hy' : r <= dist a y := hy
    have hTriangle : dist a y <= dist a x + dist x y :=
      dist_triangle a x y
    rw [dist_comm a x] at hTriangle
    linarith
  apply LipschitzOnWith.of_le_add_mul C
  intro x hx x' hx'
  have hOneSided :=
    hProfile.le_add_mul (hDistanceLower hx) (hDistanceLower hx')
  have hDistance :
      dist (dist x y) (dist x' y) <= dist x x' :=
    dist_dist_dist_le_left x x' y
  have hScaledDistance :
      (C : Real) * dist (dist x y) (dist x' y) <=
        (C : Real) * dist x x' :=
    mul_le_mul_of_nonneg_left hDistance C.property
  dsimp only [concaveProfileRadialIncrement]
  linarith

/-- The localized infimum envelope inherits the uniform Lipschitz constant
of its outer-target costs. -/
theorem lipschitzOnWith_strictConcaveProfileEnvelope
    {n : Nat} {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {u : Euclidean n -> Real}
    (hu :
      forall x y,
        dist (u x) (u y) <=
          concaveProfileRadialIncrement profile ‖x - y‖)
    {r : Real} (hr : 0 < r) (a : Euclidean n)
    (hOuter : (concaveProfileEnvelopeOuterTargets a r).Nonempty) :
    LipschitzOnWith
      ⟨concaveProfileRightSupergradient profile ((r / 2) / 2),
        (concaveProfileRightSupergradient_pos
          hMono hStrict (half_pos (half_pos hr))).le⟩
      (strictConcaveProfileEnvelope profile u a r)
      (concaveProfileEnvelopeInnerBall a r) := by
  let C : NNReal :=
    ⟨concaveProfileRightSupergradient profile ((r / 2) / 2),
      (concaveProfileRightSupergradient_pos
        hMono hStrict (half_pos (half_pos hr))).le⟩
  let Outer := concaveProfileEnvelopeOuterTargets a r
  letI : Nonempty Outer := hOuter.to_subtype
  let f : Outer -> Euclidean n -> Real :=
    fun y x => u y + concaveProfileRadialIncrement profile (dist x y)
  have hLipschitz (y : Outer) :
      LipschitzOnWith C (f y)
        (concaveProfileEnvelopeInnerBall a r) := by
    have hCost :=
      lipschitzOnWith_strictConcaveProfileCost_of_outerTarget
        hMono hStrict hr y.property
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx x' hx'
    simpa only [C, f, dist_add_left] using
      hCost.dist_le_mul x hx x' hx'
  have hBounded
      (x : Euclidean n)
      (_hx : x ∈ concaveProfileEnvelopeInnerBall a r) :
      BddBelow (Set.range fun y : Outer => f y x) := by
    simpa only [Outer, f] using
      strictConcaveProfileEnvelope_values_bddBelow hu a r x
  simpa only [strictConcaveProfileEnvelope, Outer, f] using
    lipschitzOnWith_sInf_range
      C f (concaveProfileEnvelopeInnerBall a r) hLipschitz hBounded

/-- Every outer target gives a global upper bound for the localized
envelope. -/
theorem strictConcaveProfileEnvelope_le_outerTarget
    {n : Nat} {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      forall x y,
        dist (u x) (u y) <=
          concaveProfileRadialIncrement profile ‖x - y‖)
    {a y : Euclidean n} {r : Real}
    (hy : y ∈ concaveProfileEnvelopeOuterTargets a r)
    (z : Euclidean n) :
    strictConcaveProfileEnvelope profile u a r z <=
      u y + concaveProfileRadialIncrement profile (dist z y) := by
  apply csInf_le
    (strictConcaveProfileEnvelope_values_bddBelow hu a r z)
  exact ⟨⟨y, hy⟩, rfl⟩

/-- At a contact represented by an outer target, the localized envelope
equals the potential. -/
theorem strictConcaveProfileEnvelope_eq_of_contact
    {n : Nat} {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      forall x y,
        dist (u x) (u y) <=
          concaveProfileRadialIncrement profile ‖x - y‖)
    {a x y : Euclidean n} {r : Real}
    (hy : y ∈ concaveProfileEnvelopeOuterTargets a r)
    (hContact :
      concaveProfileRadialIncrement profile (dist x y) =
        u x - u y) :
    strictConcaveProfileEnvelope profile u a r x = u x := by
  apply le_antisymm
  · have hUpper :=
      strictConcaveProfileEnvelope_le_outerTarget hu hy x
    linarith
  · apply le_csInf
    · exact
        strictConcaveProfileEnvelope_values_nonempty
          ⟨y, hy⟩ x
    · rintro _ ⟨z, rfl⟩
      exact concaveProfilePotential_le_add hu x z

/-- An outer contact target gives an exact global upper touch of the
localized envelope by its translated radial cost. -/
theorem strictConcaveProfileEnvelope_upperTouch_of_contact
    {n : Nat} {profile : Real -> Real} {u : Euclidean n -> Real}
    (hu :
      forall x y,
        dist (u x) (u y) <=
          concaveProfileRadialIncrement profile ‖x - y‖)
    {a x y : Euclidean n} {r : Real}
    (hy : y ∈ concaveProfileEnvelopeOuterTargets a r)
    (hContact :
      concaveProfileRadialIncrement profile (dist x y) =
        u x - u y) :
    (forall z,
      strictConcaveProfileEnvelope profile u a r z <=
        u y + concaveProfileRadialIncrement profile (dist z y)) /\
    strictConcaveProfileEnvelope profile u a r x =
      u y + concaveProfileRadialIncrement profile (dist x y) := by
  constructor
  · exact strictConcaveProfileEnvelope_le_outerTarget hu hy
  · rw [strictConcaveProfileEnvelope_eq_of_contact hu hy hContact]
    linarith

end ConcaveOTLimit
