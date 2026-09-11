import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Theorems.Thm_ConcaveOTLimit_sInfLipschitzFamily
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialTouchUniqueness
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Support

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ConcaveOTLimit

/-- The radial cost normalized to vanish on the diagonal. -/
def strictConcaveProfileRadialIncrement
    (profile : Real -> Real) (r : Real) : Real :=
  profile r - profile 0

/-- A bounded outer annulus of target points. The upper cutoff makes the
profile locally Lipschitz on one compact interval uniformly in the target. -/
def strictConcaveProfileContactOuterTargets {n : Nat}
    (a : Euclidean n) (r R : Real) : Set (Euclidean n) :=
  {y | r <= dist a y ∧ dist a y <= R}

/-- The source ball paired with a bounded outer target annulus. -/
def strictConcaveProfileContactInnerBall {n : Nat}
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  Metric.ball a (r / 2)

/-- The localized infimum of translates of a normalized radial profile. -/
def strictConcaveProfileContactEnvelope {n : Nat}
    (profile : Real -> Real) (u : Euclidean n -> Real)
    (a : Euclidean n) (r R : Real) (x : Euclidean n) : Real :=
  sInf
    (Set.range fun
      y : strictConcaveProfileContactOuterTargets a r R =>
        u y + strictConcaveProfileRadialIncrement profile (dist x y))

theorem exists_lipschitzOnWith_strictConcaveProfile_Icc
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile)
    {d M : Real} (hd : 0 < d) :
    ∃ K : NNReal, LipschitzOnWith K profile (Icc d M) := by
  have hLocal : LocallyLipschitzOn (Ioi (0 : Real)) profile := by
    simpa only [interior_Ici] using
      hConcave.locallyLipschitzOn_interior
  have hSubset : Icc d M ⊆ Ioi (0 : Real) := by
    intro t ht
    exact hd.trans_le ht.1
  exact
    (hLocal.mono hSubset).exists_lipschitzOnWith_of_compact
      isCompact_Icc

theorem strictConcaveProfilePotential_le_add
    {n : Nat} {profile : Real -> Real}
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    (x y : Euclidean n) :
    u x <=
      u y + strictConcaveProfileRadialIncrement profile (dist x y) := by
  have hSub :
      u x - u y <=
        strictConcaveProfileRadialIncrement profile (dist x y) := by
    calc
      u x - u y <= |u x - u y| := le_abs_self _
      _ = dist (u x) (u y) := by rw [Real.dist_eq]
      _ <= strictConcaveProfileRadialIncrement profile (dist x y) :=
        hu x y
  linarith

theorem strictConcaveProfileContactEnvelope_values_bddBelow
    {n : Nat} {profile : Real -> Real}
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    (a : Euclidean n) (r R : Real) (x : Euclidean n) :
    BddBelow
      (Set.range fun
        y : strictConcaveProfileContactOuterTargets a r R =>
          u y +
            strictConcaveProfileRadialIncrement profile (dist x y)) := by
  refine ⟨u x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact strictConcaveProfilePotential_le_add hu x y

theorem lipschitzOnWith_strictConcaveProfileCost_of_outerTarget
    {n : Nat} {profile : Real -> Real}
    {a y : Euclidean n} {r R : Real}
    (hy : y ∈ strictConcaveProfileContactOuterTargets a r R)
    (K : NNReal)
    (hProfile :
      LipschitzOnWith K profile (Icc (r / 2) (R + r / 2))) :
    LipschitzOnWith K
      (fun x : Euclidean n =>
        strictConcaveProfileRadialIncrement profile (dist x y))
      (strictConcaveProfileContactInnerBall a r) := by
  have hDistanceBounds
      {x : Euclidean n}
      (hx : x ∈ strictConcaveProfileContactInnerBall a r) :
      dist x y ∈ Icc (r / 2) (R + r / 2) := by
    have hxa : dist x a < r / 2 := by
      simpa only [strictConcaveProfileContactInnerBall,
        Metric.mem_ball] using hx
    have hLower : r / 2 <= dist x y := by
      have hTriangle : dist a y <= dist a x + dist x y :=
        dist_triangle a x y
      rw [dist_comm a x] at hTriangle
      linarith [hy.1]
    have hUpper : dist x y <= R + r / 2 := by
      have hTriangle : dist x y <= dist x a + dist a y :=
        dist_triangle x a y
      linarith [hy.2]
    exact ⟨hLower, hUpper⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx x' hx'
  calc
    dist
        (strictConcaveProfileRadialIncrement profile (dist x y))
        (strictConcaveProfileRadialIncrement profile (dist x' y)) =
        dist (profile (dist x y)) (profile (dist x' y)) := by
          simp only [strictConcaveProfileRadialIncrement,
            dist_sub_right]
    _ <= (K : Real) * dist (dist x y) (dist x' y) :=
      hProfile.dist_le_mul
        (dist x y) (hDistanceBounds hx)
        (dist x' y) (hDistanceBounds hx')
    _ <= (K : Real) * dist x x' := by
      exact mul_le_mul_of_nonneg_left
        (dist_dist_dist_le_left x x' y) K.property

/-- Each bounded localized contact envelope is Lipschitz on its inner ball. -/
theorem exists_lipschitzOnWith_strictConcaveProfileContactEnvelope
    {n : Nat} {profile : Real -> Real}
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    {r R : Real} (hr : 0 < r) (a : Euclidean n)
    (hOuter :
      (strictConcaveProfileContactOuterTargets a r R).Nonempty) :
    ∃ K : NNReal,
      LipschitzOnWith K
        (strictConcaveProfileContactEnvelope profile u a r R)
        (strictConcaveProfileContactInnerBall a r) := by
  obtain ⟨K, hProfile⟩ :=
    exists_lipschitzOnWith_strictConcaveProfile_Icc
      hStrict.concaveOn (half_pos hr)
      (M := R + r / 2)
  let Outer := strictConcaveProfileContactOuterTargets a r R
  letI : Nonempty Outer := hOuter.to_subtype
  let f : Outer -> Euclidean n -> Real :=
    fun y x =>
      u y + strictConcaveProfileRadialIncrement profile (dist x y)
  have hLipschitz (y : Outer) :
      LipschitzOnWith K (f y)
        (strictConcaveProfileContactInnerBall a r) := by
    have hCost :=
      lipschitzOnWith_strictConcaveProfileCost_of_outerTarget
        y.property K hProfile
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx x' hx'
    simpa only [f, dist_add_left] using
      hCost.dist_le_mul x hx x' hx'
  have hBounded
      (x : Euclidean n)
      (_hx : x ∈ strictConcaveProfileContactInnerBall a r) :
      BddBelow (Set.range fun y : Outer => f y x) := by
    simpa only [Outer, f] using
      strictConcaveProfileContactEnvelope_values_bddBelow
        hu a r R x
  refine ⟨K, ?_⟩
  simpa only [strictConcaveProfileContactEnvelope, Outer, f] using
    lipschitzOnWith_sInf_range
      K f (strictConcaveProfileContactInnerBall a r)
        hLipschitz hBounded

theorem strictConcaveProfileContactEnvelope_le_cost
    {n : Nat} {profile : Real -> Real}
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    {a x y : Euclidean n} {r R : Real}
    (hy : y ∈ strictConcaveProfileContactOuterTargets a r R) :
    strictConcaveProfileContactEnvelope profile u a r R x <=
      u y + strictConcaveProfileRadialIncrement profile (dist x y) := by
  apply csInf_le
    (strictConcaveProfileContactEnvelope_values_bddBelow
      hu a r R x)
  exact ⟨⟨y, hy⟩, rfl⟩

theorem strictConcaveProfileContactEnvelope_eq_of_contact
    {n : Nat} {profile : Real -> Real}
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    {a x y : Euclidean n} {r R : Real}
    (hy : y ∈ strictConcaveProfileContactOuterTargets a r R)
    (hContact :
      strictConcaveProfileRadialIncrement profile (dist x y) =
        u x - u y) :
    strictConcaveProfileContactEnvelope profile u a r R x = u x := by
  apply le_antisymm
  · calc
      strictConcaveProfileContactEnvelope profile u a r R x <=
          u y +
            strictConcaveProfileRadialIncrement profile (dist x y) :=
        strictConcaveProfileContactEnvelope_le_cost hu hy
      _ = u x := by linarith
  · apply le_csInf
    · exact
        ⟨u y + strictConcaveProfileRadialIncrement profile (dist x y),
          ⟨⟨y, hy⟩, rfl⟩⟩
    · rintro _ ⟨z, rfl⟩
      exact strictConcaveProfilePotential_le_add hu x z

/-- On an absolutely continuous source, the off-diagonal fibers of an
oriented contact relation for a monotone strictly concave radial profile are
unique almost everywhere. -/
theorem strictConcaveProfileContact_sourceAeUniqueFiber
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    {u : Euclidean n -> Real}
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hOffDiagonal : ∀ z ∈ Gamma, z.1 ≠ z.2)
    (hContact :
      ∀ z ∈ Gamma,
        strictConcaveProfileRadialIncrement profile (dist z.1 z.2) =
          u z.1 - u z.2) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      ∀ y y', (x, y) ∈ Gamma -> (x, y') ∈ Gamma -> y = y' := by
  let center : Nat -> Euclidean n :=
    TopologicalSpace.denseSeq (Euclidean n)
  let radius : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  let outerBound : Nat -> Real := fun l => (l : Real)
  have hRadiusPos (k : Nat) : 0 < radius k := by
    dsimp only [radius]
    positivity
  have hDiffAE (m k l : Nat) :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)),
        x ∈ strictConcaveProfileContactInnerBall
            (center m) (radius k) ->
        (strictConcaveProfileContactOuterTargets
            (center m) (radius k) (outerBound l)).Nonempty ->
        DifferentiableAt Real
          (strictConcaveProfileContactEnvelope
            profile u (center m) (radius k) (outerBound l)) x := by
    by_cases hOuter :
        (strictConcaveProfileContactOuterTargets
          (center m) (radius k) (outerBound l)).Nonempty
    · obtain ⟨K, hLip⟩ :=
        exists_lipschitzOnWith_strictConcaveProfileContactEnvelope
          hStrict hu (hRadiusPos k) (center m) hOuter
      filter_upwards
        [hLip.ae_differentiableWithinAt_of_mem_of_real]
        with x hx
      intro hxInner _hOuter
      apply (hx hxInner).differentiableAt
      exact Metric.isOpen_ball.mem_nhds hxInner
    · filter_upwards [] with x
      intro _hxInner hOuter'
      exact (hOuter hOuter').elim
  have hDiffAllVolume :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)),
        ∀ m k l,
          x ∈ strictConcaveProfileContactInnerBall
              (center m) (radius k) ->
          (strictConcaveProfileContactOuterTargets
              (center m) (radius k) (outerBound l)).Nonempty ->
          DifferentiableAt Real
            (strictConcaveProfileContactEnvelope
              profile u (center m) (radius k) (outerBound l)) x := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    exact hDiffAE m k
  have hDiffAll :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ m k l,
          x ∈ strictConcaveProfileContactInnerBall
              (center m) (radius k) ->
          (strictConcaveProfileContactOuterTargets
              (center m) (radius k) (outerBound l)).Nonempty ->
          DifferentiableAt Real
            (strictConcaveProfileContactEnvelope
              profile u (center m) (radius k) (outerBound l)) x :=
    hmuAC.ae_le hDiffAllVolume
  filter_upwards [hDiffAll] with x hx
  intro y y' hxy hxy'
  have hxyNe : x ≠ y := hOffDiagonal (x, y) hxy
  have hxyNe' : x ≠ y' := hOffDiagonal (x, y') hxy'
  let d : Real := min (dist x y) (dist x y')
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (dist_pos.mpr hxyNe) (dist_pos.mpr hxyNe')
  obtain ⟨k, hk⟩ :=
    exists_nat_one_div_lt (show 0 < d / 4 by positivity)
  have hk' : radius k < d / 4 := by
    simpa only [radius, Nat.cast_add, Nat.cast_one] using hk
  obtain ⟨m, hm⟩ :=
    Metric.denseRange_iff.mp
      (TopologicalSpace.denseRange_denseSeq (Euclidean n))
      x (radius k / 4) (by positivity)
  have hm' : dist x (center m) < radius k / 4 := by
    simpa only [center, dist_comm] using hm
  have hxInner :
      x ∈ strictConcaveProfileContactInnerBall
          (center m) (radius k) := by
    change dist x (center m) < radius k / 2
    linarith [hRadiusPos k]
  have hyLower : radius k <= dist (center m) y := by
    have hTriangle :
        dist x y <= dist x (center m) + dist (center m) y :=
      dist_triangle x (center m) y
    have hdle : d <= dist x y := min_le_left _ _
    linarith
  have hyLower' : radius k <= dist (center m) y' := by
    have hTriangle :
        dist x y' <= dist x (center m) + dist (center m) y' :=
      dist_triangle x (center m) y'
    have hdle : d <= dist x y' := min_le_right _ _
    linarith
  obtain ⟨l, hl⟩ :=
    exists_nat_gt
      (max (dist (center m) y) (dist (center m) y'))
  have hyUpper : dist (center m) y <= outerBound l := by
    dsimp only [outerBound]
    exact (le_max_left _ _).trans hl.le
  have hyUpper' : dist (center m) y' <= outerBound l := by
    dsimp only [outerBound]
    exact (le_max_right _ _).trans hl.le
  have hyOuter :
      y ∈ strictConcaveProfileContactOuterTargets
          (center m) (radius k) (outerBound l) :=
    ⟨hyLower, hyUpper⟩
  have hyOuter' :
      y' ∈ strictConcaveProfileContactOuterTargets
          (center m) (radius k) (outerBound l) :=
    ⟨hyLower', hyUpper'⟩
  have hOuter :
      (strictConcaveProfileContactOuterTargets
        (center m) (radius k) (outerBound l)).Nonempty :=
    ⟨y, hyOuter⟩
  let envelope : Euclidean n -> Real :=
    strictConcaveProfileContactEnvelope
      profile u (center m) (radius k) (outerBound l)
  have hDiff : DifferentiableAt Real envelope x :=
    hx m k l hxInner hOuter
  apply
    strictConcaveRadialUpperTouches_target_unique_of_differentiableAt
      (profile := profile) (v := envelope)
      (c := u y - profile 0) (c' := u y' - profile 0)
      hMono hStrict hDiff hxyNe hxyNe'
  · intro z
    have hLe :=
      strictConcaveProfileContactEnvelope_le_cost
        (x := z) hu hyOuter
    dsimp only [envelope,
      strictConcaveProfileRadialIncrement] at hLe ⊢
    linarith
  · have hEq :=
      strictConcaveProfileContactEnvelope_eq_of_contact
        hu hyOuter (hContact (x, y) hxy)
    have hContact' := hContact (x, y) hxy
    dsimp only [envelope,
      strictConcaveProfileRadialIncrement] at hEq ⊢
    dsimp only [strictConcaveProfileRadialIncrement] at hContact'
    rw [hEq]
    linarith
  · intro z
    have hLe :=
      strictConcaveProfileContactEnvelope_le_cost
        (x := z) hu hyOuter'
    dsimp only [envelope,
      strictConcaveProfileRadialIncrement] at hLe ⊢
    linarith
  · have hEq :=
      strictConcaveProfileContactEnvelope_eq_of_contact
        hu hyOuter' (hContact (x, y') hxy')
    have hContact' := hContact (x, y') hxy'
    dsimp only [envelope,
      strictConcaveProfileRadialIncrement] at hEq ⊢
    dsimp only [strictConcaveProfileRadialIncrement] at hContact'
    rw [hEq]
    linarith

/-- A coupling supported on an oriented off-diagonal contact relation for a
monotone strictly concave radial profile is induced by a measurable map when
its source is absolutely continuous. -/
theorem existsGraphPlan_of_strictConcaveProfileContactPotential
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    {profile : Real -> Real}
    (hMono : MonotoneOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (gamma : FiniteCoupling mu nu)
    (hOffDiagonal :
      ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)), z.1 ≠ z.2)
    (u : Euclidean n -> Real)
    (hu :
      ∀ x y,
        dist (u x) (u y) <=
          strictConcaveProfileRadialIncrement profile (dist x y))
    (hContact :
      ∀ z ∈ Measure.support
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)),
        strictConcaveProfileRadialIncrement profile (dist z.1 z.2) =
          u z.1 - u z.2) :
    ∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T := by
  let Gamma : Set (Euclidean n × Euclidean n) :=
    {z |
      z ∈ Measure.support
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)) ∧
        z.1 ≠ z.2}
  have hSupported : IsSupported gamma Gamma := by
    filter_upwards
      [(Measure.support_mem_ae :
        ∀ᵐ z ∂(gamma.plan :
          Measure (Euclidean n × Euclidean n)),
          z ∈ Measure.support
            (gamma.plan :
              Measure (Euclidean n × Euclidean n))),
        hOffDiagonal]
      with z hz hne
    exact ⟨hz, hne⟩
  have hUnique :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ y y', (x, y) ∈ Gamma -> (x, y') ∈ Gamma -> y = y' := by
    apply
      strictConcaveProfileContact_sourceAeUniqueFiber
        hMono hStrict hmuAC hu Gamma
    · intro z hz
      exact hz.2
    · intro z hz
      exact hContact z hz.1
  exact
    existsGraphPlanOfSupportedSourceAeUniqueFiber_polish
      gamma Gamma hSupported hUnique

end ConcaveOTLimit
