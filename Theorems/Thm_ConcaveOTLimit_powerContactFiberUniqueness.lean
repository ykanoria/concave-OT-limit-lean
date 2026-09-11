import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Theorems.Thm_ConcaveOTLimit_radialRpowGradientInjective
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Support

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace ConcaveOTLimit

/-- Exact operator norm of the derivative of powered distance away from the
diagonal. -/
theorem norm_fderiv_dist_rpow_left
    {n : Nat} {p : Real} (hp : 0 < p)
    {x y : Euclidean n} (hxy : x ≠ y) :
    ‖fderiv Real (fun z : Euclidean n => dist z y ^ p) x‖ =
      p * dist x y ^ (p - 1) := by
  rw [(hasFDerivAt_dist_rpow_left_of_ne p hxy).fderiv,
    norm_smul, norm_mul, innerSL_apply_norm]
  have hd : 0 < dist x y := dist_pos.mpr hxy
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos hp, abs_of_pos (Real.rpow_pos_of_pos hd _),
    dist_eq_norm]
  calc
    p * ‖x - y‖ ^ (p - 2) * ‖x - y‖ =
        p * (‖x - y‖ ^ (p - 2) * ‖x - y‖) := by ring
    _ = p * ‖x - y‖ ^ ((p - 2) + 1) := by
      rw [Real.rpow_add_one
        (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).ne']
    _ = p * ‖x - y‖ ^ (p - 1) := by ring_nf

/-- The twist map of the strictly concave power cost is injective away from
the diagonal. -/
theorem fderiv_dist_rpow_left_injective_target
    {n : Nat} {p : Real} (hp : 0 < p) (hp1 : p < 1)
    {x y y' : Euclidean n} (hxy : x ≠ y) (hxy' : x ≠ y')
    (hderiv :
      fderiv Real (fun z : Euclidean n => dist z y ^ p) x =
        fderiv Real (fun z : Euclidean n => dist z y' ^ p) x) :
    y = y' := by
  rw [(hasFDerivAt_dist_rpow_left_of_ne p hxy).fderiv,
    (hasFDerivAt_dist_rpow_left_of_ne p hxy').fderiv] at hderiv
  have hinner :
      dist x y ^ (p - 2) • innerSL Real (x - y) =
        dist x y' ^ (p - 2) • innerSL Real (x - y') := by
    apply smul_right_injective _ hp.ne'
    simpa only [mul_smul] using hderiv
  have hgradient :
      ‖x - y‖ ^ (p - 2) • (x - y) =
        ‖x - y'‖ ^ (p - 2) • (x - y') := by
    apply (innerSL_inj (𝕜 := Real)).mp
    simpa only [map_smul, dist_eq_norm] using hinner
  exact radialRpowGradientAtSource_injective
    (by linarith : p ≠ 1) hxy.symm hxy'.symm hgradient

/-- The outer target region used to localize the powered contact envelope. -/
def powerContactOuterTargets {n : Nat}
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  {y | r <= dist a y}

/-- The source ball on which targets in `powerContactOuterTargets a r` stay
uniformly away from the singularity of the power cost. -/
def powerContactInnerBall {n : Nat}
    (a : Euclidean n) (r : Real) : Set (Euclidean n) :=
  Metric.ball a (r / 2)

/-- The localized lower envelope of powered distance functions. -/
def powerContactEnvelope {n : Nat}
    (u : Euclidean n -> Real) (p : Real)
    (a : Euclidean n) (r : Real) (x : Euclidean n) : Real :=
  sInf
    ((fun y : Euclidean n => u y + dist x y ^ p) ''
      powerContactOuterTargets a r)

theorem powerHolder_le_add
    {n : Nat} {u : Euclidean n -> Real} {p : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    (x y : Euclidean n) :
    u x <= u y + dist x y ^ p := by
  have hsub : u x - u y <= dist x y ^ p := by
    calc
      u x - u y <= |u x - u y| := le_abs_self _
      _ = dist (u x) (u y) := by rw [Real.dist_eq]
      _ <= dist x y ^ p := hu x y
  linarith

private theorem powerContactEnvelope_values_bddBelow
    {n : Nat} {u : Euclidean n -> Real} {p : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    (a : Euclidean n) (r : Real) (x : Euclidean n) :
    BddBelow
      ((fun y : Euclidean n => u y + dist x y ^ p) ''
        powerContactOuterTargets a r) := by
  refine ⟨u x, ?_⟩
  rintro _ ⟨y, _hy, rfl⟩
  exact powerHolder_le_add hu x y

/-- Powered distance to an outer target has a Lipschitz constant uniform over
the concentric inner source ball. -/
theorem lipschitzOnWith_dist_rpow_of_outerTarget
    {n : Nat} {p r : Real} (hp : 0 < p) (hp1 : p < 1)
    (hr : 0 < r) {a y : Euclidean n}
    (hy : y ∈ powerContactOuterTargets a r) :
    LipschitzOnWith
      ⟨p * (r / 2) ^ (p - 1), by positivity⟩
      (fun x : Euclidean n => dist x y ^ p)
      (powerContactInnerBall a r) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := Real)
  · intro x hx
    have hxy : x ≠ y := by
      intro hEq
      subst y
      have hx' : dist a x < r / 2 := by
        simpa [powerContactInnerBall, Metric.mem_ball, dist_comm] using hx
      change r <= dist a x at hy
      linarith
    exact (hasFDerivAt_dist_rpow_left_of_ne p hxy).differentiableAt
  · intro x hx
    have hx' : dist a x < r / 2 := by
      simpa [powerContactInnerBall, Metric.mem_ball, dist_comm] using hx
    have hLower : r / 2 < dist x y := by
      change r <= dist a y at hy
      have htri : dist a y <= dist a x + dist x y :=
        dist_triangle a x y
      linarith
    have hxy : x ≠ y :=
      dist_ne_zero.mp (ne_of_gt (by linarith : 0 < dist x y))
    have hpow :
        dist x y ^ (p - 1) <= (r / 2) ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hLower.le (by linarith)
    apply NNReal.coe_le_coe.mp
    simp only [coe_nnnorm]
    rw [norm_fderiv_dist_rpow_left hp hxy]
    exact mul_le_mul_of_nonneg_left hpow hp.le
  · exact convex_ball a (r / 2)

/-- The localized powered contact envelope is Lipschitz on its inner ball. -/
theorem lipschitzOnWith_powerContactEnvelope
    {n : Nat} {u : Euclidean n -> Real} {p r : Real}
    (hp : 0 < p) (hp1 : p < 1) (hr : 0 < r)
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    (a : Euclidean n)
    (hOuter : (powerContactOuterTargets a r).Nonempty) :
    LipschitzOnWith
      ⟨p * (r / 2) ^ (p - 1), by positivity⟩
      (powerContactEnvelope u p a r)
      (powerContactInnerBall a r) := by
  let C : NNReal := ⟨p * (r / 2) ^ (p - 1), by positivity⟩
  let F : Euclidean n -> Set Real := fun x =>
    (fun y : Euclidean n => u y + dist x y ^ p) ''
      powerContactOuterTargets a r
  have hFNonempty (x : Euclidean n) : (F x).Nonempty :=
    hOuter.image _
  have hFBdd (x : Euclidean n) : BddBelow (F x) :=
    powerContactEnvelope_values_bddBelow hu a r x
  have hCost (y : Euclidean n)
      (hy : y ∈ powerContactOuterTargets a r) :
      LipschitzOnWith C
        (fun x : Euclidean n => dist x y ^ p)
        (powerContactInnerBall a r) := by
    exact lipschitzOnWith_dist_rpow_of_outerTarget hp hp1 hr hy
  apply LipschitzOnWith.of_le_add_mul C
  intro x hx x' hx'
  change sInf (F x) <= sInf (F x') + C * dist x x'
  apply (csInf_le_iff (hFBdd x) (hFNonempty x)).2
  intro b hb
  have hLower :
      b - C * dist x x' <= sInf (F x') := by
    apply le_csInf (hFNonempty x')
    intro q hq
    rcases hq with ⟨y, hy, rfl⟩
    have hbCost :
        b <= u y + dist x y ^ p :=
      hb ⟨y, hy, rfl⟩
    have hLip :=
      (hCost y hy).le_add_mul hx hx'
    linarith
  linarith

/-- At a localized contact, the envelope agrees with the original
potential. -/
theorem powerContactEnvelope_eq_of_contact
    {n : Nat} {u : Euclidean n -> Real} {p r : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    {a x y : Euclidean n}
    (hy : y ∈ powerContactOuterTargets a r)
    (hContact : dist x y ^ p = u x - u y) :
    powerContactEnvelope u p a r x = u x := by
  apply le_antisymm
  · apply csInf_le
      (powerContactEnvelope_values_bddBelow hu a r x)
    exact ⟨y, hy, by linarith⟩
  · apply le_csInf
    · exact ⟨u y + dist x y ^ p, ⟨y, hy, rfl⟩⟩
    · rintro _ ⟨z, _hz, rfl⟩
      exact powerHolder_le_add hu x z

/-- Differentiability of one localized envelope identifies the derivative of
every contact cost represented in that envelope. -/
theorem fderiv_powerContactEnvelope_eq_contactCost
    {n : Nat} {u : Euclidean n -> Real} {p r : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    {a x y : Euclidean n}
    (hy : y ∈ powerContactOuterTargets a r)
    (hxy : x ≠ y)
    (hContact : dist x y ^ p = u x - u y)
    (hDiff : DifferentiableAt Real
      (powerContactEnvelope u p a r) x) :
    fderiv Real (powerContactEnvelope u p a r) x =
      fderiv Real (fun z : Euclidean n => dist z y ^ p) x := by
  have hEnvelopeAt :
      powerContactEnvelope u p a r x = u x :=
    powerContactEnvelope_eq_of_contact hu hy hContact
  have hEnvelopeLe (z : Euclidean n) :
      powerContactEnvelope u p a r z <= u y + dist z y ^ p := by
    apply csInf_le
      (powerContactEnvelope_values_bddBelow hu a r z)
    exact ⟨y, hy, rfl⟩
  let g : Euclidean n -> Real := fun z =>
    powerContactEnvelope u p a r z - (u y + dist z y ^ p)
  have hMax : IsLocalMax g x := by
    apply Filter.Eventually.of_forall
    intro z
    dsimp only [g]
    have hz := hEnvelopeLe z
    rw [hEnvelopeAt]
    linarith
  have hCostDeriv :=
    hasFDerivAt_dist_rpow_left_of_ne p hxy
  have hGDeriv :
      HasFDerivAt g
        (fderiv Real (powerContactEnvelope u p a r) x -
          (0 + fderiv Real
            (fun z : Euclidean n => dist z y ^ p) x)) x := by
    apply hDiff.hasFDerivAt.sub
    simpa only [hCostDeriv.fderiv] using
      (hasFDerivAt_const (x := x) (c := u y)).add
        hCostDeriv
  have hzero := hMax.hasFDerivAt_eq_zero hGDeriv
  simpa only [zero_add, sub_eq_zero] using hzero

/-- On an absolutely continuous source, non-diagonal fibers of an oriented
powered contact relation are unique almost everywhere. The countable
localization uses a dense sequence of centers and reciprocal radii. -/
theorem powerContact_sourceAeUniqueFiber
    {n : Nat} {mu : FiniteMeasure (Euclidean n)}
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    {u : Euclidean n -> Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hOffDiagonal : ∀ z ∈ Gamma, z.1 ≠ z.2)
    (hContact :
      ∀ z ∈ Gamma, dist z.1 z.2 ^ p = u z.1 - u z.2) :
    ∀ᵐ x ∂(mu : Measure (Euclidean n)),
      ∀ y y', (x, y) ∈ Gamma -> (x, y') ∈ Gamma -> y = y' := by
  let center : Nat -> Euclidean n :=
    TopologicalSpace.denseSeq (Euclidean n)
  let radius : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hRadiusPos (k : Nat) : 0 < radius k := by
    dsimp only [radius]
    positivity
  have hDiffAE (m k : Nat) :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)),
        x ∈ powerContactInnerBall (center m) (radius k) ->
        (powerContactOuterTargets (center m) (radius k)).Nonempty ->
        DifferentiableAt Real
          (powerContactEnvelope u p (center m) (radius k)) x := by
    by_cases hOuter :
        (powerContactOuterTargets (center m) (radius k)).Nonempty
    · have hLip :=
        lipschitzOnWith_powerContactEnvelope
          hp hp1 (hRadiusPos k) hu (center m) hOuter
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
        ∀ m k,
          x ∈ powerContactInnerBall (center m) (radius k) ->
          (powerContactOuterTargets (center m) (radius k)).Nonempty ->
          DifferentiableAt Real
            (powerContactEnvelope u p (center m) (radius k)) x := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    exact hDiffAE m
  have hDiffAll :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ m k,
          x ∈ powerContactInnerBall (center m) (radius k) ->
          (powerContactOuterTargets (center m) (radius k)).Nonempty ->
          DifferentiableAt Real
            (powerContactEnvelope u p (center m) (radius k)) x :=
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
      x ∈ powerContactInnerBall (center m) (radius k) := by
    change dist x (center m) < radius k / 2
    linarith [hRadiusPos k]
  have hyOuter :
      y ∈ powerContactOuterTargets (center m) (radius k) := by
    change radius k <= dist (center m) y
    have htri :
        dist x y <= dist x (center m) + dist (center m) y :=
      dist_triangle x (center m) y
    have hdle : d <= dist x y := min_le_left _ _
    linarith
  have hyOuter' :
      y' ∈ powerContactOuterTargets (center m) (radius k) := by
    change radius k <= dist (center m) y'
    have htri :
        dist x y' <= dist x (center m) + dist (center m) y' :=
      dist_triangle x (center m) y'
    have hdle : d <= dist x y' := min_le_right _ _
    linarith
  have hOuter :
      (powerContactOuterTargets (center m) (radius k)).Nonempty :=
    ⟨y, hyOuter⟩
  have hDiff :
      DifferentiableAt Real
        (powerContactEnvelope u p (center m) (radius k)) x :=
    hx m k hxInner hOuter
  have hDeriv :=
    fderiv_powerContactEnvelope_eq_contactCost
      hu hyOuter hxyNe (hContact (x, y) hxy) hDiff
  have hDeriv' :=
    fderiv_powerContactEnvelope_eq_contactCost
      hu hyOuter' hxyNe' (hContact (x, y') hxy') hDiff
  exact
    fderiv_dist_rpow_left_injective_target
      hp hp1 hxyNe hxyNe' (hDeriv.symm.trans hDeriv')

/-- A coupling carried by the oriented contact set of a snowflake-Lipschitz
potential is a graph plan as soon as its source is absolutely continuous and
the coupling gives no mass to the diagonal. -/
theorem existsGraphPlan_of_powerContactPotential
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (gamma : FiniteCoupling mu nu)
    (hOffDiagonal :
      ∀ᵐ z ∂(gamma.plan :
        Measure (Euclidean n × Euclidean n)), z.1 ≠ z.2)
    (u : Euclidean n -> Real)
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    (hContact :
      ∀ z ∈ Measure.support
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)),
        dist z.1 z.2 ^ p = u z.1 - u z.2) :
    ∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T := by
  let Gamma : Set (Euclidean n × Euclidean n) :=
    {z | z ∈ Measure.support
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)) ∧ z.1 ≠ z.2}
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
    apply powerContact_sourceAeUniqueFiber hp hp1 hmuAC hu Gamma
    · intro z hz
      exact hz.2
    · intro z hz
      exact hContact z hz.1
  exact
    existsGraphPlanOfSupportedSourceAeUniqueFiber_polish
      gamma Gamma hSupported hUnique

end ConcaveOTLimit
