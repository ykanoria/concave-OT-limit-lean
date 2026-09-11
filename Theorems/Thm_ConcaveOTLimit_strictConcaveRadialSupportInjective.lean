import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Mathlib.Analysis.Convex.Slope
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Separation.Regular

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal Pointwise

noncomputable section

namespace ConcaveOTLimit

/-- Cyclical monotonicity for a real-valued radial profile. -/
def IsRadialProfileCyclicallyMonotone
    {E : Type*} [PseudoMetricSpace E]
    (profile : Real -> Real) (Gamma : Set (E × E)) : Prop :=
  ∀ {m : Nat} (x y : Fin m -> E),
    (∀ i, (x i, y i) ∈ Gamma) ->
      ∀ sigma : Equiv.Perm (Fin m),
        (∑ i, profile (dist (x i) (y i))) <=
          ∑ i, profile (dist (x i) (y (sigma i)))

/-- The two-point consequence of radial profile cyclical monotonicity. -/
theorem IsRadialProfileCyclicallyMonotone.twoCycle
    {E : Type*} [PseudoMetricSpace E]
    {profile : Real -> Real} {Gamma : Set (E × E)}
    (hCyclic : IsRadialProfileCyclicallyMonotone profile Gamma)
    {x y x' y' : E}
    (hxy : (x, y) ∈ Gamma) (hx'y' : (x', y') ∈ Gamma) :
    profile (dist x y) + profile (dist x' y') <=
      profile (dist x y') + profile (dist x' y) := by
  let source : Fin 2 -> E := ![x, x']
  let target : Fin 2 -> E := ![y, y']
  let sigma : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hMem : ∀ i, (source i, target i) ∈ Gamma := by
    intro i
    fin_cases i
    · simpa [source, target] using hxy
    · simpa [source, target] using hx'y'
  simpa [source, target, sigma, Fin.sum_univ_two, add_comm] using
    hCyclic source target hMem sigma

/-- Strict concavity makes equal-length radial increments strictly decrease
when the two intervals are separated. This is the scalar strictness needed
by a local rerouting argument and uses no derivative of the profile. -/
theorem strictConcave_radialIncrement_lt_of_separated
    {profile : Real -> Real}
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    {a b t : Real} (ha : 0 <= a) (ht : 0 < t)
    (hSeparated : a + t < b) :
    profile (b + t) - profile b <
      profile (a + t) - profile a := by
  have hb : 0 <= b := le_trans ha (by linarith)
  have hbt : 0 <= b + t := by linarith
  have hFirst :=
    hStrict.slope_anti_adjacent ha hb
      (by linarith : a < a + t) hSeparated
  have hSecond :=
    hStrict.slope_anti_adjacent
      (by linarith : 0 <= a + t) hbt
      hSeparated (by linarith : b < b + t)
  have hSlope :
      (profile (b + t) - profile b) / ((b + t) - b) <
        (profile (a + t) - profile a) / ((a + t) - a) :=
    hSecond.trans hFirst
  have hSlope' :
      (profile (b + t) - profile b) / t <
        (profile (a + t) - profile a) / t := by
    simpa only [add_sub_cancel_left] using hSlope
  exact (div_lt_div_iff_of_pos_right ht).mp hSlope'

/-- Sources having a target in `V` inside a compact source/target
localization of `Gamma`. -/
def localizedRadialBranchSource
    {E : Type*} [NormedAddCommGroup E]
    (Gamma : Set (E × E)) (V : Set E) (k : Nat) : Set E :=
  Prod.fst ''
    (Gamma ∩
      (closedBall (0 : E) (k : Real) ×ˢ
        (closure V ∩ closedBall (0 : E) (k : Real))))

/-- A compactly localized source set carrying branches into two target
neighborhoods. -/
def localizedRadialTwoBranchSource
    {E : Type*} [NormedAddCommGroup E]
    (Gamma : Set (E × E)) (U V : Set E) (k : Nat) : Set E :=
  localizedRadialBranchSource Gamma U k ∩
    localizedRadialBranchSource Gamma V k

/-- The set of source points with at least two distinct target fibers. -/
def radialBranchingSource
    {E : Type*} (Gamma : Set (E × E)) : Set E :=
  {x | ∃ y y', (x, y) ∈ Gamma ∧ (x, y') ∈ Gamma ∧ y ≠ y'}

theorem localizedRadialBranchSource_isCompact
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {Gamma : Set (E × E)} (hGamma : IsClosed Gamma)
    (V : Set E) (k : Nat) :
    IsCompact (localizedRadialBranchSource Gamma V k) := by
  have hTarget :
      IsCompact
        (closure V ∩ closedBall (0 : E) (k : Real)) :=
    (isCompact_closedBall (0 : E) (k : Real)).inter_left
      isClosed_closure
  have hProduct :
      IsCompact
        (closedBall (0 : E) (k : Real) ×ˢ
          (closure V ∩ closedBall (0 : E) (k : Real))) :=
    (isCompact_closedBall (0 : E) (k : Real)).prod hTarget
  exact
    (hProduct.inter_left hGamma).image continuous_fst

theorem localizedRadialTwoBranchSource_measurable
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {Gamma : Set (E × E)} (hGamma : IsClosed Gamma)
    (U V : Set E) (k : Nat) :
    MeasurableSet (localizedRadialTwoBranchSource Gamma U V k) := by
  exact
    ((localizedRadialBranchSource_isCompact hGamma U k).isClosed.measurableSet).inter
      ((localizedRadialBranchSource_isCompact hGamma V k).isClosed.measurableSet)

/-- Density one at a point, measured using centered closed Euclidean balls. -/
def HasLebesgueDensityOneAt
    {n : Nat} (s : Set (Euclidean n)) (x : Euclidean n) : Prop :=
  Tendsto
    (fun r : Real =>
      volume (s ∩ closedBall x r) / volume (closedBall x r))
    (nhdsWithin 0 (Ioi 0)) (nhds 1)

/-- A density-one source set meets every sufficiently small translated and
rescaled positive-volume test set. This is the device for choosing nearby
branching sources in a prescribed cone without differentiating the cost. -/
theorem HasLebesgueDensityOneAt.eventually_nonempty_inter_smul
    {n : Nat} {s : Set (Euclidean n)} {x : Euclidean n}
    (hDensity : HasLebesgueDensityOneAt s x)
    (t : Set (Euclidean n)) (ht : MeasurableSet t)
    (htPos : volume t ≠ 0) :
    ∀ᶠ r : Real in nhdsWithin 0 (Ioi 0),
      (s ∩ ({x} + r • t)).Nonempty := by
  exact
    Measure.eventually_nonempty_inter_smul_of_density_one
      volume s x hDensity t ht htPos

/-- In particular, a density-one source set has nearby points in every
positive-aperture direction ball. -/
theorem HasLebesgueDensityOneAt.eventually_nonempty_in_direction
    {n : Nat} {s : Set (Euclidean n)} {x : Euclidean n}
    (hDensity : HasLebesgueDensityOneAt s x)
    (direction : Euclidean n) {aperture : Real} (hAperture : 0 < aperture) :
    ∀ᶠ r : Real in nhdsWithin 0 (Ioi 0),
      (s ∩
        ({x} + r • closedBall direction aperture)).Nonempty := by
  apply HasLebesgueDensityOneAt.eventually_nonempty_inter_smul hDensity
    (closedBall direction aperture) measurableSet_closedBall
  exact (Metric.measure_closedBall_pos volume direction hAperture).ne'

/-- A measurable set with no density-one point is volume-null. -/
theorem volume_eq_zero_of_no_densityOne
    {n : Nat} {s : Set (Euclidean n)}
    (hs : MeasurableSet s)
    (hNoDensity : ∀ x ∈ s, ¬HasLebesgueDensityOneAt s x) :
    volume s = 0 := by
  have hDensity :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict s,
        HasLebesgueDensityOneAt s x := by
    simpa only [HasLebesgueDensityOneAt] using
      (Besicovitch.ae_tendsto_measure_inter_div
        (volume : Measure (Euclidean n)) s)
  have hMem :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict s, x ∈ s :=
    ae_restrict_mem hs
  have hFalse :
      ∀ᵐ _x ∂(volume : Measure (Euclidean n)).restrict s, False := by
    filter_upwards [hDensity, hMem] with x hxDensity hxMem
    exact hNoDensity x hxMem hxDensity
  by_contra hNonzero
  letI : NeBot (ae ((volume : Measure (Euclidean n)).restrict s)) :=
    ae_restrict_neBot.mpr hNonzero
  obtain ⟨x, hx⟩ := hFalse.exists
  exact hx

/-- Every branching source is captured by two countably indexed compact
branch localizations whose closed target neighborhoods are disjoint. -/
theorem radialBranchingSource_subset_countable_localizations
    {n : Nat} {Gamma : Set (Euclidean n × Euclidean n)} :
    radialBranchingSource Gamma ⊆
      ⋃ U : TopologicalSpace.countableBasis (Euclidean n),
        ⋃ V : TopologicalSpace.countableBasis (Euclidean n),
          ⋃ (_hUV : Disjoint (closure (U : Set (Euclidean n)))
              (closure (V : Set (Euclidean n)))),
            ⋃ k : Nat, localizedRadialTwoBranchSource Gamma U V k := by
  intro x hx
  rcases hx with ⟨y, y', hxy, hxy', hyy'⟩
  obtain ⟨O, hyO, hOOpen, P, hy'P, hPOpen, hClosure⟩ :=
    exists_open_nhds_disjoint_closure hyy'
  obtain ⟨U, hUBasis, hyU, hUO⟩ :=
    (TopologicalSpace.isBasis_countableBasis (Euclidean n)).exists_subset_of_mem_open
      hyO hOOpen
  obtain ⟨V, hVBasis, hy'V, hVP⟩ :=
    (TopologicalSpace.isBasis_countableBasis (Euclidean n)).exists_subset_of_mem_open
      hy'P hPOpen
  let U' : TopologicalSpace.countableBasis (Euclidean n) := ⟨U, hUBasis⟩
  let V' : TopologicalSpace.countableBasis (Euclidean n) := ⟨V, hVBasis⟩
  have hUV :
      Disjoint (closure (U' : Set (Euclidean n)))
        (closure (V' : Set (Euclidean n))) := by
    exact hClosure.mono (closure_mono hUO) (closure_mono hVP)
  obtain ⟨k, hk⟩ :=
    exists_nat_gt
      (max (dist (0 : Euclidean n) x)
        (max (dist (0 : Euclidean n) y)
          (dist (0 : Euclidean n) y')))
  have hxBall :
      x ∈ closedBall (0 : Euclidean n) (k : Real) := by
    apply mem_closedBall.mpr
    have hxBound :
        dist (0 : Euclidean n) x <=
          max (dist (0 : Euclidean n) x)
            (max (dist (0 : Euclidean n) y)
              (dist (0 : Euclidean n) y')) :=
      le_max_left _ _
    simpa only [dist_comm] using hxBound.trans hk.le
  have hyBall :
      y ∈ closedBall (0 : Euclidean n) (k : Real) := by
    apply mem_closedBall.mpr
    have hyBound :
        dist (0 : Euclidean n) y <=
          max (dist (0 : Euclidean n) x)
            (max (dist (0 : Euclidean n) y)
              (dist (0 : Euclidean n) y')) :=
      (le_max_left _ _).trans (le_max_right _ _)
    simpa only [dist_comm] using hyBound.trans hk.le
  have hy'Ball :
      y' ∈ closedBall (0 : Euclidean n) (k : Real) := by
    apply mem_closedBall.mpr
    have hy'Bound :
        dist (0 : Euclidean n) y' <=
          max (dist (0 : Euclidean n) x)
            (max (dist (0 : Euclidean n) y)
              (dist (0 : Euclidean n) y')) :=
      (le_max_right _ _).trans (le_max_right _ _)
    simpa only [dist_comm] using hy'Bound.trans hk.le
  have hxU :
      x ∈ localizedRadialBranchSource Gamma U' k := by
    refine ⟨(x, y), ?_, rfl⟩
    exact
      ⟨hxy, hxBall, subset_closure hyU, hyBall⟩
  have hxV :
      x ∈ localizedRadialBranchSource Gamma V' k := by
    refine ⟨(x, y'), ?_, rfl⟩
    exact
      ⟨hxy', hxBall, subset_closure hy'V, hy'Ball⟩
  apply mem_iUnion.2
  refine ⟨U', ?_⟩
  apply mem_iUnion.2
  refine ⟨V', ?_⟩
  apply mem_iUnion.2
  refine ⟨hUV, ?_⟩
  apply mem_iUnion.2
  refine ⟨k, ?_⟩
  exact ⟨hxU, hxV⟩

/-- The remaining local geometric statement: strict radial concavity and
two-cycle monotonicity must exclude a density-one point of every compact
two-branch localization. -/
def StrictConcaveRadialDensityReroutingPremise
    {n : Nat} (profile : Real -> Real)
    (Gamma : Set (Euclidean n × Euclidean n)) : Prop :=
  StrictMonoOn profile (Ici 0) ->
    StrictConcaveOn Real (Ici 0) profile ->
    IsRadialProfileCyclicallyMonotone profile Gamma ->
    (∀ z ∈ Gamma, z.1 ≠ z.2) ->
    ∀ (U V : TopologicalSpace.countableBasis (Euclidean n)) (k : Nat),
      Disjoint (closure (U : Set (Euclidean n)))
          (closure (V : Set (Euclidean n))) ->
        ∀ x ∈ localizedRadialTwoBranchSource Gamma U V k,
          ¬HasLebesgueDensityOneAt
            (localizedRadialTwoBranchSource Gamma U V k) x

/-- Purely local form of the remaining geometric blocker. A density point
of two separated target branches must furnish two support pairs whose
crossed rerouting is strictly cheaper, contradicting the support two-cycle
inequality. -/
def StrictConcaveRadialLocalReroutingPremise
    {n : Nat} (profile : Real -> Real)
    (Gamma : Set (Euclidean n × Euclidean n)) : Prop :=
  StrictMonoOn profile (Ici 0) ->
    StrictConcaveOn Real (Ici 0) profile ->
    IsRadialProfileCyclicallyMonotone profile Gamma ->
    (∀ z ∈ Gamma, z.1 ≠ z.2) ->
    ∀ (U V : TopologicalSpace.countableBasis (Euclidean n)) (k : Nat),
      Disjoint (closure (U : Set (Euclidean n)))
          (closure (V : Set (Euclidean n))) ->
        ∀ x ∈ localizedRadialTwoBranchSource Gamma U V k,
          HasLebesgueDensityOneAt
              (localizedRadialTwoBranchSource Gamma U V k) x ->
            ∃ p q : Euclidean n × Euclidean n,
              p ∈ Gamma ∧ q ∈ Gamma ∧
                profile (dist p.1 q.2) + profile (dist q.1 p.2) <
                  profile (dist p.1 p.2) + profile (dist q.1 q.2)

/-- A strict local rerouting violation excludes density points using only
the two-point consequence of cyclic monotonicity. -/
theorem strictConcaveRadialDensityReroutingPremise_of_localRerouting
    {n : Nat} {profile : Real -> Real}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hLocal : StrictConcaveRadialLocalReroutingPremise profile Gamma) :
    StrictConcaveRadialDensityReroutingPremise profile Gamma := by
  intro hIncreasing hStrict hCyclic hOffDiagonal U V k hUV x hx hDensity
  obtain ⟨p, q, hp, hq, hImprove⟩ :=
    hLocal hIncreasing hStrict hCyclic hOffDiagonal
      U V k hUV x hx hDensity
  exact (not_lt_of_ge (hCyclic.twoCycle hp hq)) hImprove

/-- The density/rerouting premise implies that the entire branching source
set is volume-null. -/
theorem radialBranchingSource_volume_zero_of_densityRerouting
    {n : Nat} {profile : Real -> Real}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hGammaClosed : IsClosed Gamma)
    (hIncreasing : StrictMonoOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (hCyclic : IsRadialProfileCyclicallyMonotone profile Gamma)
    (hOffDiagonal : ∀ z ∈ Gamma, z.1 ≠ z.2)
    (hRerouting :
      StrictConcaveRadialDensityReroutingPremise profile Gamma) :
    volume (radialBranchingSource Gamma) = 0 := by
  have hPieceZero
      (U V : TopologicalSpace.countableBasis (Euclidean n))
      (hUV :
        Disjoint (closure (U : Set (Euclidean n)))
          (closure (V : Set (Euclidean n))))
      (k : Nat) :
      volume (localizedRadialTwoBranchSource Gamma U V k) = 0 := by
    apply volume_eq_zero_of_no_densityOne
      (localizedRadialTwoBranchSource_measurable hGammaClosed U V k)
    exact
      hRerouting hIncreasing hStrict hCyclic hOffDiagonal U V k hUV
  have hUnionZero :
      volume
          (⋃ U : TopologicalSpace.countableBasis (Euclidean n),
            ⋃ V : TopologicalSpace.countableBasis (Euclidean n),
              ⋃ (_hUV : Disjoint (closure (U : Set (Euclidean n)))
                  (closure (V : Set (Euclidean n)))),
                ⋃ k : Nat,
                  localizedRadialTwoBranchSource Gamma U V k) = 0 := by
    apply measure_iUnion_null
    intro U
    apply measure_iUnion_null
    intro V
    apply measure_iUnion_null
    intro hUV
    apply measure_iUnion_null
    intro k
    exact hPieceZero U V hUV k
  apply le_antisymm
  · exact
      (measure_mono radialBranchingSource_subset_countable_localizations).trans_eq
        hUnionZero
  · exact bot_le

/-- A closed, cyclically monotone, off-diagonal support satisfying the local
density rerouting exclusion has source-almost-everywhere singleton fibers,
and hence the supported coupling is a graph plan. -/
theorem existsGraphPlan_of_strictConcaveRadialSupport_of_densityRerouting
    (n : Nat)
    {mu nu : FiniteMeasure (Euclidean n)}
    {profile : Real -> Real}
    (gamma : FiniteCoupling mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hGammaClosed : IsClosed Gamma)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hIncreasing : StrictMonoOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (hCyclic : IsRadialProfileCyclicallyMonotone profile Gamma)
    (hOffDiagonal : ∀ z ∈ Gamma, z.1 ≠ z.2)
    (hRerouting :
      StrictConcaveRadialDensityReroutingPremise profile Gamma) :
    ∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T := by
  have hBadVolume : volume (radialBranchingSource Gamma) = 0 :=
    radialBranchingSource_volume_zero_of_densityRerouting
      hGammaClosed hIncreasing hStrict hCyclic hOffDiagonal hRerouting
  have hBadMu :
      (mu : Measure (Euclidean n)) (radialBranchingSource Gamma) = 0 :=
    hmuAC hBadVolume
  have hNotBad :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        x ∉ radialBranchingSource Gamma := by
    rw [ae_iff]
    simpa only [compl_setOf, not_not, setOf_mem_eq] using hBadMu
  have hUnique :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ y y', (x, y) ∈ Gamma -> (x, y') ∈ Gamma -> y = y' := by
    filter_upwards [hNotBad] with x hx
    intro y y' hxy hxy'
    by_contra hyy'
    exact hx ⟨y, y', hxy, hxy', hyy'⟩
  exact
    existsGraphPlanOfSupportedSourceAeUniqueFiber_polish
      gamma Gamma hSupported hUnique

/-- Graphness from the purely local rerouting formulation of the geometric
blocker. -/
theorem existsGraphPlan_of_strictConcaveRadialSupport_of_localRerouting
    (n : Nat)
    {mu nu : FiniteMeasure (Euclidean n)}
    {profile : Real -> Real}
    (gamma : FiniteCoupling mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hGammaClosed : IsClosed Gamma)
    (hSupported : IsSupported gamma Gamma)
    (hmuAC : (mu : Measure (Euclidean n)) ≪ volume)
    (hIncreasing : StrictMonoOn profile (Ici 0))
    (hStrict : StrictConcaveOn Real (Ici 0) profile)
    (hCyclic : IsRadialProfileCyclicallyMonotone profile Gamma)
    (hOffDiagonal : ∀ z ∈ Gamma, z.1 ≠ z.2)
    (hLocal : StrictConcaveRadialLocalReroutingPremise profile Gamma) :
    ∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T := by
  exact
    existsGraphPlan_of_strictConcaveRadialSupport_of_densityRerouting
      n gamma Gamma hGammaClosed hSupported hmuAC
      hIncreasing hStrict hCyclic hOffDiagonal
      (strictConcaveRadialDensityReroutingPremise_of_localRerouting hLocal)

end ConcaveOTLimit
