import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrixMutuallySingular
import Theorems.Thm_ConcaveOTLimit_literalJuilletLevelAlternation
import Theorems.Thm_ConcaveOTLimit_measurablePositiveCrossingDecomposition
import Mathlib.Data.Set.Card.Arithmetic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace ConcaveOTLimit

noncomputable section

private theorem signedCumulative_value_mem_graph
    (mu nu : FiniteMeasure Real) (x : Real) :
    (x, signedCumulative mu nu x) ∈
      generalizedCumulativeGraph mu nu := by
  change
    signedCumulative mu nu x ∈
      uIcc (signedCumulativeLeft mu nu x)
        (signedCumulative mu nu x)
  exact right_mem_uIcc

private theorem exists_right_point_below
    (mu nu : FiniteMeasure Real) {a b h : Real}
    (hab : a < b)
    (ha : signedCumulative mu nu a < h) :
    ∃ x ∈ Ioo a b, signedCumulative mu nu x < h := by
  have hTendsto :
      Tendsto (signedCumulative mu nu)
        (nhdsWithin a (Ioi a))
        (nhds (signedCumulative mu nu a)) :=
    ((signedCumulativeRightContinuousAndLeftLim mu nu).1 a).tendsto.mono_left
      (nhdsWithin_mono a Ioi_subset_Ici_self)
  have hBelow :
      ∀ᶠ x in nhdsWithin a (Ioi a),
        signedCumulative mu nu x < h :=
    hTendsto.eventually_lt_const ha
  have hBeforeAt :
      ∀ᶠ x in nhds a, x < b :=
    Iio_mem_nhds hab
  have hBefore :
      ∀ᶠ x in nhdsWithin a (Ioi a), x < b :=
    hBeforeAt.filter_mono inf_le_left
  have hExists :
      ∀ᶠ x in nhdsWithin a (Ioi a),
        x ∈ Ioi a ∧ x < b ∧ signedCumulative mu nu x < h := by
    filter_upwards [hBelow, hBefore, self_mem_nhdsWithin] with
        x hxBelow hxb hax
    exact ⟨hax, hxb, hxBelow⟩
  rcases hExists.exists with ⟨x, hax, hxb, hxBelow⟩
  exact ⟨x, ⟨hax, hxb⟩, hxBelow⟩

private theorem exists_graph_hit_Ioc
    (mu nu : FiniteMeasure Real) {a b h : Real}
    (hab : a < b)
    (ha : signedCumulative mu nu a < h)
    (hb : h < signedCumulative mu nu b) :
    ∃ x ∈ Ioc a b,
      (x, h) ∈ generalizedCumulativeGraph mu nu := by
  by_contra hNone
  push Not at hNone
  obtain ⟨z, hz, hzBelow⟩ :=
    exists_right_point_below mu nu hab ha
  have hAvoid :
      ∀ x ∈ Ioc a b,
        (x, h) ∉ generalizedCumulativeGraph mu nu := by
    intro x hx hGraph
    exact hNone x hx hGraph
  have hSide :=
    signedCumulative_side_constant_on_preconnected
      mu nu h isPreconnected_Ioc hAvoid
      (show z ∈ Ioc a b from ⟨hz.1, hz.2.le⟩)
      (show b ∈ Ioc a b from ⟨hab, le_rfl⟩)
  exact (not_lt_of_ge hb.le) (hSide.mp hzBelow)

private theorem exists_positive_crossing_Ioc
    (mu nu : FiniteMeasure Real) {a b h : Real}
    (hab : a < b)
    (ha : signedCumulative mu nu a < h)
    (hb : h < signedCumulative mu nu b)
    (hFinite :
      {x : Real |
        (x, h) ∈ generalizedCumulativeGraph mu nu}.Finite)
    (hClassified :
      ∀ x : Real,
        (x, h) ∈ generalizedCumulativeGraph mu nu →
          IsGoodIncreasingCrossing mu nu x h ∨
            IsGoodDecreasingCrossing mu nu x h) :
    ∃ x ∈ Ioc a b,
      IsGoodIncreasingCrossing mu nu x h := by
  let hits : Set Real :=
    {x | x ∈ Ioc a b ∧
      (x, h) ∈ generalizedCumulativeGraph mu nu}
  have hHitsFinite : hits.Finite :=
    hFinite.subset fun x hx => hx.2
  have hHitsNonempty : hits.Nonempty := by
    obtain ⟨x, hx, hGraph⟩ :=
      exists_graph_hit_Ioc mu nu hab ha hb
    exact ⟨x, hx, hGraph⟩
  have hHitsFinsetNonempty :
      hHitsFinite.toFinset.Nonempty :=
    hHitsFinite.toFinset_nonempty.mpr hHitsNonempty
  let x := hHitsFinite.toFinset.min' hHitsFinsetNonempty
  have hxHits : x ∈ hits :=
    hHitsFinite.mem_toFinset.mp
      (Finset.min'_mem _ hHitsFinsetNonempty)
  have hxLeast : ∀ y ∈ hits, x ≤ y := by
    intro y hy
    exact Finset.min'_le _ y
      (hHitsFinite.mem_toFinset.mpr hy)
  rcases hClassified x hxHits.2 with hIncreasing | hDecreasing
  · exact ⟨x, hxHits.1, hIncreasing⟩
  · obtain ⟨_hxGraph, epsilon, hEpsilon, hLocal⟩ := hDecreasing
    have hLower : max a (x - epsilon) < x :=
      max_lt hxHits.1.1 (sub_lt_self x hEpsilon)
    obtain ⟨y, hyLower, hyx⟩ := exists_between hLower
    have hay : a < y :=
      (le_max_left a (x - epsilon)).trans_lt hyLower
    have hxyEpsilon : x - epsilon < y :=
      (le_max_right a (x - epsilon)).trans_lt hyLower
    have hyNear : y ∈ Ioo (x - epsilon) (x + epsilon) :=
      ⟨hxyEpsilon, hyx.trans (lt_add_of_pos_right x hEpsilon)⟩
    have hProduct :=
      hLocal hyNear hyx.ne
        (signedCumulative_value_mem_graph mu nu y)
    have hyAbove : h < signedCumulative mu nu y := by
      rcases mul_neg_iff.mp hProduct with hSigns | hSigns
      · exact sub_pos.mp hSigns.1
      · exact
          ((not_lt_of_ge (sub_nonpos.mpr hyx.le)) hSigns.2).elim
    obtain ⟨z, hz, hzBelow⟩ :=
      exists_right_point_below mu nu hxHits.1.1 ha
    have hAvoid :
        ∀ q ∈ Ioo a x,
          (q, h) ∉ generalizedCumulativeGraph mu nu := by
      intro q hq hqGraph
      have hqHits : q ∈ hits :=
        ⟨⟨hq.1, hq.2.le.trans hxHits.1.2⟩, hqGraph⟩
      exact (not_lt_of_ge (hxLeast q hqHits)) hq.2
    have hSide :=
      signedCumulative_side_constant_on_preconnected
        mu nu h isPreconnected_Ioo hAvoid hz
        (show y ∈ Ioo a x from ⟨hay, hyx⟩)
    exact ((not_lt_of_ge hyAbove.le) (hSide.mp hzBelow)).elim

private theorem ofReal_apply_le_posPart
    (sigma : SignedMeasure Real) {s : Set Real}
    (hs : MeasurableSet s) :
    ENNReal.ofReal (sigma s) ≤
      sigma.toJordanDecomposition.posPart s := by
  have hApply :
      sigma s =
        sigma.toJordanDecomposition.posPart.real s -
          sigma.toJordanDecomposition.negPart.real s := by
    calc
      sigma s =
          sigma.toJordanDecomposition.toSignedMeasure s :=
        congrArg (fun tau : SignedMeasure Real => tau s)
          (SignedMeasure.toSignedMeasure_toJordanDecomposition sigma).symm
      _ = sigma.toJordanDecomposition.posPart.real s -
          sigma.toJordanDecomposition.negPart.real s := by
        rw [JordanDecomposition.toSignedMeasure,
          Measure.toSignedMeasure_sub_apply hs]
  have hLe :
      sigma s ≤ sigma.toJordanDecomposition.posPart.real s := by
    rw [hApply]
    exact sub_le_self _ (measureReal_nonneg)
  calc
    ENNReal.ofReal (sigma s) ≤
        ENNReal.ofReal
          (sigma.toJordanDecomposition.posPart.real s) :=
      ENNReal.ofReal_le_ofReal hLe
    _ = sigma.toJordanDecomposition.posPart s := by
      exact ENNReal.ofReal_toReal
        (measure_ne_top
          sigma.toJordanDecomposition.posPart s)

private theorem exists_measurable_crossing_branch
    {piece : Set (Real × Real)}
    (hPiece : MeasurableSet piece)
    (hInj : InjOn Prod.snd piece) :
    ∃ branch : Real → Real,
      Measurable branch ∧
        ∀ p ∈ piece, branch p.2 = p.1 := by
  by_cases hNonempty : piece.Nonempty
  · letI : StandardBorelSpace piece := hPiece.standardBorel
    let level : piece → Real := fun p => p.1.2
    have hLevelMeasurable : Measurable level :=
      measurable_snd.comp measurable_subtype_coe
    have hLevelInjective : Injective level := by
      intro p q hpq
      apply Subtype.ext
      exact hInj p.2 q.2 hpq
    have hEmbedding : MeasurableEmbedding level :=
      hLevelMeasurable.measurableEmbedding hLevelInjective
    letI : Nonempty piece := hNonempty.to_subtype
    let branch : Real → Real :=
      fun h => (hEmbedding.invFun h).1.1
    refine ⟨branch, ?_, ?_⟩
    · exact measurable_fst.comp
        (measurable_subtype_coe.comp hEmbedding.measurable_invFun)
    · intro p hp
      let q : piece := ⟨p, hp⟩
      have hLeft := hEmbedding.leftInverse_invFun q
      have hFirst := congrArg (fun r : piece => r.1.1) hLeft
      simpa only [branch, level, q] using hFirst
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    intro p hp
    exact (hNonempty ⟨p, hp⟩).elim

private theorem measurable_positiveCrossingFiber_encard
    (mu nu : FiniteMeasure Real) {s : Set Real}
    (hs : MeasurableSet s) :
    Measurable fun h =>
      ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞) := by
  let decomposition :=
    measurablePositiveCrossingDecomposition mu nu
  have hBranchExists :
      ∀ n, ∃ branch : Real → Real,
        Measurable branch ∧
          ∀ p ∈ decomposition.piece n,
            branch p.2 = p.1 := fun n =>
    exists_measurable_crossing_branch
      (decomposition.measurable_piece n)
      (decomposition.snd_injOn n)
  choose crossing hCrossingMeasurable hBranchOnPiece using hBranchExists
  let levelSet : Nat → Set Real :=
    fun n => Prod.snd '' decomposition.piece n
  have hLevelSetMeasurable (n : Nat) :
      MeasurableSet (levelSet n) :=
    (decomposition.measurable_piece n).image_of_measurable_injOn
      measurable_snd (decomposition.snd_injOn n)
  have hBranchMemPiece (n : Nat) {h : Real}
      (hh : h ∈ levelSet n) :
      (crossing n h, h) ∈ decomposition.piece n := by
    rcases hh with ⟨p, hp, rfl⟩
    rw [hBranchOnPiece n p hp]
    exact hp
  have hBranchGood (n : Nat) {h : Real}
      (hh : h ∈ levelSet n) :
      IsGoodIncreasingCrossing mu nu (crossing n h) h := by
    change (crossing n h, h) ∈ positiveCrossingRelation mu nu
    rw [← decomposition.iUnion_piece]
    exact mem_iUnion.2 ⟨n, hBranchMemPiece n hh⟩
  have hBranchBijOn (h : Real) :
      BijOn (fun n => crossing n h)
        {n | h ∈ levelSet n ∧ crossing n h ∈ s}
        (positiveCrossingFiber mu nu s h) := by
    refine BijOn.mk ?_ ?_ ?_
    · intro n hn
      exact ⟨hn.2, hBranchGood n hn.1⟩
    · intro n hn m hm hnm
      by_contra hne
      have hpn := hBranchMemPiece n hn.1
      have hpm := hBranchMemPiece m hm.1
      have hpm' :
          (crossing n h, h) ∈ decomposition.piece m := by
        simpa only [hnm] using hpm
      exact (Set.disjoint_left.1
        (decomposition.pairwise_disjoint hne)) hpn hpm'
    · intro x hx
      have hxUnion :
          (x, h) ∈ ⋃ n, decomposition.piece n := by
        rw [decomposition.iUnion_piece]
        exact hx.2
      rcases mem_iUnion.1 hxUnion with ⟨n, hxn⟩
      have hhLevel : h ∈ levelSet n :=
        ⟨(x, h), hxn, rfl⟩
      have hBranch : crossing n h = x := by
        simpa only using hBranchOnPiece n (x, h) hxn
      exact ⟨n, ⟨hhLevel, hBranch ▸ hx.1⟩, hBranch⟩
  have hFiberCount (h : Real) :
      (∑' n,
          {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
            (fun _ => (1 : ℝ≥0∞)) h) =
        ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞) := by
    let active : Set Nat :=
      {n | h ∈ levelSet n ∧ crossing n h ∈ s}
    have hBij :
        BijOn (fun n => crossing n h) active
          (positiveCrossingFiber mu nu s h) := by
      simpa only [active] using hBranchBijOn h
    calc
      (∑' n,
          {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
            (fun _ => (1 : ℝ≥0∞)) h) =
          ∑' _ : active, (1 : ℝ≥0∞) := by
        symm
        simpa only [active, Set.mem_setOf_eq] using
          (tsum_subtype active (fun _ : Nat => (1 : ℝ≥0∞)))
      _ = (active.encard : ℝ≥0∞) :=
        ENNReal.tsum_set_one active
      _ = ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞) := by
        rw [Set.encard_congr hBij.equiv]
  rw [← funext hFiberCount]
  apply Measurable.tsum
  intro n
  exact measurable_const.indicator
    ((hLevelSetMeasurable n).inter
      (hs.preimage (hCrossingMeasurable n)))

private theorem enat_toENNReal_finset_sum
    {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f : ι → ℕ∞) :
    ((∑ i ∈ t, f i : ℕ∞) : ℝ≥0∞) =
      ∑ i ∈ t, (f i : ℝ≥0∞) := by
  induction t using Finset.induction_on with
  | empty =>
      simp
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi, ENat.toENNReal_add, ih]

/-- Every positive increment across an interval is paid for both by an
increasing completed-graph crossing in that interval (after layer cake) and
by the positive Jordan part of the canonical BV vector measure. -/
theorem positiveIncrement_le_crossingOccupation_and_positivePart_Ioc
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    {a b : Real} (hab : a < b) :
    let increment :=
      ENNReal.ofReal
        (signedCumulative mu nu b - signedCumulative mu nu a)
    increment ≤
        (∫⁻ h,
          ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ℝ≥0∞)
            ∂(volume : Measure Real)) ∧
      increment ≤
        (SignedMeasure.toJordanDecomposition
          (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
            (Ioc a b) := by
  dsimp only
  constructor
  · have hRegular :=
      generalizedCumulativeGraphFiniteAndRegularAe
        mu nu hAtomless
    have hPointwise :
        ∀ᵐ h ∂(volume : Measure Real),
          (Ioo (signedCumulative mu nu a)
              (signedCumulative mu nu b)).indicator
              (fun _ => (1 : ℝ≥0∞)) h ≤
            ((positiveCrossingFiber mu nu (Ioc a b) h).encard :
              ℝ≥0∞) := by
      filter_upwards [hRegular] with h hRegularLevel
      by_cases hh :
          h ∈ Ioo (signedCumulative mu nu a)
            (signedCumulative mu nu b)
      · rw [indicator_of_mem hh]
        obtain ⟨x, hx, hIncreasing⟩ :=
          exists_positive_crossing_Ioc mu nu hab
            hh.1 hh.2 hRegularLevel.1 hRegularLevel.2
        have hNonempty :
            (positiveCrossingFiber mu nu (Ioc a b) h).Nonempty :=
          ⟨x, hx, hIncreasing⟩
        exact_mod_cast
          (Set.one_le_encard_iff_nonempty.mpr hNonempty)
      · rw [Set.indicator_of_notMem hh]
        exact bot_le
    calc
      ENNReal.ofReal
            (signedCumulative mu nu b -
              signedCumulative mu nu a) =
          (volume : Measure Real)
            (Ioo (signedCumulative mu nu a)
              (signedCumulative mu nu b)) := by
        rw [Real.volume_Ioo]
      _ = ∫⁻ h,
          (Ioo (signedCumulative mu nu a)
              (signedCumulative mu nu b)).indicator
              (fun _ => (1 : ℝ≥0∞)) h
          ∂(volume : Measure Real) :=
        (lintegral_indicator_one measurableSet_Ioo).symm
      _ ≤ ∫⁻ h,
          ((positiveCrossingFiber mu nu (Ioc a b) h).encard :
            ℝ≥0∞)
          ∂(volume : Measure Real) :=
        lintegral_mono_ae hPointwise
  · have hVectorMeasure :
        (signedCumulativeBoundedVariation mu nu).vectorMeasure
            (Ioc a b) =
          signedCumulative mu nu b -
            signedCumulative mu nu a := by
      rw [(signedCumulativeBoundedVariation mu nu).vectorMeasure_Ioc
        hab.le]
      rw [((signedCumulativeRightContinuousAndLeftLim mu nu).1 b).rightLim_eq,
        ((signedCumulativeRightContinuousAndLeftLim mu nu).1 a).rightLim_eq]
    rw [← hVectorMeasure]
    exact ofReal_apply_le_posPart
      (signedCumulativeBoundedVariation mu nu).vectorMeasure
      measurableSet_Ioc

/-- Finite disjoint positive-increment sums are bounded simultaneously by
the crossing occupation and the positive Jordan mass of every set containing
the intervals. This is the partition form of the localized
layer-cake bound. -/
theorem finiteDisjointPositiveIncrements_le_crossingOccupation_and_positivePart
    {ι : Type*} [DecidableEq ι]
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (t : Finset ι) (left right : ι → Real)
    {s : Set Real}
    (hlt : ∀ i ∈ t, left i < right i)
    (hDisjoint :
      (t : Set ι).PairwiseDisjoint
        (fun i => Ioc (left i) (right i)))
    (hSubset :
      ∀ i ∈ t, Ioc (left i) (right i) ⊆ s) :
    let positiveIncrementSum :=
      ∑ i ∈ t,
        ENNReal.ofReal
          (signedCumulative mu nu (right i) -
            signedCumulative mu nu (left i))
    positiveIncrementSum ≤
        (∫⁻ h,
          ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞)
            ∂(volume : Measure Real)) ∧
      positiveIncrementSum ≤
        (SignedMeasure.toJordanDecomposition
          (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart s := by
  dsimp only
  let fiber : ι → Real → Set Real :=
    fun i h =>
      positiveCrossingFiber mu nu
        (Ioc (left i) (right i)) h
  have hIntervalBound (i : ι) (hi : i ∈ t) :
      ENNReal.ofReal
          (signedCumulative mu nu (right i) -
            signedCumulative mu nu (left i)) ≤
        (∫⁻ h, ((fiber i h).encard : ℝ≥0∞)
          ∂(volume : Measure Real)) ∧
      ENNReal.ofReal
          (signedCumulative mu nu (right i) -
            signedCumulative mu nu (left i)) ≤
        (SignedMeasure.toJordanDecomposition
          (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
            (Ioc (left i) (right i)) := by
    simpa only [fiber] using
      positiveIncrement_le_crossingOccupation_and_positivePart_Ioc
        mu nu hAtomless (hlt i hi)
  constructor
  · calc
      (∑ i ∈ t,
          ENNReal.ofReal
            (signedCumulative mu nu (right i) -
              signedCumulative mu nu (left i))) ≤
          ∑ i ∈ t,
            ∫⁻ h, ((fiber i h).encard : ℝ≥0∞)
              ∂(volume : Measure Real) := by
        exact Finset.sum_le_sum fun i hi => (hIntervalBound i hi).1
      _ = ∫⁻ h, ∑ i ∈ t, ((fiber i h).encard : ℝ≥0∞)
            ∂(volume : Measure Real) := by
        symm
        apply lintegral_finsetSum
        intro i hi
        exact measurable_positiveCrossingFiber_encard
          mu nu measurableSet_Ioc
      _ ≤ ∫⁻ h,
          ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞)
          ∂(volume : Measure Real) := by
        apply lintegral_mono
        intro h
        have hFiberSubset (i : ι) (hi : i ∈ t) :
            fiber i h ⊆ Ioc (left i) (right i) :=
          fun _ hx => hx.1
        have hFiberDisjoint :
            (t : Set ι).PairwiseDisjoint (fun i => fiber i h) :=
          hDisjoint.mono_on fun i hi => hFiberSubset i hi
        have hUnionSubset :
            (⋃ i ∈ (t : Set ι), fiber i h) ⊆
              positiveCrossingFiber mu nu s h := by
          intro x hx
          rcases mem_iUnion.1 hx with ⟨i, hx⟩
          rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
          exact ⟨hSubset i hi hxi.1, hxi.2⟩
        have hCard :=
          t.finite_toSet.encard_biUnion hFiberDisjoint
        have hCard' :
            (⋃ i ∈ (t : Set ι), fiber i h).encard =
              ∑ i ∈ t, (fiber i h).encard := by
          calc
            (⋃ i ∈ (t : Set ι), fiber i h).encard =
                ∑ᶠ i ∈ (t : Set ι), (fiber i h).encard :=
              hCard
            _ = ∑ i ∈ t, (fiber i h).encard := by
              simpa using
                (finsum_mem_eq_finite_toFinset_sum
                  (fun i => (fiber i h).encard) t.finite_toSet)
        have hCardENNReal :=
          congrArg ENat.toENNReal hCard'
        have hCastSum :
            ((∑ i ∈ t, (fiber i h).encard : ℕ∞) : ℝ≥0∞) =
              ∑ i ∈ t, ((fiber i h).encard : ℝ≥0∞) := by
          exact enat_toENNReal_finset_sum t
            (fun i => (fiber i h).encard)
        calc
          (∑ i ∈ t, ((fiber i h).encard : ℝ≥0∞)) =
              (((⋃ i ∈ (t : Set ι), fiber i h).encard : ℕ∞) :
                ℝ≥0∞) := by
            rw [← hCastSum]
            exact hCardENNReal.symm
          _ ≤ ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞) :=
            ENat.toENNReal_mono (Set.encard_le_encard hUnionSubset)
  · calc
      (∑ i ∈ t,
          ENNReal.ofReal
            (signedCumulative mu nu (right i) -
              signedCumulative mu nu (left i))) ≤
          ∑ i ∈ t,
            (SignedMeasure.toJordanDecomposition
              (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
                (Ioc (left i) (right i)) := by
        exact Finset.sum_le_sum fun i hi => (hIntervalBound i hi).2
      _ =
          (SignedMeasure.toJordanDecomposition
            (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
              (⋃ i ∈ (t : Set ι), Ioc (left i) (right i)) := by
        symm
        apply measure_biUnion_finset hDisjoint
        intro i hi
        exact measurableSet_Ioc
      _ ≤
          (SignedMeasure.toJordanDecomposition
            (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart s := by
        apply measure_mono
        intro x hx
        rcases mem_iUnion.1 hx with ⟨i, hx⟩
        rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
        exact hSubset i hi hxi

end

end ConcaveOTLimit
