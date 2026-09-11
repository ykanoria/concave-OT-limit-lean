import Definitions.Def_LiteralJuilletExcursion
import Theorems.Thm_ConcaveOTLimit_canonicalRouteGraphSourceAe
import Theorems.Thm_ConcaveOTLimit_consecutiveAtLevelRightUnique
import Theorems.Thm_ConcaveOTLimit_existsJuilletExcursionMapCoupling
import Theorems.Thm_ConcaveOTLimit_existsPositiveCrossingOccupationEnumeration
import Theorems.Thm_ConcaveOTLimit_goodIncreasingCrossingLevelEqOfAtomlessAt
import Theorems.Thm_ConcaveOTLimit_juilletBadCrossingLevelsNull
import Theorems.Thm_ConcaveOTLimit_juilletRouteConcentrationOfBadNullAndMapAC
import Theorems.Thm_ConcaveOTLimit_literalJuilletLevelAlternation
import Theorems.Thm_ConcaveOTLimit_literalJuilletMeasure
import Theorems.Thm_ConcaveOTLimit_literalJuilletRegularLevels
import Theorems.Thm_ConcaveOTLimit_measurablePositiveCrossingDecomposition

open Function MeasureTheory Set
open scoped ENNReal

namespace ConcaveOTLimit

private theorem exists_measurable_branch_of_crossing_piece
    {piece : Set (Real × Real)}
    (hPiece : MeasurableSet piece)
    (hInj : InjOn Prod.snd piece) :
    ∃ branch : Real -> Real,
      Measurable branch ∧
        ∀ p ∈ piece, branch p.2 = p.1 := by
  by_cases hNonempty : piece.Nonempty
  · letI : StandardBorelSpace piece := hPiece.standardBorel
    let level : piece -> Real := fun p => p.1.2
    have hLevelMeasurable : Measurable level :=
      measurable_snd.comp measurable_subtype_coe
    have hLevelInjective : Injective level := by
      intro p q hpq
      apply Subtype.ext
      exact hInj p.2 q.2 hpq
    have hEmbedding : MeasurableEmbedding level :=
      hLevelMeasurable.measurableEmbedding hLevelInjective
    letI : Nonempty piece := hNonempty.to_subtype
    let branch : Real -> Real :=
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

/-- The graph-decomposition construction actually enumerates every increasing
crossing exactly once at every level. This strengthens the existing
occupation theorem by exposing the pointwise bijection used in its proof. -/
theorem existsPositiveCrossingOccupationEnumeration_exhaustive
    (mu nu : FiniteMeasure Real)
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ (crossing : Nat -> Real -> Real)
        (levelSet : Nat -> Set Real),
      (∀ n, Measurable (crossing n)) ∧
        (∀ n, MeasurableSet (levelSet n)) ∧
        (∀ n h, h ∈ levelSet n ->
          IsGoodIncreasingCrossing mu nu (crossing n h) h) ∧
        (∀ h,
          BijOn (fun n => crossing n h)
            {n | h ∈ levelSet n}
            (positiveCrossingFiber mu nu univ h)) ∧
        Measure.sum (fun n =>
            Measure.map (crossing n)
              ((volume : Measure Real).restrict (levelSet n))) =
          juilletPositiveVariationMeasure mu nu ∧
        (∀ h,
          (∑' n,
              (levelSet n).indicator
                (fun _ => (1 : ENNReal)) h) =
            ((positiveCrossingFiber mu nu univ h).encard : ENNReal)) := by
  have hBranchExists :
      ∀ n, ∃ branch : Real -> Real,
        Measurable branch ∧
          ∀ p ∈ decomposition.piece n,
            branch p.2 = p.1 := fun n =>
    exists_measurable_branch_of_crossing_piece
      (decomposition.measurable_piece n) (decomposition.snd_injOn n)
  choose crossing hCrossingMeasurable hBranchOnPiece using hBranchExists
  let levelSet : Nat -> Set Real :=
    fun n => Prod.snd '' decomposition.piece n
  have hLevelSetMeasurable (n : Nat) :
      MeasurableSet (levelSet n) := by
    exact (decomposition.measurable_piece n).image_of_measurable_injOn
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
  have hBranchBijOn (s : Set Real) (h : Real) :
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
  have hBranchBijOnUniv (h : Real) :
      BijOn (fun n => crossing n h)
        {n | h ∈ levelSet n}
        (positiveCrossingFiber mu nu univ h) := by
    simpa only [mem_univ, and_true] using hBranchBijOn univ h
  have hFiberCount (s : Set Real) (h : Real) :
      (∑' n,
          {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
            (fun _ => (1 : ENNReal)) h) =
        ((positiveCrossingFiber mu nu s h).encard : ENNReal) := by
    let active : Set Nat :=
      {n | h ∈ levelSet n ∧ crossing n h ∈ s}
    have hBij :
        BijOn (fun n => crossing n h) active
          (positiveCrossingFiber mu nu s h) := by
      simpa only [active] using hBranchBijOn s h
    calc
      (∑' n,
          {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
            (fun _ => (1 : ENNReal)) h) =
          ∑' _ : active, (1 : ENNReal) := by
        symm
        simpa only [active, Set.mem_setOf_eq] using
          (tsum_subtype active (fun _ : Nat => (1 : ENNReal)))
      _ = (active.encard : ENNReal) :=
        ENNReal.tsum_set_one active
      _ = ((positiveCrossingFiber mu nu s h).encard : ENNReal) := by
        rw [Set.encard_congr hBij.equiv]
  have hOccupation :
      Measure.sum (fun n =>
          Measure.map (crossing n)
            ((volume : Measure Real).restrict (levelSet n))) =
        juilletPositiveVariationMeasure mu nu := by
    ext s hs
    have hActiveMeasurable (n : Nat) :
        MeasurableSet
          {h | h ∈ levelSet n ∧ crossing n h ∈ s} :=
      (hLevelSetMeasurable n).inter
        (hs.preimage (hCrossingMeasurable n))
    calc
      Measure.sum (fun n =>
          Measure.map (crossing n)
            ((volume : Measure Real).restrict (levelSet n))) s =
          ∑' n,
            Measure.map (crossing n)
              ((volume : Measure Real).restrict (levelSet n)) s :=
        Measure.sum_apply _ hs
      _ = ∑' n,
          (volume : Measure Real)
            {h | h ∈ levelSet n ∧ crossing n h ∈ s} := by
        apply tsum_congr
        intro n
        rw [Measure.map_apply (hCrossingMeasurable n) hs,
          Measure.restrict_apply
            (hs.preimage (hCrossingMeasurable n))]
        congr 1
        ext h
        simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, and_comm]
      _ = ∑' n,
          ∫⁻ h,
            {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
              (fun _ => (1 : ENNReal)) h
            ∂(volume : Measure Real) := by
        apply tsum_congr
        intro n
        exact (lintegral_indicator_one (hActiveMeasurable n)).symm
      _ = ∫⁻ h,
          ∑' n,
            {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
              (fun _ => (1 : ENNReal)) h
          ∂(volume : Measure Real) := by
        symm
        apply lintegral_tsum
        intro n
        exact (measurable_const.indicator
          (hActiveMeasurable n)).aemeasurable
      _ = ∫⁻ h,
          ((positiveCrossingFiber mu nu s h).encard : ENNReal)
          ∂(volume : Measure Real) :=
        lintegral_congr (hFiberCount s)
      _ = juilletPositiveVariationMeasure mu nu s :=
        hIndicatrix s hs
  have hCount (h : Real) :
      (∑' n,
          (levelSet n).indicator
            (fun _ => (1 : ENNReal)) h) =
        ((positiveCrossingFiber mu nu univ h).encard : ENNReal) := by
    simpa only [mem_univ, and_true] using hFiberCount univ h
  exact ⟨crossing, levelSet, hCrossingMeasurable,
    hLevelSetMeasurable, fun n h hh => hBranchGood n hh,
    hBranchBijOnUniv, hOccupation, hCount⟩

private theorem signedCumulative_nonnegative_of_stochasticOrder
    {mu nu : FiniteMeasure Real}
    (hOrder : StochasticallyDominates nu mu) (x : Real) :
    0 <= signedCumulative mu nu x := by
  have hToReal :
      ((nu : Measure Real) (Iic x)).toReal <=
        ((mu : Measure Real) (Iic x)).toReal :=
    ENNReal.toReal_mono
      (measure_ne_top (mu : Measure Real) (Iic x))
      (hOrder x)
  unfold signedCumulative
  linarith

/-- Under source atomlessness and stochastic order, every strict increasing
crossing lies at a genuinely positive level. -/
theorem goodIncreasingCrossing_positive
    {mu nu : FiniteMeasure Real}
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    {x h : Real}
    (hCrossing : IsGoodIncreasingCrossing mu nu x h) :
    0 < h := by
  have hCumulativeNonnegative :
      0 <= signedCumulative mu nu x :=
    signedCumulative_nonnegative_of_stochasticOrder hOrder x
  have hCumulativeLeLeft :
      signedCumulative mu nu x <= signedCumulativeLeft mu nu x :=
    signedCumulativeLeLeftOfAtomlessAt mu nu x (hAtomless x)
  have hLevelNonnegative : 0 <= h := by
    have hGraph := hCrossing.1
    change h ∈
      uIcc (signedCumulativeLeft mu nu x)
        (signedCumulative mu nu x) at hGraph
    rw [uIcc_comm, uIcc_of_le hCumulativeLeLeft] at hGraph
    exact hCumulativeNonnegative.trans hGraph.1
  refine lt_of_le_of_ne hLevelNonnegative ?_
  intro hZero
  obtain ⟨_hGraph, epsilon, hEpsilon, hLocal⟩ := hCrossing
  let x' := x - epsilon / 2
  have hxMem : x' ∈ Ioo (x - epsilon) (x + epsilon) := by
    dsimp only [x']
    constructor <;> linarith
  have hxNe : x' ≠ x := by
    dsimp only [x']
    linarith
  have hxGraph :
      (x', signedCumulative mu nu x') ∈
        generalizedCumulativeGraph mu nu := by
    change signedCumulative mu nu x' ∈
      uIcc (signedCumulativeLeft mu nu x')
        (signedCumulative mu nu x')
    exact right_mem_uIcc
  have hProduct := hLocal hxMem hxNe hxGraph
  have hxCumulativeNonnegative :
      0 <= signedCumulative mu nu x' :=
    signedCumulative_nonnegative_of_stochasticOrder hOrder x'
  rw [← hZero] at hProduct
  have hProduct' :
      0 < signedCumulative mu nu x' * (x' - x) := by
    simpa only [sub_zero] using hProduct
  have hxDiffNegative : x' - x < 0 := by
    dsimp only [x']
    linarith
  exact (not_lt_of_ge
    (mul_nonpos_of_nonneg_of_nonpos hxCumulativeNonnegative
      hxDiffNegative.le)) hProduct'

/-- If every target branch is obtained from its source branch by one
measurable map, the literal pair occupation is the corresponding graph
plan. -/
theorem literalJuilletExcursionMeasure_eq_finiteGraphPlan
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu)
    (T : Real -> Real)
    (hT : Measurable T)
    (hTarget :
      ∀ i h, data.target i h = T (data.source i h))
    (hSourceOccupation :
      Measure.sum (fun i =>
          Measure.map (data.source i)
            ((volume : Measure Real).restrict (data.active i))) =
        (mu : Measure Real)) :
    literalJuilletExcursionMeasure data =
      ((finiteGraphPlan mu T hT :
          FiniteMeasure (Real × Real)) :
        Measure (Real × Real)) := by
  have hPairMeasurable :
      Measurable (fun x : Real => (x, T x)) :=
    measurable_id.prodMk hT
  simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
  rw [literalJuilletExcursionMeasure]
  calc
    Measure.sum (fun i =>
        Measure.map
          (fun h => (data.source i h, data.target i h))
          ((volume : Measure Real).restrict (data.active i))) =
        Measure.sum (fun i =>
          Measure.map (fun x : Real => (x, T x))
            (Measure.map (data.source i)
              ((volume : Measure Real).restrict
                (data.active i)))) := by
      apply Measure.sum_congr
      intro i
      rw [Measure.map_map hPairMeasurable
        (data.source_measurable i)]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun h =>
        Prod.ext rfl (hTarget i h)
    _ = Measure.map (fun x : Real => (x, T x))
        (Measure.sum fun i =>
          Measure.map (data.source i)
            ((volume : Measure Real).restrict
              (data.active i))) :=
      (Measure.map_sum hPairMeasurable.aemeasurable).symm
    _ = Measure.map (fun x : Real => (x, T x))
        (mu : Measure Real) := by
      rw [hSourceOccupation]

/-- Given an existing Juillet excursion coupling, a measurable entrance
decomposition and its Banach-indicatrix identity construct literal
completed-graph pairing data whose occupation measure is exactly that
coupling. -/
theorem literalJuilletPairingConstruction_of_juilletExcursionPlan
    (mu nu : FiniteMeasure Real)
    (gamma : FiniteCoupling mu nu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan)
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (decomposition :
      MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ data : JuilletCompletedGraphPairingData mu nu,
      Measure.map Prod.fst
          (literalJuilletExcursionMeasure data) =
        (mu : Measure Real) ∧
      Measure.map Prod.snd
          (literalJuilletExcursionMeasure data) =
        (nu : Measure Real) ∧
      (gamma.plan : Measure (Real × Real)) =
        literalJuilletExcursionMeasure data := by
  obtain ⟨source, active, hSourceMeasurable, hActiveMeasurable,
      hSourceGood, hSourceBij, hSourceVariation, _hSourceCount⟩ :=
    existsPositiveCrossingOccupationEnumeration_exhaustive
      mu nu decomposition hIndicatrix
  have hActivePositive (i : Nat) :
      active i ⊆ Ioi 0 := by
    intro h hh
    exact goodIncreasingCrossing_positive hAtomless hOrder
      (hSourceGood i h hh)
  have hSourceOccupation :
      Measure.sum (fun i =>
          Measure.map (source i)
            ((volume : Measure Real).restrict (active i))) =
        (mu : Measure Real) :=
    hSourceVariation.trans
      (juilletPositiveVariationMeasureEqSource hSingular)
  obtain ⟨T, hGraph⟩ :=
    juilletExcursionPlanIsGraph
      gamma hSingular hAtomless hOrder hExcursion
  obtain ⟨hT, hPlan⟩ := hGraph
  have hGraph' : IsGraphPlan gamma T :=
    ⟨hT, hPlan⟩
  let target : Nat -> Real -> Real :=
    fun i h => T (source i h)
  have hTargetMeasurable (i : Nat) :
      Measurable (target i) :=
    hT.comp (hSourceMeasurable i)
  have hMapAC :
      Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
        (volume : Measure Real) := by
    apply juilletCumulativeLevelMapACOfPositiveCrossingEnumeration
      hSingular hAtomless source active hSourceMeasurable
        hSourceVariation
    intro i
    exact (ae_restrict_mem (hActiveMeasurable i)).mono
      fun h hh => hSourceGood i h hh
  have hRouteSupport :
      IsSupported gamma (juilletCanonicalRouteSet mu nu) :=
    juilletRouteConcentrationOfBadNullAndMapAC
      hSingular hAtomless hOrder
        (juilletBadCrossingLevelsNull mu nu hAtomless)
        hMapAC gamma hExcursion
  have hRouteSource :
      ∀ᵐ x ∂(mu : Measure Real),
        (x, T x) ∈ juilletCanonicalRouteSet mu nu :=
    canonicalRouteGraphSourceAe gamma hGraph' hRouteSupport
  have hPairedAtIndex (i : Nat) :
      ∀ᵐ h ∂(volume : Measure Real),
        h ∈ active i ->
          (source i h, target i h) ∈
            juilletCompletedGraphPairFiber mu nu h := by
    let branchMeasure : Measure Real :=
      Measure.map (source i)
        ((volume : Measure Real).restrict (active i))
    have hBranchLe :
        branchMeasure <= (mu : Measure Real) := by
      rw [← hSourceOccupation]
      exact Measure.le_sum _ i
    have hRouteBranch :
        ∀ᵐ x ∂branchMeasure,
          (x, T x) ∈ juilletCanonicalRouteSet mu nu :=
      (Measure.absolutelyContinuous_of_le hBranchLe).ae_le hRouteSource
    have hRouteAtLevel :
        ∀ᵐ h ∂(volume : Measure Real).restrict (active i),
          (source i h, target i h) ∈
            juilletCanonicalRouteSet mu nu := by
      exact ae_of_ae_map
        (hSourceMeasurable i).aemeasurable hRouteBranch
    have hPairAtLevel :
        ∀ᵐ h ∂(volume : Measure Real).restrict (active i),
          (source i h, target i h) ∈
            juilletCompletedGraphPairFiber mu nu h := by
      filter_upwards
        [hRouteAtLevel,
         ae_restrict_mem (hActiveMeasurable i)] with h hRoute hActive
      rcases hRoute with
        ⟨level, hLevelPositive, hLevelSource,
          hLevelTarget, hLevelConsecutive⟩
      have hAtLevel := hSourceGood i h hActive
      have hEq :
          level = h := by
        have hLevelEq :=
          goodIncreasingCrossingLevelEqOfAtomlessAt
            mu nu (source i h) level
              (hAtomless (source i h)) hLevelSource
        have hEq' :=
          goodIncreasingCrossingLevelEqOfAtomlessAt
            mu nu (source i h) h
              (hAtomless (source i h)) hAtLevel
        exact hLevelEq.trans hEq'.symm
      subst level
      exact ⟨hActivePositive i hActive, hAtLevel,
        hLevelTarget, hLevelConsecutive⟩
    exact ae_imp_of_ae_restrict hPairAtLevel
  have hPaired :
      ∀ᵐ h ∂(volume : Measure Real),
        ∀ i, h ∈ active i ->
          (source i h, target i h) ∈
            juilletCompletedGraphPairFiber mu nu h :=
    ae_all_iff.mpr hPairedAtIndex
  have hEntrancesExhaustive :
      ∀ᵐ h ∂(volume : Measure Real),
        ∀ x, 0 < h ->
          IsGoodIncreasingCrossing mu nu x h ->
            ∃! i : Nat, h ∈ active i ∧ source i h = x := by
    refine Filter.Eventually.of_forall fun h x _hPositive hx => ?_
    have hxFiber :
        x ∈ positiveCrossingFiber mu nu univ h :=
      ⟨mem_univ x, hx⟩
    obtain ⟨i, hi, hix⟩ := (hSourceBij h).surjOn hxFiber
    refine ⟨i, ⟨hi, hix⟩, ?_⟩
    intro j hj
    exact ((hSourceBij h).injOn hi hj.1
      (hix.trans hj.2.symm)).symm
  have hExitsExhaustive :
      ∀ᵐ h ∂(volume : Measure Real),
        ∀ y, 0 < h ->
          IsGoodDecreasingCrossing mu nu y h ->
            ∃! i : Nat, h ∈ active i ∧ target i h = y := by
    have hRegular :
        ∀ᵐ h ∂(volume : Measure Real),
          h ∈ Ioi 0 ->
            IsJuilletRegularPositiveLevel mu nu h :=
      ae_imp_of_ae_restrict
        (isJuilletRegularPositiveLevel_ae mu nu hAtomless)
    filter_upwards [hPaired, hRegular] with h hPair hRegularAt
    intro y hPositive hy
    have hFacts :=
      literalJuilletLevelAlternation_of_coupling gamma hOrder
        (hRegularAt hPositive)
    obtain ⟨x, hx, _hxUnique⟩ :=
      hFacts.decreasing_is_paired y hy
    have hxFiber :
        x ∈ positiveCrossingFiber mu nu univ h :=
      ⟨mem_univ x, hx.1⟩
    obtain ⟨i, hi, hix⟩ :=
      (hSourceBij h).surjOn hxFiber
    have hConsecutiveI :
        AreConsecutiveAtLevel mu nu h x (target i h) := by
      simpa only [hix] using (hPair i hi).2.2.2
    have hiy :
        target i h = y :=
      consecutiveAtLevelRightUnique
        mu nu h x (target i h) y hConsecutiveI hx.2
    refine ⟨i, ⟨hi, hiy⟩, ?_⟩
    intro j hj
    have hConsecutiveJ :
        AreConsecutiveAtLevel mu nu h (source j h) y := by
      simpa only [hj.2] using (hPair j hj.1).2.2.2
    have hxj :
        x = source j h :=
      consecutiveAtLevelLeftUnique
        mu nu h x (source j h) y hx.2 hConsecutiveJ
    exact ((hSourceBij h).injOn hi hj.1 (hix.trans hxj)).symm
  have hFiniteActive :
      ∀ᵐ h ∂(volume : Measure Real),
        {i | h ∈ active i}.Finite := by
    filter_upwards
      [positiveCrossingFiberFiniteAe mu nu univ] with h hFinite
    exact (hSourceBij h).finite_iff_finite.mpr hFinite
  let data : JuilletCompletedGraphPairingData mu nu := {
    source := source
    target := target
    active := active
    source_measurable := hSourceMeasurable
    target_measurable := hTargetMeasurable
    active_measurable := hActiveMeasurable
    active_positive := hActivePositive
    regular_positive_levels :=
      isJuilletRegularPositiveLevel_ae mu nu hAtomless
    paired_ae := hPaired
    entrances_exhaustive_unique_ae := hEntrancesExhaustive
    exits_exhaustive_unique_ae := hExitsExhaustive
    finite_active_ae := hFiniteActive
  }
  have hMapTarget :
      Measure.map T (mu : Measure Real) =
        (nu : Measure Real) := by
    have hSecond :=
      congrArg
        (fun eta : FiniteMeasure Real => (eta : Measure Real))
        gamma.property.2
    change
      Measure.map Prod.snd
          (gamma.plan : Measure (Real × Real)) =
        (nu : Measure Real) at hSecond
    rw [hPlan, finiteGraphPlan] at hSecond
    change
      Measure.map Prod.snd
          (Measure.map (fun x : Real => (x, T x))
            (mu : Measure Real)) =
        (nu : Measure Real) at hSecond
    have hPairMeasurable :
        Measurable (fun x : Real => (x, T x)) :=
      measurable_id.prodMk hT
    have hMapMap :
        Measure.map Prod.snd
            (Measure.map (fun x : Real => (x, T x))
              (mu : Measure Real)) =
          Measure.map
            (Prod.snd ∘ fun x : Real => (x, T x))
            (mu : Measure Real) :=
      Measure.map_map measurable_snd hPairMeasurable
    calc
      Measure.map T (mu : Measure Real) =
          Measure.map
            (Prod.snd ∘ fun x : Real => (x, T x))
            (mu : Measure Real) := by
        rfl
      _ = Measure.map Prod.snd
          (Measure.map (fun x : Real => (x, T x))
            (mu : Measure Real)) :=
        hMapMap.symm
      _ = (nu : Measure Real) := hSecond
  have hTargetOccupation :
      Measure.sum (fun i =>
          Measure.map (target i)
            ((volume : Measure Real).restrict (active i))) =
        (nu : Measure Real) := by
    calc
      Measure.sum (fun i =>
          Measure.map (target i)
            ((volume : Measure Real).restrict (active i))) =
          Measure.map T
            (Measure.sum fun i =>
              Measure.map (source i)
                ((volume : Measure Real).restrict (active i))) := by
        rw [Measure.map_sum hT.aemeasurable]
        apply Measure.sum_congr
        intro i
        rw [Measure.map_map hT (hSourceMeasurable i)]
        rfl
      _ = Measure.map T (mu : Measure Real) := by
        rw [hSourceOccupation]
      _ = (nu : Measure Real) := hMapTarget
  have hGraphPlanMeasure :
      (gamma.plan : Measure (Real × Real)) =
        ((finiteGraphPlan mu T hT :
            FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) :=
    congrArg
      (fun eta : FiniteMeasure (Real × Real) =>
        (eta : Measure (Real × Real))) hPlan
  have hLiteralPlan :
      (gamma.plan : Measure (Real × Real)) =
        literalJuilletExcursionMeasure data :=
    hGraphPlanMeasure.trans
      (literalJuilletExcursionMeasure_eq_finiteGraphPlan
        data T hT (fun _ _ => rfl) hSourceOccupation).symm
  refine ⟨data, ?_, ?_, hLiteralPlan⟩
  · rw [map_fst_literalJuilletExcursionMeasure]
    exact hSourceOccupation
  · rw [map_snd_literalJuilletExcursionMeasure]
    exact hTargetOccupation

/-- Under the crossing decomposition and indicatrix hypotheses, every
existing Juillet excursion coupling is its literal completed-graph
occupation measure. -/
theorem isLiteralJuilletExcursionPlan_of_juilletExcursionPlan
    (mu nu : FiniteMeasure Real)
    (gamma : FiniteCoupling mu nu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan)
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (decomposition :
      MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    IsLiteralJuilletExcursionPlan mu nu gamma.plan := by
  obtain ⟨data, _hFirst, _hSecond, hLiteral⟩ :=
    literalJuilletPairingConstruction_of_juilletExcursionPlan
      mu nu gamma hExcursion hSingular hAtomless hOrder
        decomposition hIndicatrix
  exact ⟨gamma.property, data, hLiteral⟩

/-- A uniform supply of measurable crossing decompositions and their
indicatrix identities directly discharges the one-dimensional literal
identification premise, without constructing a second coupling. -/
theorem literalJuilletIdentificationPremise_of_crossingDecompositions
    (hCrossingAnalysis :
      ∀ (mu nu : FiniteMeasure Real),
        IsAtomlessFinite mu ->
          FiniteMutuallySingular mu nu ->
            StochasticallyDominates nu mu ->
              ∃ _decomposition :
                  MeasurablePositiveCrossingDecomposition mu nu,
                PositiveCrossingIndicatrixIdentity mu nu) :
    LiteralJuilletIdentificationPremise := by
  intro mu nu gamma hAtomless hSingular hOrder hCoupling
    _hForward hExcursion
  obtain ⟨decomposition, hIndicatrix⟩ :=
    hCrossingAnalysis mu nu hAtomless hSingular hOrder
  let gammaCoupling : FiniteCoupling mu nu :=
    ⟨gamma, hCoupling⟩
  exact
    isLiteralJuilletExcursionPlan_of_juilletExcursionPlan
      mu nu gammaCoupling hExcursion hSingular hAtomless hOrder
        decomposition hIndicatrix

/-- The measurable crossing decomposition is unconditional, so the oriented
indicatrix identity is the only remaining analytic input to literal
one-dimensional identification. -/
theorem literalJuilletIdentificationPremise_of_positiveCrossingIndicatrix
    (hIndicatrix :
      ∀ (mu nu : FiniteMeasure Real),
        IsAtomlessFinite mu ->
          FiniteMutuallySingular mu nu ->
            StochasticallyDominates nu mu ->
              PositiveCrossingIndicatrixIdentity mu nu) :
    LiteralJuilletIdentificationPremise := by
  apply literalJuilletIdentificationPremise_of_crossingDecompositions
  intro mu nu hAtomless hSingular hOrder
  exact
    ⟨measurablePositiveCrossingDecomposition mu nu,
      hIndicatrix mu nu hAtomless hSingular hOrder⟩

/-- A measurable entrance decomposition and its Banach-indicatrix identity
construct literal completed-graph pairing data with the prescribed
marginals. -/
theorem literalJuilletPairingConstruction
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (decomposition :
      MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ data : JuilletCompletedGraphPairingData mu nu,
      Measure.map Prod.fst
          (literalJuilletExcursionMeasure data) =
        (mu : Measure Real) ∧
      Measure.map Prod.snd
          (literalJuilletExcursionMeasure data) =
        (nu : Measure Real) := by
  obtain ⟨gamma, _T, _hGraph, _hForward, hExcursion, _hUnique⟩ :=
    existsJuilletExcursionMapCoupling
      mu nu hMass hPositive hFirstMu hFirstNu
        hSingular hAtomless hOrder
  obtain ⟨data, hFirst, hSecond, _hPlan⟩ :=
    literalJuilletPairingConstruction_of_juilletExcursionPlan
      mu nu gamma hExcursion hSingular hAtomless hOrder
        decomposition hIndicatrix
  exact ⟨data, hFirst, hSecond⟩

/-- The constructed pairing and its exact marginal identities produce a
finite literal Juillet excursion coupling. -/
theorem existsLiteralJuilletExcursionPlan_of_crossingDecompositions
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (decomposition :
      MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ gamma : FiniteMeasure (Real × Real),
      IsLiteralJuilletExcursionPlan mu nu gamma := by
  obtain ⟨data, hFirst, hSecond⟩ :=
    literalJuilletPairingConstruction
      mu nu hMass hPositive hFirstMu hFirstNu hSingular
        hAtomless hOrder decomposition hIndicatrix
  exact exists_literalJuilletExcursionPlan_of_pairing_marginals
    data hFirst hSecond

/-- The literal completed-graph occupation and the existing laminar Juillet
coupling are one and the same finite measure. -/
theorem existsLiteralAndJuilletExcursionPlan_of_crossingDecompositions
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (decomposition :
      MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ gamma : FiniteMeasure (Real × Real),
      IsLiteralJuilletExcursionPlan mu nu gamma ∧
        IsJuilletExcursionPlan mu nu gamma := by
  obtain ⟨gamma, _T, _hGraph, _hForward, hExcursion, _hUnique⟩ :=
    existsJuilletExcursionMapCoupling
      mu nu hMass hPositive hFirstMu hFirstNu
        hSingular hAtomless hOrder
  exact ⟨gamma.plan,
    isLiteralJuilletExcursionPlan_of_juilletExcursionPlan
      mu nu gamma hExcursion hSingular hAtomless hOrder
        decomposition hIndicatrix,
    hExcursion⟩

end ConcaveOTLimit
