import Theorems.Thm_ConcaveOTLimit_completedGraphLevelFiniteAe
import Theorems.Thm_ConcaveOTLimit_positiveCrossingMeasureConstruction
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Function MeasureTheory Set
open scoped ENNReal

namespace ConcaveOTLimit

/-- The relation whose level fibers are the good increasing crossings. -/
def positiveCrossingRelation
    (mu nu : FiniteMeasure Real) : Set (Real × Real) :=
  {p | IsGoodIncreasingCrossing mu nu p.1 p.2}

/-- Good increasing crossings at level `h`, restricted to abscissae in `s`. -/
def positiveCrossingFiber
    (mu nu : FiniteMeasure Real) (s : Set Real) (h : Real) : Set Real :=
  {x | x ∈ s ∧ IsGoodIncreasingCrossing mu nu x h}

/-- The oriented Banach-indicatrix identity needed for the positive Jordan
variation.  This formulation is independent of any choice of enumeration. -/
def PositiveCrossingIndicatrixIdentity
    (mu nu : FiniteMeasure Real) : Prop :=
  ∀ s : Set Real, MeasurableSet s →
    (∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞)
      ∂(volume : Measure Real)) =
      juilletPositiveVariationMeasure mu nu s

/-- A Lusin-Novikov-style decomposition of the positive-crossing relation
into measurable graphs over the level coordinate. -/
structure MeasurablePositiveCrossingDecomposition
    (mu nu : FiniteMeasure Real) where
  piece : Nat → Set (Real × Real)
  measurable_piece : ∀ n, MeasurableSet (piece n)
  pairwise_disjoint : Pairwise (Disjoint on piece)
  iUnion_piece : (⋃ n, piece n) = positiveCrossingRelation mu nu
  snd_injOn : ∀ n, InjOn Prod.snd (piece n)

/-- The positive-crossing fibers are finite almost everywhere.  Thus the
extended cardinal in `PositiveCrossingIndicatrixIdentity` is finite away from
a Lebesgue-null set. -/
theorem positiveCrossingFiberFiniteAe
    (mu nu : FiniteMeasure Real) (s : Set Real) :
    ∀ᵐ h ∂(volume : Measure Real),
      (positiveCrossingFiber mu nu s h).Finite := by
  filter_upwards [generalizedCumulativeGraphLevelFiniteAe mu nu] with h hFinite
  exact hFinite.subset fun x hx => hx.2.1

private theorem exists_measurable_branch_of_piece
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
      have hFirst :=
        congrArg (fun r : piece => r.1.1) hLeft
      simpa only [branch, level, q] using hFirst
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    intro p hp
    exact (hNonempty ⟨p, hp⟩).elim

/-- A measurable graph decomposition and the branch-independent oriented
indicatrix identity produce an exhaustive measurable occupation enumeration.
At every level, the active branches enumerate every good increasing crossing
exactly once; the active indices are finite at almost every level. -/
theorem
    existsPositiveCrossingOccupationEnumeration_exhaustive_of_graphDecomposition
    (mu nu : FiniteMeasure Real)
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ (crossing : Nat → Real → Real)
        (levelSet : Nat → Set Real),
      (∀ n, Measurable (crossing n)) ∧
        (∀ n, MeasurableSet (levelSet n)) ∧
        (∀ n h, h ∈ levelSet n →
          IsGoodIncreasingCrossing mu nu (crossing n h) h) ∧
        (∀ h,
          BijOn (fun n => crossing n h)
            {n | h ∈ levelSet n}
            (positiveCrossingFiber mu nu univ h)) ∧
        (∀ᵐ h ∂(volume : Measure Real),
          {n | h ∈ levelSet n}.Finite) ∧
        Measure.sum
            (fun n =>
              Measure.map (crossing n)
                ((volume : Measure Real).restrict (levelSet n))) =
          juilletPositiveVariationMeasure mu nu := by
  have hBranchExists :
      ∀ n, ∃ branch : Real → Real,
        Measurable branch ∧
          ∀ p ∈ decomposition.piece n,
            branch p.2 = p.1 := fun n =>
    exists_measurable_branch_of_piece
      (decomposition.measurable_piece n) (decomposition.snd_injOn n)
  choose crossing hCrossingMeasurable hBranchOnPiece using hBranchExists
  let levelSet : Nat → Set Real :=
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
  have hActiveFinite :
      ∀ᵐ h ∂(volume : Measure Real),
        {n | h ∈ levelSet n}.Finite := by
    filter_upwards [positiveCrossingFiberFiniteAe mu nu univ] with h hFinite
    exact (hBranchBijOnUniv h).finite_iff_finite.mpr hFinite
  have hFiberCount (s : Set Real) (h : Real) :
      (∑' n,
          {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
            (fun _ => (1 : ℝ≥0∞)) h) =
        ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞) := by
    let active : Set Nat :=
      {n | h ∈ levelSet n ∧ crossing n h ∈ s}
    have hBij :
        BijOn (fun n => crossing n h) active
          (positiveCrossingFiber mu nu s h) := by
      simpa only [active] using hBranchBijOn s h
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
              (fun _ => (1 : ℝ≥0∞)) h
            ∂(volume : Measure Real) := by
        apply tsum_congr
        intro n
        exact (lintegral_indicator_one (hActiveMeasurable n)).symm
      _ = ∫⁻ h,
          ∑' n,
            {u | u ∈ levelSet n ∧ crossing n u ∈ s}.indicator
              (fun _ => (1 : ℝ≥0∞)) h
          ∂(volume : Measure Real) := by
        symm
        apply lintegral_tsum
        intro n
        exact (measurable_const.indicator
          (hActiveMeasurable n)).aemeasurable
      _ = ∫⁻ h,
          ((positiveCrossingFiber mu nu s h).encard : ℝ≥0∞)
          ∂(volume : Measure Real) :=
        lintegral_congr (hFiberCount s)
      _ = juilletPositiveVariationMeasure mu nu s :=
        hIndicatrix s hs
  exact ⟨crossing, levelSet, hCrossingMeasurable,
    hLevelSetMeasurable, fun n h hh => hBranchGood n hh,
    hBranchBijOnUniv, hActiveFinite, hOccupation⟩

/-- A measurable graph decomposition and the branch-independent oriented
indicatrix identity produce the exact measurable occupation enumeration. -/
theorem existsPositiveCrossingOccupationEnumeration_of_graphDecomposition
    (mu nu : FiniteMeasure Real)
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ (crossing : Nat → Real → Real)
        (levelSet : Nat → Set Real),
      (∀ n, Measurable (crossing n)) ∧
        (∀ n, MeasurableSet (levelSet n)) ∧
        (∀ n,
          ∀ᵐ h ∂((volume : Measure Real).restrict (levelSet n)),
            IsGoodIncreasingCrossing mu nu (crossing n h) h) ∧
        Measure.sum (fun n =>
            Measure.map (crossing n)
              ((volume : Measure Real).restrict (levelSet n))) =
          juilletPositiveVariationMeasure mu nu := by
  obtain ⟨crossing, levelSet, hCrossingMeasurable,
      hLevelSetMeasurable, hCrossingOn, _hBranchBijOn,
      _hActiveFinite, hOccupation⟩ :=
    existsPositiveCrossingOccupationEnumeration_exhaustive_of_graphDecomposition
      mu nu decomposition hIndicatrix
  have hCrossing :
      ∀ n,
        ∀ᵐ h ∂((volume : Measure Real).restrict (levelSet n)),
          IsGoodIncreasingCrossing mu nu (crossing n h) h := by
    intro n
    exact (ae_restrict_mem (hLevelSetMeasurable n)).mono
      fun h hh => hCrossingOn n h hh
  exact ⟨crossing, levelSet, hCrossingMeasurable,
    hLevelSetMeasurable, hCrossing, hOccupation⟩

/-- Lean-ready fallback for the requested occupation-enumeration theorem.
The extra decomposition premise is the precise Lusin-Novikov boundary, while
`hIndicatrix` is the remaining analytic premise. -/
theorem existsPositiveCrossingOccupationEnumeration
    (mu nu : FiniteMeasure Real)
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ (crossing : Nat → Real → Real)
        (levelSet : Nat → Set Real),
      (∀ n, Measurable (crossing n)) ∧
        (∀ n, MeasurableSet (levelSet n)) ∧
        (∀ n,
          ∀ᵐ h ∂((volume : Measure Real).restrict (levelSet n)),
            IsGoodIncreasingCrossing mu nu (crossing n h) h) ∧
        Measure.sum (fun n =>
            Measure.map (crossing n)
              ((volume : Measure Real).restrict (levelSet n))) =
          juilletPositiveVariationMeasure mu nu :=
  existsPositiveCrossingOccupationEnumeration_of_graphDecomposition
    mu nu decomposition hIndicatrix

/-- The enumeration theorem supplies the positive crossing measure expected
by the existing C154/C168 interface. -/
theorem existsPositiveCrossingMeasure_of_graphDecomposition
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (hIndicatrix : PositiveCrossingIndicatrixIdentity mu nu) :
    ∃ zeta : Measure (Real × Real),
      Measure.map Prod.fst zeta = (mu : Measure Real) ∧
        Measure.map Prod.snd zeta ≪ (volume : Measure Real) ∧
          ∀ᵐ p ∂zeta,
            IsGoodIncreasingCrossing mu nu p.1 p.2 := by
  obtain ⟨crossing, levelSet, hCrossingMeasurable, _hLevelSetMeasurable,
      hCrossing, hOccupation⟩ :=
    existsPositiveCrossingOccupationEnumeration
      mu nu decomposition hIndicatrix
  exact positiveCrossingMeasureConstruction hSingular crossing levelSet
    hCrossingMeasurable hOccupation hCrossing

end ConcaveOTLimit
