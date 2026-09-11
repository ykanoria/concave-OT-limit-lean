import Theorems.Thm_ConcaveOTLimit_positiveCrossingOccupationFinite
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Function MeasureTheory Set
open scoped ENNReal

namespace ConcaveOTLimit

noncomputable section

private theorem exists_measurable_positiveCrossingBranch
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

private noncomputable def positiveCrossingOccupationBranch
    (mu nu : FiniteMeasure Real) (n : Nat) : Real → Real :=
  Classical.choose
    (exists_measurable_positiveCrossingBranch
      ((measurablePositiveCrossingDecomposition mu nu).measurable_piece n)
      ((measurablePositiveCrossingDecomposition mu nu).snd_injOn n))

private noncomputable def positiveCrossingOccupationLevelSet
    (mu nu : FiniteMeasure Real) (n : Nat) : Set Real :=
  Prod.snd ''
    (measurablePositiveCrossingDecomposition mu nu).piece n

private theorem positiveCrossingOccupationBranch_spec
    (mu nu : FiniteMeasure Real) (n : Nat) :
    Measurable (positiveCrossingOccupationBranch mu nu n) ∧
      ∀ p ∈ (measurablePositiveCrossingDecomposition mu nu).piece n,
        positiveCrossingOccupationBranch mu nu n p.2 = p.1 :=
  Classical.choose_spec
    (exists_measurable_positiveCrossingBranch
      ((measurablePositiveCrossingDecomposition mu nu).measurable_piece n)
      ((measurablePositiveCrossingDecomposition mu nu).snd_injOn n))

private theorem measurable_positiveCrossingOccupationBranch
    (mu nu : FiniteMeasure Real) (n : Nat) :
    Measurable (positiveCrossingOccupationBranch mu nu n) :=
  (positiveCrossingOccupationBranch_spec mu nu n).1

private theorem measurableSet_positiveCrossingOccupationLevelSet
    (mu nu : FiniteMeasure Real) (n : Nat) :
    MeasurableSet (positiveCrossingOccupationLevelSet mu nu n) := by
  exact
    ((measurablePositiveCrossingDecomposition mu nu).measurable_piece n)
      |>.image_of_measurable_injOn measurable_snd
        ((measurablePositiveCrossingDecomposition mu nu).snd_injOn n)

private theorem positiveCrossingOccupationBranch_mem_piece
    (mu nu : FiniteMeasure Real) (n : Nat) {h : Real}
    (hh : h ∈ positiveCrossingOccupationLevelSet mu nu n) :
    (positiveCrossingOccupationBranch mu nu n h, h) ∈
      (measurablePositiveCrossingDecomposition mu nu).piece n := by
  rcases hh with ⟨p, hp, rfl⟩
  rw [(positiveCrossingOccupationBranch_spec mu nu n).2 p hp]
  exact hp

private theorem positiveCrossingOccupationBranch_good
    (mu nu : FiniteMeasure Real) (n : Nat) {h : Real}
    (hh : h ∈ positiveCrossingOccupationLevelSet mu nu n) :
    IsGoodIncreasingCrossing mu nu
      (positiveCrossingOccupationBranch mu nu n h) h := by
  change
    (positiveCrossingOccupationBranch mu nu n h, h) ∈
      positiveCrossingRelation mu nu
  rw [← (measurablePositiveCrossingDecomposition mu nu).iUnion_piece]
  exact mem_iUnion.2
    ⟨n, positiveCrossingOccupationBranch_mem_piece mu nu n hh⟩

private theorem positiveCrossingOccupationBranch_bijOn
    (mu nu : FiniteMeasure Real) (s : Set Real) (h : Real) :
    BijOn (fun n => positiveCrossingOccupationBranch mu nu n h)
      {n |
        h ∈ positiveCrossingOccupationLevelSet mu nu n ∧
          positiveCrossingOccupationBranch mu nu n h ∈ s}
      (positiveCrossingFiber mu nu s h) := by
  let decomposition := measurablePositiveCrossingDecomposition mu nu
  refine BijOn.mk ?_ ?_ ?_
  · intro n hn
    exact
      ⟨hn.2, positiveCrossingOccupationBranch_good mu nu n hn.1⟩
  · intro n hn m hm hnm
    by_contra hne
    have hpn :=
      positiveCrossingOccupationBranch_mem_piece mu nu n hn.1
    have hpm :=
      positiveCrossingOccupationBranch_mem_piece mu nu m hm.1
    have hpm' :
        (positiveCrossingOccupationBranch mu nu n h, h) ∈
          decomposition.piece m := by
      simpa only [decomposition, hnm] using hpm
    exact
      (Set.disjoint_left.1
        (decomposition.pairwise_disjoint hne)) hpn hpm'
  · intro x hx
    have hxUnion :
        (x, h) ∈ ⋃ n, decomposition.piece n := by
      rw [decomposition.iUnion_piece]
      exact hx.2
    rcases mem_iUnion.1 hxUnion with ⟨n, hxn⟩
    have hhLevel :
        h ∈ positiveCrossingOccupationLevelSet mu nu n :=
      ⟨(x, h), hxn, rfl⟩
    have hBranch :
        positiveCrossingOccupationBranch mu nu n h = x := by
      simpa only using
        (positiveCrossingOccupationBranch_spec mu nu n).2 (x, h) hxn
    exact ⟨n, ⟨hhLevel, hBranch ▸ hx.1⟩, hBranch⟩

private theorem positiveCrossingOccupationBranch_count
    (mu nu : FiniteMeasure Real) (s : Set Real) (h : Real) :
    (∑' n,
        {u |
          u ∈ positiveCrossingOccupationLevelSet mu nu n ∧
            positiveCrossingOccupationBranch mu nu n u ∈ s}.indicator
          (fun _ => (1 : ENNReal)) h) =
      ((positiveCrossingFiber mu nu s h).encard : ENNReal) := by
  let active : Set Nat :=
    {n |
      h ∈ positiveCrossingOccupationLevelSet mu nu n ∧
        positiveCrossingOccupationBranch mu nu n h ∈ s}
  have hBij :
      BijOn (fun n => positiveCrossingOccupationBranch mu nu n h)
        active (positiveCrossingFiber mu nu s h) := by
    simpa only [active] using
      positiveCrossingOccupationBranch_bijOn mu nu s h
  calc
    (∑' n,
        {u |
          u ∈ positiveCrossingOccupationLevelSet mu nu n ∧
            positiveCrossingOccupationBranch mu nu n u ∈ s}.indicator
          (fun _ => (1 : ENNReal)) h) =
        ∑' _ : active, (1 : ENNReal) := by
      symm
      simpa only [active, Set.mem_setOf_eq] using
        (tsum_subtype active (fun _ : Nat => (1 : ENNReal)))
    _ = (active.encard : ENNReal) :=
      ENNReal.tsum_set_one active
    _ = ((positiveCrossingFiber mu nu s h).encard : ENNReal) := by
      rw [Set.encard_congr hBij.equiv]

/-- The measure obtained by integrating every good increasing crossing once
against Lebesgue measure in the level coordinate. -/
noncomputable def positiveCrossingOccupationMeasure
    (mu nu : FiniteMeasure Real) : Measure Real :=
  Measure.sum fun n =>
    Measure.map (positiveCrossingOccupationBranch mu nu n)
      ((volume : Measure Real).restrict
        (positiveCrossingOccupationLevelSet mu nu n))

/-- On measurable sets, the canonical occupation measure is exactly the
integral of the extended cardinality of the positive-crossing fibers. -/
theorem positiveCrossingOccupationMeasure_apply
    (mu nu : FiniteMeasure Real) {s : Set Real}
    (hs : MeasurableSet s) :
    positiveCrossingOccupationMeasure mu nu s =
      ∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)
        ∂(volume : Measure Real) := by
  have hActiveMeasurable (n : Nat) :
      MeasurableSet
        {h |
          h ∈ positiveCrossingOccupationLevelSet mu nu n ∧
            positiveCrossingOccupationBranch mu nu n h ∈ s} :=
    (measurableSet_positiveCrossingOccupationLevelSet mu nu n).inter
      (hs.preimage
        (measurable_positiveCrossingOccupationBranch mu nu n))
  calc
    positiveCrossingOccupationMeasure mu nu s =
        ∑' n,
          Measure.map (positiveCrossingOccupationBranch mu nu n)
            ((volume : Measure Real).restrict
              (positiveCrossingOccupationLevelSet mu nu n)) s := by
      rw [positiveCrossingOccupationMeasure, Measure.sum_apply _ hs]
    _ = ∑' n,
        (volume : Measure Real)
          {h |
            h ∈ positiveCrossingOccupationLevelSet mu nu n ∧
              positiveCrossingOccupationBranch mu nu n h ∈ s} := by
      apply tsum_congr
      intro n
      rw [Measure.map_apply
          (measurable_positiveCrossingOccupationBranch mu nu n) hs,
        Measure.restrict_apply
          (hs.preimage
            (measurable_positiveCrossingOccupationBranch mu nu n))]
      congr 1
      ext h
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, and_comm]
    _ = ∑' n,
        ∫⁻ h,
          {u |
            u ∈ positiveCrossingOccupationLevelSet mu nu n ∧
              positiveCrossingOccupationBranch mu nu n u ∈ s}.indicator
            (fun _ => (1 : ENNReal)) h
          ∂(volume : Measure Real) := by
      apply tsum_congr
      intro n
      exact (lintegral_indicator_one (hActiveMeasurable n)).symm
    _ = ∫⁻ h,
        ∑' n,
          {u |
            u ∈ positiveCrossingOccupationLevelSet mu nu n ∧
              positiveCrossingOccupationBranch mu nu n u ∈ s}.indicator
            (fun _ => (1 : ENNReal)) h
        ∂(volume : Measure Real) := by
      symm
      apply lintegral_tsum
      intro n
      exact
        (measurable_const.indicator
          (hActiveMeasurable n)).aemeasurable
    _ = ∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)
        ∂(volume : Measure Real) :=
      lintegral_congr
        (positiveCrossingOccupationBranch_count mu nu s)

/-- The total positive-crossing occupation is finite. -/
theorem positiveCrossingOccupationMeasure_univ_ne_top
    (mu nu : FiniteMeasure Real) :
    positiveCrossingOccupationMeasure mu nu univ ≠ ∞ := by
  rw [positiveCrossingOccupationMeasure_apply mu nu MeasurableSet.univ]
  exact positiveCrossingOccupationFinite mu nu univ

noncomputable instance positiveCrossingOccupationMeasure_isFinite
    (mu nu : FiniteMeasure Real) :
    IsFiniteMeasure (positiveCrossingOccupationMeasure mu nu) where
  measure_univ_lt_top :=
    (positiveCrossingOccupationMeasure_univ_ne_top mu nu).lt_top

end

end ConcaveOTLimit
