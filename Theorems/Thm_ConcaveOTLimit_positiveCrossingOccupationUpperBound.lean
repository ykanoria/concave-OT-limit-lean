import Theorems.Thm_ConcaveOTLimit_positiveCrossingOccupationFinite
import Theorems.Thm_ConcaveOTLimit_goodIncreasingCrossingLevelEqOfAtomlessAt
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Interval.Set.Union

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace ConcaveOTLimit

noncomputable section

private def positiveOccupationGrid
    (a b : Real) (k i : Nat) : Real :=
  a + (b - a) * (i : Real) / ((k : Real) + 1)

private def positiveOccupationMesh
    (a b : Real) (k : Nat) : Real :=
  (b - a) / ((k : Real) + 1)

private lemma positiveOccupationGrid_monotone
    {a b : Real} (hab : a ≤ b) (k : Nat) :
    Monotone (positiveOccupationGrid a b k) := by
  intro i j hij
  unfold positiveOccupationGrid
  gcongr

private lemma positiveOccupationGrid_succ
    (a b : Real) (k i : Nat) :
    positiveOccupationGrid a b k (i + 1) -
        positiveOccupationGrid a b k i =
      positiveOccupationMesh a b k := by
  unfold positiveOccupationGrid positiveOccupationMesh
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private lemma positiveOccupationGrid_zero
    (a b : Real) (k : Nat) :
    positiveOccupationGrid a b k 0 = a := by
  simp [positiveOccupationGrid]

private lemma positiveOccupationGrid_last
    (a b : Real) (k : Nat) :
    positiveOccupationGrid a b k (k + 1) = b := by
  unfold positiveOccupationGrid
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private lemma positiveOccupationMesh_pos
    {a b : Real} (hab : a < b) (k : Nat) :
    0 < positiveOccupationMesh a b k := by
  unfold positiveOccupationMesh
  positivity

private lemma positiveOccupationMesh_tendsto_zero
    (a b : Real) :
    Tendsto (positiveOccupationMesh a b) atTop (nhds 0) := by
  simpa [positiveOccupationMesh, Function.comp_def, Nat.cast_add,
    Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp
      (tendsto_add_atTop_nat 1)

private lemma exists_positiveOccupationGrid_cell
    {a b x : Real} (hx : x ∈ Ioc a b)
    (k : Nat) :
    ∃ i < k + 1,
      positiveOccupationGrid a b k i < x ∧
        x ≤ positiveOccupationGrid a b k (i + 1) := by
  have hx' :
      x ∈ Ioc (positiveOccupationGrid a b k 0)
        (positiveOccupationGrid a b k (k + 1)) := by
    simpa [positiveOccupationGrid_zero, positiveOccupationGrid_last] using hx
  have hCover :=
    Ioc_subset_biUnion_Ioc (k + 1)
      (positiveOccupationGrid a b k) hx'
  rcases mem_iUnion.1 hCover with ⟨i, hCover⟩
  rcases mem_iUnion.1 hCover with ⟨hi, hCell⟩
  exact ⟨i, Finset.mem_range.1 hi, hCell⟩

private def positiveOccupationCellLevels
    (mu nu : FiniteMeasure Real) (a b : Real)
    (k i : Nat) : Set Real :=
  Ioc
    (signedCumulative mu nu (positiveOccupationGrid a b k i))
    (signedCumulative mu nu (positiveOccupationGrid a b k (i + 1)))

private def positiveOccupationGridCount
    (mu nu : FiniteMeasure Real) (a b : Real)
    (k : Nat) (h : Real) : ENNReal :=
  ∑ i ∈ Finset.range (k + 1),
    (positiveOccupationCellLevels mu nu a b k i).indicator
      (fun _ => (1 : ENNReal)) h

private lemma measurable_positiveOccupationGridCount
    (mu nu : FiniteMeasure Real) (a b : Real) (k : Nat) :
    Measurable (positiveOccupationGridCount mu nu a b k) := by
  unfold positiveOccupationGridCount positiveOccupationCellLevels
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator measurableSet_Ioc

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
    exact sub_le_self _ measureReal_nonneg
  calc
    ENNReal.ofReal (sigma s) ≤
        ENNReal.ofReal
          (sigma.toJordanDecomposition.posPart.real s) :=
      ENNReal.ofReal_le_ofReal hLe
    _ = sigma.toJordanDecomposition.posPart s := by
      exact ENNReal.ofReal_toReal
        (measure_ne_top sigma.toJordanDecomposition.posPart s)

private lemma positiveOccupationCells_pairwiseDisjoint
    {a b : Real} (hab : a ≤ b) (k : Nat) :
    ((Finset.range (k + 1) : Finset Nat) : Set Nat).PairwiseDisjoint
      (fun i =>
        Ioc (positiveOccupationGrid a b k i)
          (positiveOccupationGrid a b k (i + 1))) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Ioc_disjoint_Ioc_of_le
      (positiveOccupationGrid_monotone hab k (by omega))
  · exact (Ioc_disjoint_Ioc_of_le
      (positiveOccupationGrid_monotone hab k (by omega))).symm

private lemma iUnion_positiveOccupationCells
    {a b : Real} (hab : a ≤ b) (k : Nat) :
    (⋃ i ∈ (Finset.range (k + 1) : Set Nat),
        Ioc (positiveOccupationGrid a b k i)
          (positiveOccupationGrid a b k (i + 1))) =
      Ioc a b := by
  apply subset_antisymm
  · intro x hx
    rcases mem_iUnion.1 hx with ⟨i, hx⟩
    rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
    have hi' : i < k + 1 := Finset.mem_range.1 hi
    have hLeft :
        a ≤ positiveOccupationGrid a b k i := by
      calc
        a = positiveOccupationGrid a b k 0 :=
          (positiveOccupationGrid_zero a b k).symm
        _ ≤ positiveOccupationGrid a b k i :=
          positiveOccupationGrid_monotone hab k (Nat.zero_le i)
    have hRight :
        positiveOccupationGrid a b k (i + 1) ≤ b := by
      calc
        positiveOccupationGrid a b k (i + 1) ≤
            positiveOccupationGrid a b k (k + 1) :=
          positiveOccupationGrid_monotone hab k (by omega)
        _ = b := positiveOccupationGrid_last a b k
    exact ⟨hLeft.trans_lt hxi.1, hxi.2.trans hRight⟩
  · intro x hx
    apply Ioc_subset_biUnion_Ioc (k + 1)
      (positiveOccupationGrid a b k)
    simpa only [positiveOccupationGrid_zero,
      positiveOccupationGrid_last] using hx

private lemma positiveOccupationCell_increment_le_positivePart
    (mu nu : FiniteMeasure Real)
    {a b : Real} (hab : a < b) (k i : Nat) :
    volume (positiveOccupationCellLevels mu nu a b k i) ≤
      (SignedMeasure.toJordanDecomposition
        (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
          (Ioc (positiveOccupationGrid a b k i)
            (positiveOccupationGrid a b k (i + 1))) := by
  let left := positiveOccupationGrid a b k i
  let right := positiveOccupationGrid a b k (i + 1)
  have hLeftRight : left < right := by
    rw [← sub_pos, show right - left =
      positiveOccupationMesh a b k by
        exact positiveOccupationGrid_succ a b k i]
    exact positiveOccupationMesh_pos hab k
  have hVectorMeasure :
      (signedCumulativeBoundedVariation mu nu).vectorMeasure
          (Ioc left right) =
        signedCumulative mu nu right -
          signedCumulative mu nu left := by
    rw [(signedCumulativeBoundedVariation mu nu).vectorMeasure_Ioc
      hLeftRight.le]
    rw [((signedCumulativeRightContinuousAndLeftLim mu nu).1 right).rightLim_eq,
      ((signedCumulativeRightContinuousAndLeftLim mu nu).1 left).rightLim_eq]
  rw [positiveOccupationCellLevels, Real.volume_Ioc]
  change
    ENNReal.ofReal
        (signedCumulative mu nu right -
          signedCumulative mu nu left) ≤ _
  rw [← hVectorMeasure]
  exact ofReal_apply_le_posPart
    (signedCumulativeBoundedVariation mu nu).vectorMeasure
    measurableSet_Ioc

private lemma lintegral_positiveOccupationGridCount_le_positivePart
    (mu nu : FiniteMeasure Real)
    {a b : Real} (hab : a < b) (k : Nat) :
    (∫⁻ h, positiveOccupationGridCount mu nu a b k h
      ∂(volume : Measure Real)) ≤
      (SignedMeasure.toJordanDecomposition
        (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
          (Ioc a b) := by
  let rho :=
    (SignedMeasure.toJordanDecomposition
      (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
  have hDisjoint :=
    positiveOccupationCells_pairwiseDisjoint hab.le k
  calc
    (∫⁻ h, positiveOccupationGridCount mu nu a b k h
        ∂(volume : Measure Real)) =
        ∑ i ∈ Finset.range (k + 1),
          volume (positiveOccupationCellLevels mu nu a b k i) := by
      simp only [positiveOccupationGridCount]
      rw [lintegral_finsetSum (Finset.range (k + 1))]
      · apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_indicator_one measurableSet_Ioc
      · intro i hi
        exact measurable_const.indicator measurableSet_Ioc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
          rho
            (Ioc (positiveOccupationGrid a b k i)
              (positiveOccupationGrid a b k (i + 1))) := by
      exact Finset.sum_le_sum fun i hi =>
        positiveOccupationCell_increment_le_positivePart
          mu nu hab k i
    _ = rho
          (⋃ i ∈ (Finset.range (k + 1) : Set Nat),
            Ioc (positiveOccupationGrid a b k i)
              (positiveOccupationGrid a b k (i + 1))) := by
      symm
      apply measure_biUnion_finset hDisjoint
      intro i hi
      exact measurableSet_Ioc
    _ = rho (Ioc a b) := by
      rw [iUnion_positiveOccupationCells hab.le k]

private theorem signedCumulative_value_mem_graph
    (mu nu : FiniteMeasure Real) (x : Real) :
    (x, signedCumulative mu nu x) ∈
      generalizedCumulativeGraph mu nu := by
  change
    signedCumulative mu nu x ∈
      uIcc (signedCumulativeLeft mu nu x)
        (signedCumulative mu nu x)
  exact right_mem_uIcc

private lemma positiveCrossingFiber_le_liminf_grid
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    {a b h : Real}
    (hFinite :
      (positiveCrossingFiber mu nu (Ioc a b) h).Finite) :
    ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ENNReal) ≤
      liminf
        (fun k => positiveOccupationGridCount mu nu a b k h)
        atTop := by
  let points := positiveCrossingFiber mu nu (Ioc a b) h
  letI : Fintype points := hFinite.fintype
  let x : Fin (Fintype.card points) → Real :=
    fun j => ((Fintype.equivFin points).symm j).1
  have hxInjective : Injective x := by
    intro i j hij
    apply (Fintype.equivFin points).symm.injective
    apply Subtype.ext
    exact hij
  have hxMem (j : Fin (Fintype.card points)) :
      x j ∈ points :=
    ((Fintype.equivFin points).symm j).2
  have hCellExists (k : Nat) (j : Fin (Fintype.card points)) :
      ∃ i, i < k + 1 ∧
        positiveOccupationGrid a b k i < x j ∧
          x j ≤ positiveOccupationGrid a b k (i + 1) := by
    simpa only [exists_and_left] using
      exists_positiveOccupationGrid_cell (hxMem j).1 k
  choose cell hCellLt hCellLeft hCellRight using hCellExists
  have hCellEventuallyActive (j : Fin (Fintype.card points)) :
      ∀ᶠ k in atTop,
        h ∈ positiveOccupationCellLevels mu nu a b k (cell k j) := by
    have hxCrossing :
        IsGoodIncreasingCrossing mu nu (x j) h :=
      (hxMem j).2
    have hLevel :
        h = signedCumulative mu nu (x j) :=
      goodIncreasingCrossingLevelEqOfAtomlessAt
        mu nu (x j) h (hAtomless (x j)) hxCrossing
    obtain ⟨_hxGraph, epsilon, hEpsilon, hLocal⟩ := hxCrossing
    filter_upwards [
      (positiveOccupationMesh_tendsto_zero a b).eventually_lt_const hEpsilon
    ] with k hk
    let left := positiveOccupationGrid a b k (cell k j)
    let right := positiveOccupationGrid a b k (cell k j + 1)
    have hWidth :
        right - left = positiveOccupationMesh a b k := by
      exact positiveOccupationGrid_succ a b k (cell k j)
    have hLeftNear : left ∈ Ioo (x j - epsilon) (x j + epsilon) := by
      constructor
      · linarith [hCellRight k j]
      · exact (hCellLeft k j).trans
          (lt_add_of_pos_right (x j) hEpsilon)
    have hLeftNe : left ≠ x j :=
      (hCellLeft k j).ne
    have hLeftProduct :
        0 <
          (signedCumulative mu nu left - h) *
            (left - x j) :=
      hLocal hLeftNear hLeftNe
        (signedCumulative_value_mem_graph mu nu left)
    have hLeftBelow :
        signedCumulative mu nu left < h := by
      rcases mul_pos_iff.mp hLeftProduct with hSigns | hSigns
      · exact
          ((not_lt_of_ge (sub_nonpos.mpr (hCellLeft k j).le))
            hSigns.2).elim
      · exact sub_neg.mp hSigns.1
    have hRightAbove :
        h ≤ signedCumulative mu nu right := by
      by_cases hRightEq : right = x j
      · rw [hRightEq, hLevel]
      · have hxRight : x j < right :=
          lt_of_le_of_ne (hCellRight k j) (Ne.symm hRightEq)
        have hRightNear :
            right ∈ Ioo (x j - epsilon) (x j + epsilon) := by
          constructor
          · exact (sub_lt_self (x j) hEpsilon).trans_le
              (hCellRight k j)
          · linarith [hCellLeft k j]
        have hRightProduct :
            0 <
              (signedCumulative mu nu right - h) *
                (right - x j) :=
          hLocal hRightNear hRightEq
            (signedCumulative_value_mem_graph mu nu right)
        rcases mul_pos_iff.mp hRightProduct with hSigns | hSigns
        · exact (sub_pos.mp hSigns.1).le
        · exact
            ((not_lt_of_ge (sub_nonneg.mpr (hCellRight k j)))
              hSigns.2).elim
    exact ⟨hLeftBelow, hRightAbove⟩
  have hCellsEventuallyActive :
      ∀ᶠ k in atTop,
        ∀ j : Fin (Fintype.card points),
          h ∈ positiveOccupationCellLevels mu nu a b k (cell k j) := by
    rw [Filter.eventually_all]
    exact hCellEventuallyActive
  have hCellsEventuallyInjective :
      ∀ᶠ k in atTop, Injective (cell k) := by
    have hPair
        (j l : Fin (Fintype.card points)) (hjl : j ≠ l) :
        ∀ᶠ k in atTop, cell k j ≠ cell k l := by
      have hDistance : 0 < |x j - x l| :=
        abs_pos.mpr (sub_ne_zero.mpr (hxInjective.ne hjl))
      filter_upwards [
        (positiveOccupationMesh_tendsto_zero a b).eventually_lt_const hDistance
      ] with k hk hEq
      have hSameRight :
          positiveOccupationGrid a b k (cell k j + 1) =
            positiveOccupationGrid a b k (cell k l + 1) := by
        rw [hEq]
      have hSameLeft :
          positiveOccupationGrid a b k (cell k j) =
            positiveOccupationGrid a b k (cell k l) := by
        rw [hEq]
      have hTooClose :
          |x j - x l| < positiveOccupationMesh a b k := by
        rw [abs_lt]
        constructor
        · calc
            -positiveOccupationMesh a b k =
                positiveOccupationGrid a b k (cell k j) -
                  positiveOccupationGrid a b k (cell k j + 1) := by
              rw [← positiveOccupationGrid_succ]
              ring
            _ < x j - x l := by
              rw [hSameLeft, hSameRight]
              linarith [hCellLeft k j, hCellRight k l]
        · calc
            x j - x l <
                positiveOccupationGrid a b k (cell k j + 1) -
                  positiveOccupationGrid a b k (cell k j) := by
              rw [hSameLeft, hSameRight]
              linarith [hCellRight k j, hCellLeft k l]
            _ = positiveOccupationMesh a b k :=
              positiveOccupationGrid_succ a b k (cell k j)
      exact (hTooClose.trans_le hk.le).false
    rw [show
      (∀ᶠ k in atTop, Injective (cell k)) ↔
        ∀ j, ∀ l, ∀ᶠ k in atTop, cell k j = cell k l → j = l by
          simp only [Injective, Filter.eventually_all]]
    intro j l
    by_cases hjl : j = l
    · subst l
      exact Eventually.of_forall fun _ _ => rfl
    · exact (hPair j l hjl).mono fun _ hne heq =>
        (hne heq).elim
  have hCount
      (k : Nat) (hCellInjective : Injective (cell k))
      (hCellActive :
        ∀ j : Fin (Fintype.card points),
          h ∈ positiveOccupationCellLevels mu nu a b k (cell k j)) :
      ((points.encard : ENat) : ENNReal) ≤
        positiveOccupationGridCount mu nu a b k h := by
    let selected : Finset Nat :=
      Finset.univ.image (cell k)
    have hSelectedCard :
        selected.card = Fintype.card points := by
      dsimp only [selected]
      rw [Finset.card_image_iff.mpr hCellInjective.injOn,
        Finset.card_univ, Fintype.card_fin]
    have hSelectedSubset :
        selected ⊆ Finset.range (k + 1) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact Finset.mem_range.mpr (hCellLt k j)
    rw [positiveOccupationGridCount]
    calc
      ((points.encard : ENat) : ENNReal) =
          ∑ i ∈ selected, (1 : ENNReal) := by
        rw [← points.coe_fintypeCard]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hSelectedCard.symm
      _ = ∑ i ∈ selected,
          (positiveOccupationCellLevels mu nu a b k i).indicator
            (fun _ => (1 : ENNReal)) h := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        rw [indicator_of_mem (hCellActive j)]
      _ ≤ ∑ i ∈ Finset.range (k + 1),
          (positiveOccupationCellLevels mu nu a b k i).indicator
            (fun _ => (1 : ENNReal)) h :=
        Finset.sum_le_sum_of_subset_of_nonneg hSelectedSubset
          (fun _ _ _ => zero_le)
  exact le_liminf_of_le (by isBoundedDefault)
    ((hCellsEventuallyInjective.and hCellsEventuallyActive).mono
      fun k hk => hCount k hk.1 hk.2)

/-- The occupation of good increasing completed-graph crossings in `(a, b]`
is bounded by the positive Jordan mass of the canonical BV vector measure on
the same interval. -/
theorem positiveCrossingOccupation_Ioc_le_positivePart
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    {a b : Real} (hab : a < b) :
    (∫⁻ h,
        ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ENNReal)
      ∂(volume : Measure Real)) ≤
      (SignedMeasure.toJordanDecomposition
        (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
          (Ioc a b) := by
  have hFinite :=
    positiveCrossingFiberFiniteAe mu nu (Ioc a b)
  have hPointwise :
      ∀ᵐ h ∂(volume : Measure Real),
        ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ENNReal) ≤
          liminf
            (fun k => positiveOccupationGridCount mu nu a b k h)
            atTop := by
    filter_upwards [hFinite] with h hFinite
    exact positiveCrossingFiber_le_liminf_grid
      mu nu hAtomless hFinite
  calc
    (∫⁻ h,
        ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ENNReal)
      ∂(volume : Measure Real)) ≤
        ∫⁻ h,
          liminf
            (fun k => positiveOccupationGridCount mu nu a b k h)
            atTop
          ∂(volume : Measure Real) :=
      lintegral_mono_ae hPointwise
    _ ≤ liminf
          (fun k =>
            ∫⁻ h, positiveOccupationGridCount mu nu a b k h
              ∂(volume : Measure Real))
          atTop :=
      lintegral_liminf_le
        (fun k => measurable_positiveOccupationGridCount mu nu a b k)
    _ ≤
        (SignedMeasure.toJordanDecomposition
          (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart
            (Ioc a b) :=
      liminf_le_of_frequently_le'
        (Frequently.of_forall fun k =>
          lintegral_positiveOccupationGridCount_le_positivePart
            mu nu hab k)

end

end ConcaveOTLimit
