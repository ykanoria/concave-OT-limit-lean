import Mathlib
import Theorems.Thm_ConcaveOTLimit_cumulativeMassClockExceptionalSetsCountable
import Theorems.Thm_ConcaveOTLimit_existsSignedCumulativeLipschitzMassClockFactor
import Theorems.Thm_ConcaveOTLimit_lipschitzCriticalValuesNull
import Theorems.Thm_ConcaveOTLimit_signedCumulativeMassClockJumpInterpolation
import Theorems.Thm_ConcaveOTLimit_strictCrossingOfHasDerivAtNeZero

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ConcaveOTLimit

private noncomputable def indicatrixGrid (m k i : Nat) : Real :=
  -((m : Real) + 1) +
    2 * ((m : Real) + 1) * (i : Real) / ((k : Real) + 1)

private noncomputable def indicatrixMesh (m k : Nat) : Real :=
  2 * ((m : Real) + 1) / ((k : Real) + 1)

private lemma indicatrixGrid_monotone (m k : Nat) :
    Monotone (indicatrixGrid m k) := by
  intro i j hij
  unfold indicatrixGrid
  gcongr

private lemma indicatrixGrid_succ (m k i : Nat) :
    indicatrixGrid m k (i + 1) - indicatrixGrid m k i =
      indicatrixMesh m k := by
  unfold indicatrixGrid indicatrixMesh
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private lemma exists_indicatrixGrid_cell
    (m k : Nat) {x : Real}
    (hx : x ∈ Icc (-(m : Real)) (m : Real)) :
    ∃ i < k + 1,
      indicatrixGrid m k i < x ∧
        x ≤ indicatrixGrid m k (i + 1) := by
  let L : Real := (m : Real) + 1
  let K : Real := (k : Real) + 1
  let q : Real := K * (x + L) / (2 * L)
  have hL : 0 < L := by positivity
  have hK : 0 < K := by positivity
  have hxLeft : -L < x := by
    dsimp only [L]
    exact lt_of_lt_of_le (by linarith) hx.1
  have hxRight : x < L := by
    dsimp only [L]
    exact lt_of_le_of_lt hx.2 (by linarith)
  have hqPos : 0 < q := by
    dsimp only [q]
    exact div_pos (mul_pos hK (by linarith)) (by positivity)
  have hqLt : q < K := by
    dsimp only [q]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * L)]
    nlinarith
  let c : Nat := ⌈q⌉₊
  have hcPos : 0 < c := by
    dsimp only [c]
    exact Nat.ceil_pos.mpr hqPos
  have hcLe : c ≤ k + 1 := by
    dsimp only [c]
    rw [Nat.ceil_le]
    simpa only [K, Nat.cast_add, Nat.cast_one] using hqLt.le
  let i := c - 1
  have hiSucc : i + 1 = c := Nat.sub_add_cancel hcPos
  have hiLtC : i < c := by omega
  have hiLtQ : (i : Real) < q := by
    exact (Nat.lt_ceil (α := Real)).mp
      (hiLtC.trans_eq (show c = ⌈q⌉₊ by rfl))
  have hqLeC : q ≤ (c : Real) := Nat.le_ceil q
  refine ⟨i, by omega, ?_, ?_⟩
  · change -L + 2 * L * (i : Real) / K < x
    calc
      -L + 2 * L * (i : Real) / K <
          -L + 2 * L * q / K := by gcongr
      _ = x := by
        dsimp only [q]
        field_simp
        ring
  · change x ≤ -L + 2 * L * ((i + 1 : Nat) : Real) / K
    calc
      x = -L + 2 * L * q / K := by
        dsimp only [q]
        field_simp
        ring
      _ ≤ -L + 2 * L * (c : Real) / K := by gcongr
      _ = -L + 2 * L * ((i + 1 : Nat) : Real) / K := by
        rw [hiSucc]

private lemma indicatrixMesh_tendsto_zero (m : Nat) :
    Tendsto (indicatrixMesh m) atTop (𝓝 0) := by
  simpa [indicatrixMesh, Function.comp_def, Nat.cast_add,
    Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat
      (2 * ((m : Real) + 1))).comp (tendsto_add_atTop_nat 1)

private lemma completedGraph_mem_localVariationBall
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    {a x b h : Real} (hax : a < x) (hxb : x ≤ b)
    (hh : h ∈ uIcc (Function.leftLim f x) (f x)) :
    h ∈ Metric.closedBall (f a)
      (eVariationOn f (Icc a b)).toReal := by
  have hCell : BoundedVariationOn f (Icc a b) :=
    hBV.mono (subset_univ _)
  have ha : a ∈ Icc a b := ⟨le_rfl, hax.le.trans hxb⟩
  have hx : x ∈ Icc a b := ⟨hax.le, hxb⟩
  have hRight :
      dist (f x) (f a) ≤ (eVariationOn f (Icc a b)).toReal :=
    hCell.dist_le hx ha
  have hLeft :
      dist (Function.leftLim f x) (f a) ≤
        (eVariationOn f (Icc a b)).toReal := by
    apply le_of_tendsto
      ((hBV.tendsto_leftLim x).dist tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsLT hax] with y hy
    exact hCell.dist_le
      ⟨hy.1.le, hy.2.le.trans hxb⟩ ha
  rw [Metric.mem_closedBall, Real.dist_eq]
  rw [Real.dist_eq] at hRight hLeft
  rcases abs_le.mp hRight with ⟨hRightLower, hRightUpper⟩
  rcases abs_le.mp hLeft with ⟨hLeftLower, hLeftUpper⟩
  rcases le_total (Function.leftLim f x) (f x) with hOrder | hOrder
  · rw [uIcc_of_le hOrder] at hh
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2]
  · rw [uIcc_of_ge hOrder] at hh
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2]

private noncomputable def indicatrixCellLevels
    (f : Real → Real) (m k i : Nat) : Set Real :=
  Metric.closedBall (f (indicatrixGrid m k i))
    (eVariationOn f
      (Icc (indicatrixGrid m k i)
        (indicatrixGrid m k (i + 1)))).toReal

private noncomputable def indicatrixCrossingCount
    (f : Real → Real) (m k : Nat) (h : Real) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1),
    (indicatrixCellLevels f m k i).indicator
      (fun _ => (1 : ℝ≥0∞)) h

private def indicatrixManyCrossings
    (f : Real → Real) (m k n : Nat) : Set Real :=
  {h | (n : ℝ≥0∞) ≤ indicatrixCrossingCount f m k h}

private lemma measurable_indicatrixCrossingCount
    (f : Real → Real) (m k : Nat) :
    Measurable (indicatrixCrossingCount f m k) := by
  unfold indicatrixCrossingCount indicatrixCellLevels
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator
    Metric.isClosed_closedBall.measurableSet

private lemma volume_indicatrixCellLevels
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m k i : Nat) :
    volume (indicatrixCellLevels f m k i) =
      2 * eVariationOn f
        (Icc (indicatrixGrid m k i)
          (indicatrixGrid m k (i + 1))) := by
  have hCell :
      BoundedVariationOn f
        (Icc (indicatrixGrid m k i)
          (indicatrixGrid m k (i + 1))) :=
    hBV.mono (subset_univ _)
  rw [indicatrixCellLevels, Real.volume_closedBall,
    ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hCell]

private lemma lintegral_indicatrixCrossingCount_le
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m k : Nat) :
    ∫⁻ h, indicatrixCrossingCount f m k h ∂volume ≤
      2 * eVariationOn f univ := by
  calc
    (∫⁻ h, indicatrixCrossingCount f m k h ∂volume) =
        ∑ i ∈ Finset.range (k + 1),
          volume (indicatrixCellLevels f m k i) := by
      simp only [indicatrixCrossingCount]
      rw [lintegral_finsetSum (Finset.range (k + 1))]
      · apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_indicator_one
          Metric.isClosed_closedBall.measurableSet
      · intro i hi
        exact measurable_const.indicator
          Metric.isClosed_closedBall.measurableSet
    _ = 2 * ∑ i ∈ Finset.range (k + 1),
          eVariationOn f
            (Icc (indicatrixGrid m k i)
              (indicatrixGrid m k (i + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact volume_indicatrixCellLevels hBV m k i
    _ = 2 * eVariationOn f
          (Icc (indicatrixGrid m k 0)
            (indicatrixGrid m k (k + 1))) := by
      rw [eVariationOn.sum' f (indicatrixGrid_monotone m k)]
    _ ≤ 2 * eVariationOn f univ := by
      gcongr
      exact eVariationOn.mono f (subset_univ _)

private lemma volume_indicatrixManyCrossings_le
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m k n : Nat) (hn : n ≠ 0) :
    volume (indicatrixManyCrossings f m k n) ≤
      (2 * eVariationOn f univ) / n := by
  rw [indicatrixManyCrossings]
  apply (meas_ge_le_lintegral_div
    (measurable_indicatrixCrossingCount f m k).aemeasurable
    (by exact_mod_cast hn)
    (ENNReal.natCast_ne_top n)).trans
  gcongr
  exact lintegral_indicatrixCrossingCount_le hBV m k

private def boundedCompletedGraphHasAtLeast
    (f : Real → Real) (m n : Nat) : Set Real :=
  {h | ∃ x : Fin n → Real,
    Function.Injective x ∧
      (∀ j, x j ∈ Icc (-(m : Real)) (m : Real)) ∧
      ∀ j, h ∈ uIcc (Function.leftLim f (x j)) (f (x j))}

private def indicatrixEventuallyManyCrossings
    (f : Real → Real) (m n : Nat) : Set Real :=
  ⋃ N, ⋂ k, ⋂ (_ : N ≤ k), indicatrixManyCrossings f m k n

private lemma boundedCompletedGraph_subset_eventuallyManyCrossings
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m n : Nat) :
    boundedCompletedGraphHasAtLeast f m n ⊆
      indicatrixEventuallyManyCrossings f m n := by
  intro h hh
  rcases hh with ⟨x, hxInjective, hxBounded, hxGraph⟩
  have hCellExists (k : Nat) (j : Fin n) :
      ∃ i, i < k + 1 ∧
        indicatrixGrid m k i < x j ∧
        x j ≤ indicatrixGrid m k (i + 1) := by
    simpa only [exists_and_left] using
      exists_indicatrixGrid_cell m k (hxBounded j)
  choose cell hCellLt hCellLeft hCellRight using hCellExists
  have hCellGraph (k : Nat) (j : Fin n) :
      h ∈ indicatrixCellLevels f m k (cell k j) := by
    unfold indicatrixCellLevels
    exact completedGraph_mem_localVariationBall hBV
      (hCellLeft k j) (hCellRight k j) (hxGraph j)
  have hCellsEventuallyInjective :
      ∀ᶠ k in atTop, Function.Injective (cell k) := by
    have hPair (j l : Fin n) (hjl : j ≠ l) :
        ∀ᶠ k in atTop, cell k j ≠ cell k l := by
      have hDistance : 0 < |x j - x l| :=
        abs_pos.mpr (sub_ne_zero.mpr (hxInjective.ne hjl))
      filter_upwards [
        (indicatrixMesh_tendsto_zero m).eventually_lt_const hDistance
      ] with k hk hEq
      have hSameRight :
          indicatrixGrid m k (cell k j + 1) =
            indicatrixGrid m k (cell k l + 1) := by
        rw [hEq]
      have hSameLeft :
          indicatrixGrid m k (cell k j) =
            indicatrixGrid m k (cell k l) := by
        rw [hEq]
      have hTooClose :
          |x j - x l| < indicatrixMesh m k := by
        rw [abs_lt]
        constructor
        · calc
            -indicatrixMesh m k =
                indicatrixGrid m k (cell k j) -
                  indicatrixGrid m k (cell k j + 1) := by
                    rw [← indicatrixGrid_succ]
                    ring
            _ < x j - x l := by
              rw [hSameLeft, hSameRight]
              linarith [hCellLeft k j, hCellRight k l]
        · calc
            x j - x l <
                indicatrixGrid m k (cell k j + 1) -
                  indicatrixGrid m k (cell k j) := by
              rw [hSameLeft, hSameRight]
              linarith [hCellRight k j, hCellLeft k l]
            _ = indicatrixMesh m k :=
              indicatrixGrid_succ m k (cell k j)
      exact (hTooClose.trans_le hk.le).false
    rw [show
      (∀ᶠ k in atTop, Function.Injective (cell k)) ↔
        ∀ j, ∀ l, ∀ᶠ k in atTop, cell k j = cell k l → j = l by
          simp only [Function.Injective, Filter.eventually_all]]
    intro j l
    by_cases hjl : j = l
    · subst l
      exact Eventually.of_forall fun _ _ => rfl
    · exact (hPair j l hjl).mono fun _ hne heq =>
        (hne heq).elim
  have hMany (k : Nat) (hCellInjective : Function.Injective (cell k)) :
      h ∈ indicatrixManyCrossings f m k n := by
    let selected : Finset Nat := Finset.univ.image (cell k)
    have hSelectedCard : selected.card = n := by
      dsimp only [selected]
      rw [Finset.card_image_iff.mpr hCellInjective.injOn,
        Finset.card_univ, Fintype.card_fin]
    have hSelectedSubset :
        selected ⊆ Finset.range (k + 1) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact Finset.mem_range.mpr (hCellLt k j)
    rw [indicatrixManyCrossings]
    change (n : ℝ≥0∞) ≤ indicatrixCrossingCount f m k h
    rw [indicatrixCrossingCount]
    calc
      (n : ℝ≥0∞) =
          ∑ i ∈ selected, (1 : ℝ≥0∞) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hSelectedCard.symm
      _ = ∑ i ∈ selected,
          (indicatrixCellLevels f m k i).indicator
            (fun _ => (1 : ℝ≥0∞)) h := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        rw [indicator_of_mem (hCellGraph k j)]
      _ ≤ ∑ i ∈ Finset.range (k + 1),
          (indicatrixCellLevels f m k i).indicator
            (fun _ => (1 : ℝ≥0∞)) h :=
        Finset.sum_le_sum_of_subset_of_nonneg hSelectedSubset
          (fun _ _ _ => zero_le)
  rcases (eventually_atTop.1 hCellsEventuallyInjective) with ⟨N, hN⟩
  rw [indicatrixEventuallyManyCrossings]
  refine mem_iUnion.2 ⟨N, ?_⟩
  refine mem_iInter.2 fun k => ?_
  refine mem_iInter.2 fun hNk => ?_
  exact hMany k (hN k hNk)

private lemma volume_indicatrixEventuallyManyCrossings_le
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m n : Nat) (hn : n ≠ 0) :
    volume (indicatrixEventuallyManyCrossings f m n) ≤
      (2 * eVariationOn f univ) / n := by
  let tail : Nat → Set Real := fun N =>
    ⋂ k, ⋂ (_ : N ≤ k), indicatrixManyCrossings f m k n
  have hTailMonotone : Monotone tail := by
    intro N M hNM h hh
    simp only [tail, mem_iInter] at hh ⊢
    intro k hMk
    exact hh k (hNM.trans hMk)
  rw [indicatrixEventuallyManyCrossings]
  change volume (⋃ N, tail N) ≤
    (2 * eVariationOn f univ) / n
  rw [hTailMonotone.measure_iUnion]
  refine iSup_le fun N => ?_
  calc
    volume (tail N) ≤
        volume (indicatrixManyCrossings f m N n) := by
      apply measure_mono
      intro h hh
      exact (mem_iInter.1 (mem_iInter.1 hh N) le_rfl)
    _ ≤ (2 * eVariationOn f univ) / n :=
      volume_indicatrixManyCrossings_le hBV m N n hn

private lemma volume_boundedCompletedGraphHasAtLeast_le
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m n : Nat) (hn : n ≠ 0) :
    volume (boundedCompletedGraphHasAtLeast f m n) ≤
      (2 * eVariationOn f univ) / n := by
  exact
    (measure_mono
      (boundedCompletedGraph_subset_eventuallyManyCrossings hBV m n)).trans
      (volume_indicatrixEventuallyManyCrossings_le hBV m n hn)

private def completedGraphHasAtLeast
    (f : Real → Real) (n : Nat) : Set Real :=
  {h | ∃ x : Fin n → Real,
    Function.Injective x ∧
      ∀ j, h ∈ uIcc (Function.leftLim f (x j)) (f (x j))}

private lemma completedGraphHasAtLeast_eq_iUnion_bounded
    (f : Real → Real) (n : Nat) :
    completedGraphHasAtLeast f n =
      ⋃ m, boundedCompletedGraphHasAtLeast f m n := by
  ext h
  constructor
  · rintro ⟨x, hxInjective, hxGraph⟩
    obtain ⟨m, hm⟩ :=
      exists_nat_gt (∑ j : Fin n, |x j|)
    refine mem_iUnion.2 ⟨m, x, hxInjective, ?_, hxGraph⟩
    intro j
    have hj :
        |x j| ≤ ∑ l : Fin n, |x l| := by
      exact Finset.single_le_sum
        (fun l _ => abs_nonneg (x l)) (Finset.mem_univ j)
    have hjm : |x j| ≤ (m : Real) :=
      hj.trans hm.le
    change -(m : Real) ≤ x j ∧ x j ≤ (m : Real)
    exact abs_le.mp hjm
  · intro hh
    rcases mem_iUnion.1 hh with
      ⟨m, x, hxInjective, _hxBounded, hxGraph⟩
    exact ⟨x, hxInjective, hxGraph⟩

private lemma boundedCompletedGraphHasAtLeast_monotone
    (f : Real → Real) (n : Nat) :
    Monotone (fun m => boundedCompletedGraphHasAtLeast f m n) := by
  intro a b hab h hh
  rcases hh with ⟨x, hxInjective, hxBounded, hxGraph⟩
  have habReal : (a : Real) ≤ (b : Real) := by
    exact_mod_cast hab
  refine ⟨x, hxInjective, ?_, hxGraph⟩
  intro j
  constructor
  · linarith [(hxBounded j).1]
  · exact (hxBounded j).2.trans habReal

private lemma volume_completedGraphHasAtLeast_le
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (n : Nat) (hn : n ≠ 0) :
    volume (completedGraphHasAtLeast f n) ≤
      (2 * eVariationOn f univ) / n := by
  rw [completedGraphHasAtLeast_eq_iUnion_bounded,
    (boundedCompletedGraphHasAtLeast_monotone f n).measure_iUnion]
  exact iSup_le fun m =>
    volume_boundedCompletedGraphHasAtLeast_le hBV m n hn

private def completedGraphInfiniteLevels
    (f : Real → Real) : Set Real :=
  {h |
    {x : Real |
      h ∈ uIcc (Function.leftLim f x) (f x)}.Infinite}

private lemma completedGraphInfiniteLevels_subset_hasAtLeast
    (f : Real → Real) (n : Nat) :
    completedGraphInfiniteLevels f ⊆
      completedGraphHasAtLeast f n := by
  intro h hh
  let fiber : Set Real :=
    {x : Real |
      h ∈ uIcc (Function.leftLim f x) (f x)}
  have hFiberInfinite : fiber.Infinite := by
    simpa only [completedGraphInfiniteLevels, fiber, mem_setOf_eq] using hh
  letI : Infinite fiber := hFiberInfinite.to_subtype
  let embedding : Nat ↪ fiber := Infinite.natEmbedding fiber
  let x : Fin n → Real := fun j => (embedding j.1).1
  have hxInjective : Function.Injective x := by
    intro j l hjl
    have hEmbedding : embedding j.1 = embedding l.1 := by
      apply Subtype.ext
      simpa only [x] using hjl
    exact Fin.ext (embedding.injective hEmbedding)
  refine ⟨x, hxInjective, ?_⟩
  intro j
  simpa only [x, fiber, mem_setOf_eq] using (embedding j.1).2

private lemma volume_completedGraphInfiniteLevels_eq_zero
    {f : Real → Real} (hBV : BoundedVariationOn f univ) :
    volume (completedGraphInfiniteLevels f) = 0 := by
  let C : ℝ≥0∞ := 2 * eVariationOn f univ
  have hCne : C ≠ ∞ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num) hBV
  have hRealTendsto :
      Tendsto
        (fun n : Nat => C.toReal / ((n + 1 : Nat) : Real))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_const_div_atTop_nhds_zero_nat C.toReal).comp
        (tendsto_add_atTop_nat 1)
  have hBoundTendsto :
      Tendsto
        (fun n : Nat => C / ((n + 1 : Nat) : ℝ≥0∞))
        atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal hRealTendsto using 1
    · funext n
      rw [ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_toReal hCne, ENNReal.ofReal_natCast]
    · norm_num
  have hBounds :
      ∀ n : Nat,
        volume (completedGraphInfiniteLevels f) ≤
          C / ((n + 1 : Nat) : ℝ≥0∞) := by
    intro n
    exact
      (measure_mono
        (completedGraphInfiniteLevels_subset_hasAtLeast f (n + 1))).trans
        (by
          simpa only [C] using
            volume_completedGraphHasAtLeast_le hBV (n + 1) (by omega))
  apply le_antisymm
  · exact ge_of_tendsto hBoundTendsto
      (Eventually.of_forall hBounds)
  · exact zero_le

/-- A globally bounded-variation real function has only finitely many hits
of its completed graph at almost every level. -/
theorem completedGraphLevelFiniteAe
    {f : Real → Real} (hBV : BoundedVariationOn f univ) :
    ∀ᵐ h ∂(volume : Measure Real),
      {x : Real |
        h ∈ uIcc (Function.leftLim f x) (f x)}.Finite := by
  apply ae_iff.mpr
  simpa only [Set.not_finite, completedGraphInfiniteLevels,
    mem_setOf_eq] using
    volume_completedGraphInfiniteLevels_eq_zero hBV

/-- Almost every level of a signed cumulative function has a finite
completed-graph fiber. -/
theorem generalizedCumulativeGraphLevelFiniteAe
    (mu nu : FiniteMeasure Real) :
    ∀ᵐ h ∂(volume : Measure Real),
      {x : Real |
        (x, h) ∈ generalizedCumulativeGraph mu nu}.Finite := by
  simpa only [generalizedCumulativeGraph, mem_setOf_eq,
    (signedCumulativeRightContinuousAndLeftLim mu nu).2] using
    completedGraphLevelFiniteAe
      (signedCumulativeBoundedVariation mu nu)

private def massClockPlateauParameters
    (mu nu : FiniteMeasure Real) : Set Real :=
  {c : Real |
    ∃ x y : Real,
      x < y ∧
        cumulativeMassClock mu nu x = c ∧
          cumulativeMassClock mu nu y = c}

private lemma cumulativeMassClock_tendsto_left
    (mu nu : FiniteMeasure Real) (x : Real) :
    Tendsto (cumulativeMassClock mu nu)
      (nhdsWithin x (Iio x))
      (nhds (cumulativeMassClockLeft mu nu x)) := by
  have hCumulativeTendsto
      (eta : FiniteMeasure Real) :
      Tendsto
        (fun y : Real => (eta : Measure Real).real (Iic y))
        (nhdsWithin x (Iio x))
        (nhds ((eta : Measure Real).real (Iio x))) := by
    have hTendsto :=
      (signedCumulativeBoundedVariation eta
        (0 : FiniteMeasure Real)).tendsto_leftLim x
    rw [(signedCumulativeRightContinuousAndLeftLim eta
      (0 : FiniteMeasure Real)).2 x] at hTendsto
    have hCumulative :
        signedCumulative eta (0 : FiniteMeasure Real) =
          fun y : Real => (eta : Measure Real).real (Iic y) := by
      funext y
      simp [signedCumulative, Measure.real]
    rw [hCumulative] at hTendsto
    simpa [signedCumulative, signedCumulativeLeft, Measure.real] using
      hTendsto
  simpa only [cumulativeMassClock, cumulativeMassClockLeft] using
    (hCumulativeTendsto mu).add (hCumulativeTendsto nu)

private lemma cumulativeMassClock_continuousWithinAt_right
    (mu nu : FiniteMeasure Real) (x : Real) :
    ContinuousWithinAt (cumulativeMassClock mu nu) (Ici x) x := by
  have hCumulative
      (eta : FiniteMeasure Real) :
      signedCumulative eta (0 : FiniteMeasure Real) =
        fun y : Real => (eta : Measure Real).real (Iic y) := by
    funext y
    simp [signedCumulative, Measure.real]
  have hMu :=
    (signedCumulativeRightContinuousAndLeftLim mu
      (0 : FiniteMeasure Real)).1 x
  have hNu :=
    (signedCumulativeRightContinuousAndLeftLim nu
      (0 : FiniteMeasure Real)).1 x
  rw [hCumulative mu] at hMu
  rw [hCumulative nu] at hNu
  simpa only [cumulativeMassClock] using hMu.add hNu

private lemma cumulativeMassClockInterval_local
    (mu nu : FiniteMeasure Real) (x : Real)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ delta, 0 < delta ∧
      ∀ ⦃z t : Real⦄,
        z ∈ Ioo (x - delta) (x + delta) →
          t ∈ Icc (cumulativeMassClockLeft mu nu z)
            (cumulativeMassClock mu nu z) →
            t ∈ Ioo
              (cumulativeMassClockLeft mu nu x - epsilon)
              (cumulativeMassClock mu nu x + epsilon) := by
  have hLeftEventually :
      ∀ᶠ y in nhdsWithin x (Iio x),
        cumulativeMassClockLeft mu nu x - epsilon <
          cumulativeMassClock mu nu y :=
    (cumulativeMassClock_tendsto_left mu nu x).eventually
      (Ioi_mem_nhds
        (sub_lt_self (cumulativeMassClockLeft mu nu x) hepsilon))
  obtain ⟨a, haValue, hax⟩ :=
    (hLeftEventually.and
      (show ∀ᶠ y in nhdsWithin x (Iio x), y ∈ Iio x from
        self_mem_nhdsWithin)).exists
  have hRightTendsto :
      Tendsto (cumulativeMassClock mu nu)
        (nhdsWithin x (Ioi x))
        (nhds (cumulativeMassClock mu nu x)) :=
    (cumulativeMassClock_continuousWithinAt_right mu nu x).tendsto.mono_left
      (nhdsWithin_mono x Ioi_subset_Ici_self)
  have hRightEventually :
      ∀ᶠ y in nhdsWithin x (Ioi x),
        cumulativeMassClock mu nu y <
          cumulativeMassClock mu nu x + epsilon :=
    hRightTendsto.eventually
      (Iio_mem_nhds
        (lt_add_of_pos_right (cumulativeMassClock mu nu x) hepsilon))
  obtain ⟨b, hbValue, hxb⟩ :=
    (hRightEventually.and
      (show ∀ᶠ y in nhdsWithin x (Ioi x), y ∈ Ioi x from
        self_mem_nhdsWithin)).exists
  let delta := min (x - a) (b - x)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (sub_pos.mpr hax) (sub_pos.mpr hxb)
  refine ⟨delta, hdelta, ?_⟩
  intro z t hz ht
  have haz : a < z := by
    have hdeltaLe : delta ≤ x - a := by
      dsimp only [delta]
      exact min_le_left _ _
    linarith [hz.1]
  have hzb : z < b := by
    have hdeltaLe : delta ≤ b - x := by
      dsimp only [delta]
      exact min_le_right _ _
    linarith [hz.2]
  have hCaLeLeftZ :
      cumulativeMassClock mu nu a ≤
        cumulativeMassClockLeft mu nu z := by
    unfold cumulativeMassClock cumulativeMassClockLeft
    exact add_le_add
      (measureReal_mono (Iic_subset_Iio.mpr haz))
      (measureReal_mono (Iic_subset_Iio.mpr haz))
  have hCzLeCb :
      cumulativeMassClock mu nu z ≤
        cumulativeMassClock mu nu b := by
    unfold cumulativeMassClock
    exact add_le_add
      (measureReal_mono (Iic_subset_Iic.mpr hzb.le))
      (measureReal_mono (Iic_subset_Iic.mpr hzb.le))
  exact
    ⟨haValue.trans_le (hCaLeLeftZ.trans ht.1),
      lt_of_le_of_lt (ht.2.trans hCzLeCb) hbValue⟩

private lemma cumulativeMassClockInterval_lt_of_left
    (mu nu : FiniteMeasure Real)
    {x z t : Real}
    (hzx : z < x)
    (ht : t ∈ Icc (cumulativeMassClockLeft mu nu z)
      (cumulativeMassClock mu nu z))
    (hNotPlateau :
      cumulativeMassClock mu nu x ∉
        massClockPlateauParameters mu nu) :
    t < cumulativeMassClock mu nu x := by
  have hClockLe :
      cumulativeMassClock mu nu z ≤
        cumulativeMassClock mu nu x := by
    unfold cumulativeMassClock
    exact add_le_add
      (measureReal_mono (Iic_subset_Iic.mpr hzx.le))
      (measureReal_mono (Iic_subset_Iic.mpr hzx.le))
  have hClockNe :
      cumulativeMassClock mu nu z ≠
        cumulativeMassClock mu nu x := by
    intro hEq
    apply hNotPlateau
    exact ⟨z, x, hzx, hEq, rfl⟩
  exact ht.2.trans_lt (lt_of_le_of_ne hClockLe hClockNe)

private lemma cumulativeMassClockInterval_lt_of_right
    (mu nu : FiniteMeasure Real)
    {x z t : Real}
    (hxz : x < z)
    (ht : t ∈ Icc (cumulativeMassClockLeft mu nu z)
      (cumulativeMassClock mu nu z))
    (hNotPlateau :
      cumulativeMassClock mu nu x ∉
        massClockPlateauParameters mu nu) :
    cumulativeMassClock mu nu x < t := by
  have hClockLe :
      cumulativeMassClock mu nu x ≤
        cumulativeMassClockLeft mu nu z := by
    unfold cumulativeMassClock cumulativeMassClockLeft
    exact add_le_add
      (measureReal_mono (Iic_subset_Iio.mpr hxz))
      (measureReal_mono (Iic_subset_Iio.mpr hxz))
  have hClockNe :
      cumulativeMassClock mu nu x ≠
        cumulativeMassClockLeft mu nu z := by
    intro hEq
    let y : Real := (x + z) / 2
    have hxy : x < y := by
      dsimp only [y]
      linarith
    have hyz : y < z := by
      dsimp only [y]
      linarith
    have hLower :
        cumulativeMassClock mu nu x ≤
          cumulativeMassClock mu nu y := by
      unfold cumulativeMassClock
      exact add_le_add
        (measureReal_mono (Iic_subset_Iic.mpr hxy.le))
        (measureReal_mono (Iic_subset_Iic.mpr hxy.le))
    have hUpper :
        cumulativeMassClock mu nu y ≤
          cumulativeMassClockLeft mu nu z := by
      unfold cumulativeMassClock cumulativeMassClockLeft
      exact add_le_add
        (measureReal_mono (Iic_subset_Iio.mpr hyz))
        (measureReal_mono (Iic_subset_Iio.mpr hyz))
    have hMiddle :
        cumulativeMassClock mu nu y =
          cumulativeMassClock mu nu x :=
      le_antisymm (hUpper.trans_eq hEq.symm) hLower
    apply hNotPlateau
    exact ⟨x, y, hxy, rfl, hMiddle⟩
  exact (lt_of_le_of_ne hClockLe hClockNe).trans_le ht.1

/-- Under an atomless source, every completed signed-cumulative graph hit is
the value of the Lipschitz mass-clock factor at a parameter in the
corresponding clock interval. -/
theorem signedCumulativeCompletedGraphMassClockParameterization
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (g : Real → Real)
    (hg : LipschitzWith 1 g)
    (hFactor : ∀ x : Real,
      g (cumulativeMassClock mu nu x) =
        signedCumulative mu nu x)
    {x h : Real}
    (hGraph : (x, h) ∈ generalizedCumulativeGraph mu nu) :
    ∃ t : Real,
      t ∈ Icc (cumulativeMassClockLeft mu nu x)
        (cumulativeMassClock mu nu x) ∧
        g t = h := by
  obtain ⟨_hLeftFactor, hInterpolate⟩ :=
    signedCumulativeMassClockJumpInterpolation
      mu nu hAtomless g hg hFactor
  have hClockLe :
      cumulativeMassClockLeft mu nu x ≤
        cumulativeMassClock mu nu x := by
    unfold cumulativeMassClockLeft cumulativeMassClock
    exact add_le_add
      (measureReal_mono Iio_subset_Iic_self)
      (measureReal_mono Iio_subset_Iic_self)
  have hAtRight :=
    hInterpolate x (cumulativeMassClock mu nu x)
      ⟨hClockLe, le_rfl⟩
  rw [hFactor x] at hAtRight
  have hSignedLeLeft :
      signedCumulative mu nu x ≤
        signedCumulativeLeft mu nu x := by
    rw [hAtRight]
    linarith
  change h ∈
    uIcc (signedCumulativeLeft mu nu x)
      (signedCumulative mu nu x) at hGraph
  rw [uIcc_of_ge hSignedLeLeft] at hGraph
  let t : Real :=
    cumulativeMassClockLeft mu nu x +
      (signedCumulativeLeft mu nu x - h)
  have ht :
      t ∈ Icc (cumulativeMassClockLeft mu nu x)
        (cumulativeMassClock mu nu x) := by
    constructor
    · dsimp only [t]
      linarith [hGraph.2]
    · dsimp only [t]
      linarith [hGraph.1, hAtRight]
  refine ⟨t, ht, ?_⟩
  rw [hInterpolate x t ht]
  dsimp only [t]
  ring

private lemma goodCrossing_of_massClock_nonjump
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (g : Real → Real)
    (hg : LipschitzWith 1 g)
    (hFactor : ∀ x : Real,
      g (cumulativeMassClock mu nu x) =
        signedCumulative mu nu x)
    {x h d : Real}
    (hGraph : (x, h) ∈ generalizedCumulativeGraph mu nu)
    (hNoJump :
      cumulativeMassClockLeft mu nu x =
        cumulativeMassClock mu nu x)
    (hNotPlateau :
      cumulativeMassClock mu nu x ∉
        massClockPlateauParameters mu nu)
    (hValue :
      g (cumulativeMassClock mu nu x) = h)
    (hDeriv :
      HasDerivAt g d (cumulativeMassClock mu nu x))
    (hd : d ≠ 0) :
    IsGoodIncreasingCrossing mu nu x h ∨
      IsGoodDecreasingCrossing mu nu x h := by
  rcases strictCrossingOfHasDerivAtNeZero hDeriv hd with
      hIncreasing | hDecreasing
  · rcases hIncreasing with
      ⟨_hdPositive, epsilon, hepsilon, hParameterCrossing⟩
    obtain ⟨delta, hdelta, hLocal⟩ :=
      cumulativeMassClockInterval_local mu nu x hepsilon
    refine Or.inl ⟨hGraph, delta, hdelta, ?_⟩
    intro z h' hz hzx hGraph'
    obtain ⟨t, ht, hgt⟩ :=
      signedCumulativeCompletedGraphMassClockParameterization
        mu nu hAtomless g hg hFactor hGraph'
    have htNearRaw := hLocal hz ht
    have htNear :
        t ∈ Ioo
          (cumulativeMassClock mu nu x - epsilon)
          (cumulativeMassClock mu nu x + epsilon) := by
      simpa only [hNoJump] using htNearRaw
    rcases lt_or_gt_of_ne hzx with hzxLeft | hxzRight
    · have htLeft :
          t < cumulativeMassClock mu nu x :=
        cumulativeMassClockInterval_lt_of_left
          mu nu hzxLeft ht hNotPlateau
      have hParameter :=
        hParameterCrossing t htNear htLeft.ne
      have hgLeft :
          g t - g (cumulativeMassClock mu nu x) < 0 := by
        rcases (mul_pos_iff.mp hParameter) with
            ⟨_hgPositive, htPositive⟩ | ⟨hgNegative, _htNegative⟩
        · exact (not_lt_of_ge htLeft.le
            (sub_pos.mp htPositive)).elim
        · exact hgNegative
      rw [← hgt, ← hValue]
      exact mul_pos_of_neg_of_neg hgLeft (sub_neg.mpr hzxLeft)
    · have htRight :
          cumulativeMassClock mu nu x < t :=
        cumulativeMassClockInterval_lt_of_right
          mu nu hxzRight ht hNotPlateau
      have hParameter :=
        hParameterCrossing t htNear htRight.ne'
      have hgRight :
          0 < g t - g (cumulativeMassClock mu nu x) := by
        rcases (mul_pos_iff.mp hParameter) with
            ⟨hgPositive, _htPositive⟩ | ⟨_hgNegative, htNegative⟩
        · exact hgPositive
        · exact (not_lt_of_ge htRight.le
            (sub_neg.mp htNegative)).elim
      rw [← hgt, ← hValue]
      exact mul_pos hgRight (sub_pos.mpr hxzRight)
  · rcases hDecreasing with
      ⟨_hdNegative, epsilon, hepsilon, hParameterCrossing⟩
    obtain ⟨delta, hdelta, hLocal⟩ :=
      cumulativeMassClockInterval_local mu nu x hepsilon
    refine Or.inr ⟨hGraph, delta, hdelta, ?_⟩
    intro z h' hz hzx hGraph'
    obtain ⟨t, ht, hgt⟩ :=
      signedCumulativeCompletedGraphMassClockParameterization
        mu nu hAtomless g hg hFactor hGraph'
    have htNearRaw := hLocal hz ht
    have htNear :
        t ∈ Ioo
          (cumulativeMassClock mu nu x - epsilon)
          (cumulativeMassClock mu nu x + epsilon) := by
      simpa only [hNoJump] using htNearRaw
    rcases lt_or_gt_of_ne hzx with hzxLeft | hxzRight
    · have htLeft :
          t < cumulativeMassClock mu nu x :=
        cumulativeMassClockInterval_lt_of_left
          mu nu hzxLeft ht hNotPlateau
      have hParameter :=
        hParameterCrossing t htNear htLeft.ne
      have hgLeft :
          0 < g t - g (cumulativeMassClock mu nu x) := by
        rcases (mul_neg_iff.mp hParameter) with
            ⟨hgPositive, _htNegative⟩ | ⟨_hgNegative, htPositive⟩
        · exact hgPositive
        · exact (not_lt_of_ge htLeft.le
            (sub_pos.mp htPositive)).elim
      rw [← hgt, ← hValue]
      exact mul_neg_of_pos_of_neg hgLeft (sub_neg.mpr hzxLeft)
    · have htRight :
          cumulativeMassClock mu nu x < t :=
        cumulativeMassClockInterval_lt_of_right
          mu nu hxzRight ht hNotPlateau
      have hParameter :=
        hParameterCrossing t htNear htRight.ne'
      have hgRight :
          g t - g (cumulativeMassClock mu nu x) < 0 := by
        rcases (mul_neg_iff.mp hParameter) with
            ⟨_hgPositive, htNegative⟩ | ⟨hgNegative, _htPositive⟩
        · exact (not_lt_of_ge htRight.le
            (sub_neg.mp htNegative)).elim
        · exact hgNegative
      rw [← hgt, ← hValue]
      exact mul_neg_of_neg_of_pos hgRight (sub_pos.mpr hxzRight)

private lemma goodDecreasingCrossing_of_massClock_jump
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (g : Real → Real)
    (hg : LipschitzWith 1 g)
    (hFactor : ∀ x : Real,
      g (cumulativeMassClock mu nu x) =
        signedCumulative mu nu x)
    {x h : Real}
    (hGraph : (x, h) ∈ generalizedCumulativeGraph mu nu)
    (hJump :
      cumulativeMassClockLeft mu nu x <
        cumulativeMassClock mu nu x)
    (hNeLeft : h ≠ signedCumulativeLeft mu nu x)
    (hNeRight : h ≠ signedCumulative mu nu x) :
    IsGoodDecreasingCrossing mu nu x h := by
  obtain ⟨hLeftFactor, hInterpolate⟩ :=
    signedCumulativeMassClockJumpInterpolation
      mu nu hAtomless g hg hFactor
  have hAtRight :=
    hInterpolate x (cumulativeMassClock mu nu x)
      ⟨hJump.le, le_rfl⟩
  rw [hFactor x] at hAtRight
  have hSignedLeLeft :
      signedCumulative mu nu x ≤
        signedCumulativeLeft mu nu x := by
    rw [hAtRight]
    linarith
  have hGraphLevels := hGraph
  change h ∈
    uIcc (signedCumulativeLeft mu nu x)
      (signedCumulative mu nu x) at hGraphLevels
  rw [uIcc_of_ge hSignedLeLeft] at hGraphLevels
  have hAboveRight :
      signedCumulative mu nu x < h :=
    lt_of_le_of_ne hGraphLevels.1 (Ne.symm hNeRight)
  have hBelowLeft :
      h < signedCumulativeLeft mu nu x :=
    lt_of_le_of_ne hGraphLevels.2 hNeLeft
  have hLeftGap :
      0 <
        g (cumulativeMassClockLeft mu nu x) - h := by
    rw [hLeftFactor x]
    exact sub_pos.mpr hBelowLeft
  have hRightGap :
      0 <
        h - g (cumulativeMassClock mu nu x) := by
    rw [hFactor x]
    exact sub_pos.mpr hAboveRight
  let epsilon :=
    min
      (g (cumulativeMassClockLeft mu nu x) - h)
      (h - g (cumulativeMassClock mu nu x))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min hLeftGap hRightGap
  obtain ⟨delta, hdelta, hLocal⟩ :=
    cumulativeMassClockInterval_local mu nu x hepsilon
  refine ⟨hGraph, delta, hdelta, ?_⟩
  intro z h' hz hzx hGraph'
  obtain ⟨t, ht, hgt⟩ :=
    signedCumulativeCompletedGraphMassClockParameterization
      mu nu hAtomless g hg hFactor hGraph'
  have htNear := hLocal hz ht
  rcases lt_or_gt_of_ne hzx with hzxLeft | hxzRight
  · have hClockOrder :
        cumulativeMassClock mu nu z ≤
          cumulativeMassClockLeft mu nu x := by
      unfold cumulativeMassClock cumulativeMassClockLeft
      exact add_le_add
        (measureReal_mono (Iic_subset_Iio.mpr hzxLeft))
        (measureReal_mono (Iic_subset_Iio.mpr hzxLeft))
    have htLe :
        t ≤ cumulativeMassClockLeft mu nu x :=
      ht.2.trans hClockOrder
    have htDistance :
        |t - cumulativeMassClockLeft mu nu x| < epsilon := by
      rw [abs_of_nonpos (sub_nonpos.mpr htLe)]
      linarith [htNear.1]
    have htGap :
        |t - cumulativeMassClockLeft mu nu x| <
          g (cumulativeMassClockLeft mu nu x) - h :=
      htDistance.trans_le (min_le_left _ _)
    have hgDistance :=
      hg.dist_le_mul t (cumulativeMassClockLeft mu nu x)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hgDistance
    have hgGap :
        |g t - g (cumulativeMassClockLeft mu nu x)| <
          g (cumulativeMassClockLeft mu nu x) - h :=
      hgDistance.trans_lt htGap
    have hAbove : h < g t := by
      have hLower := (abs_lt.mp hgGap).1
      linarith
    rw [← hgt]
    exact mul_neg_of_pos_of_neg
      (sub_pos.mpr hAbove) (sub_neg.mpr hzxLeft)
  · have hClockOrder :
        cumulativeMassClock mu nu x ≤
          cumulativeMassClockLeft mu nu z := by
      unfold cumulativeMassClock cumulativeMassClockLeft
      exact add_le_add
        (measureReal_mono (Iic_subset_Iio.mpr hxzRight))
        (measureReal_mono (Iic_subset_Iio.mpr hxzRight))
    have htGe :
        cumulativeMassClock mu nu x ≤ t :=
      hClockOrder.trans ht.1
    have htDistance :
        |t - cumulativeMassClock mu nu x| < epsilon := by
      rw [abs_of_nonneg (sub_nonneg.mpr htGe)]
      linarith [htNear.2]
    have htGap :
        |t - cumulativeMassClock mu nu x| <
          h - g (cumulativeMassClock mu nu x) :=
      htDistance.trans_le (min_le_right _ _)
    have hgDistance :=
      hg.dist_le_mul t (cumulativeMassClock mu nu x)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hgDistance
    have hgGap :
        |g t - g (cumulativeMassClock mu nu x)| <
          h - g (cumulativeMassClock mu nu x) :=
      hgDistance.trans_lt htGap
    have hBelow : g t < h := by
      have hUpper := (abs_lt.mp hgGap).2
      linarith
    rw [← hgt]
    exact mul_neg_of_neg_of_pos
      (sub_neg.mpr hBelow) (sub_pos.mpr hxzRight)

/-- The mass-clock parameters and completed-graph endpoint levels at which
the direct regular-crossing argument can fail. -/
def massClockRegularityExceptionalLevels
    (mu nu : FiniteMeasure Real) (g : Real → Real) : Set Real :=
  g '' massClockPlateauParameters mu nu ∪
    ((signedCumulative mu nu ''
        {x : Real |
          cumulativeMassClockLeft mu nu x <
            cumulativeMassClock mu nu x} ∪
      signedCumulativeLeft mu nu ''
        {x : Real |
          cumulativeMassClockLeft mu nu x <
            cumulativeMassClock mu nu x}) ∪
      (g '' {t : Real | ¬ DifferentiableAt Real g t} ∪
        g '' {t : Real | HasDerivAt g 0 t}))

/-- Plateau parameters, jump endpoint levels, and Lipschitz critical values
transport to a Lebesgue-null set of completed-graph levels. -/
theorem massClockRegularityExceptionalLevelsNull
    (mu nu : FiniteMeasure Real)
    {g : Real → Real}
    (hg : LipschitzWith 1 g) :
    volume (massClockRegularityExceptionalLevels mu nu g) = 0 := by
  obtain ⟨hPlateauCountable, _hJumpPointsCountable,
      _hJumpLevelsCountable, hJumpLevelsNull⟩ :=
    cumulativeMassClockExceptionalSetsCountable mu nu
  have hPlateauLevelsNull :
      volume
        (g '' massClockPlateauParameters mu nu) = 0 := by
    apply (hPlateauCountable.image g).measure_zero volume
  have hCriticalLevelsNull :
      volume
        (g '' {t : Real | ¬ DifferentiableAt Real g t} ∪
          g '' {t : Real | HasDerivAt g 0 t}) = 0 :=
    lipschitzCriticalValuesNull hg
  unfold massClockRegularityExceptionalLevels
  exact measure_union_null hPlateauLevelsNull
    (measure_union_null hJumpLevelsNull hCriticalLevelsNull)

/-- Outside the explicit mass-clock exceptional levels, every completed
signed-cumulative graph hit is a good crossing. -/
theorem massClockRegularityOutsideExceptionalLevels
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    (g : Real → Real)
    (hg : LipschitzWith 1 g)
    (hFactor : ∀ x : Real,
      g (cumulativeMassClock mu nu x) =
        signedCumulative mu nu x)
    {h : Real}
    (hRegular :
      h ∉ massClockRegularityExceptionalLevels mu nu g) :
    ∀ x : Real,
      (x, h) ∈ generalizedCumulativeGraph mu nu →
        IsGoodIncreasingCrossing mu nu x h ∨
          IsGoodDecreasingCrossing mu nu x h := by
  simp only [massClockRegularityExceptionalLevels, mem_union,
    not_or] at hRegular
  rcases hRegular with
    ⟨hNotPlateauLevel,
      ⟨⟨hNotRightJumpLevel, hNotLeftJumpLevel⟩,
        ⟨hNotNondifferentiableLevel, hNotZeroDerivativeLevel⟩⟩⟩
  intro x hGraph
  have hClockLe :
      cumulativeMassClockLeft mu nu x ≤
        cumulativeMassClock mu nu x := by
    unfold cumulativeMassClockLeft cumulativeMassClock
    exact add_le_add
      (measureReal_mono Iio_subset_Iic_self)
      (measureReal_mono Iio_subset_Iic_self)
  rcases hClockLe.eq_or_lt with hNoJump | hJump
  · obtain ⟨t, ht, hgt⟩ :=
      signedCumulativeCompletedGraphMassClockParameterization
        mu nu hAtomless g hg hFactor hGraph
    have htEq :
        t = cumulativeMassClock mu nu x :=
      le_antisymm ht.2 (hNoJump ▸ ht.1)
    have hValue :
        g (cumulativeMassClock mu nu x) = h := by
      rw [← htEq]
      exact hgt
    have hNotPlateau :
        cumulativeMassClock mu nu x ∉
          massClockPlateauParameters mu nu := by
      intro hPlateau
      exact hNotPlateauLevel
        ⟨cumulativeMassClock mu nu x, hPlateau, hValue⟩
    have hDifferentiable :
        DifferentiableAt Real g
          (cumulativeMassClock mu nu x) := by
      by_contra hNotDifferentiable
      exact hNotNondifferentiableLevel
        ⟨cumulativeMassClock mu nu x,
          hNotDifferentiable, hValue⟩
    have hDeriv :
        HasDerivAt g
          (deriv g (cumulativeMassClock mu nu x))
          (cumulativeMassClock mu nu x) :=
      hDifferentiable.hasDerivAt
    have hDerivNe :
        deriv g (cumulativeMassClock mu nu x) ≠ 0 := by
      intro hZero
      apply hNotZeroDerivativeLevel
      refine ⟨cumulativeMassClock mu nu x, ?_, hValue⟩
      simpa only [hZero] using hDeriv
    exact goodCrossing_of_massClock_nonjump
      mu nu hAtomless g hg hFactor hGraph hNoJump
        hNotPlateau hValue hDeriv hDerivNe
  · have hNeLeft :
        h ≠ signedCumulativeLeft mu nu x := by
      intro hEq
      exact hNotLeftJumpLevel ⟨x, hJump, hEq.symm⟩
    have hNeRight :
        h ≠ signedCumulative mu nu x := by
      intro hEq
      exact hNotRightJumpLevel ⟨x, hJump, hEq.symm⟩
    exact Or.inr
      (goodDecreasingCrossing_of_massClock_jump
        mu nu hAtomless g hg hFactor hGraph hJump
          hNeLeft hNeRight)

/-- The finite-fiber, mass-clock parameterization, and null-exception
conclusions available before the final local crossing-transport step. -/
theorem existsSignedCumulativeMassClockRegularityPackage
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu) :
    ∃ g : Real → Real,
      LipschitzWith 1 g ∧
        (∀ x : Real,
          g (cumulativeMassClock mu nu x) =
            signedCumulative mu nu x) ∧
        volume (massClockRegularityExceptionalLevels mu nu g) = 0 ∧
        (∀ᵐ h ∂(volume : Measure Real),
          {x : Real |
            (x, h) ∈ generalizedCumulativeGraph mu nu}.Finite) ∧
        ∀ ⦃x h : Real⦄,
          (x, h) ∈ generalizedCumulativeGraph mu nu →
            ∃ t : Real,
              t ∈ Icc (cumulativeMassClockLeft mu nu x)
                (cumulativeMassClock mu nu x) ∧
                g t = h := by
  obtain ⟨_hClockMonotone, _hSharp, g, hg, hFactor⟩ :=
    existsSignedCumulativeLipschitzMassClockFactor mu nu
  refine ⟨g, hg, hFactor,
    massClockRegularityExceptionalLevelsNull mu nu hg,
    generalizedCumulativeGraphLevelFiniteAe mu nu, ?_⟩
  intro x h hGraph
  exact signedCumulativeCompletedGraphMassClockParameterization
    mu nu hAtomless g hg hFactor hGraph

/-- For almost every level, the completed signed-cumulative graph has a
finite fiber and every hit in that fiber is a good crossing. -/
theorem generalizedCumulativeGraphFiniteAndRegularAe
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu) :
    ∀ᵐ h ∂(volume : Measure Real),
      {x : Real |
        (x, h) ∈ generalizedCumulativeGraph mu nu}.Finite ∧
      ∀ x : Real,
        (x, h) ∈ generalizedCumulativeGraph mu nu →
          IsGoodIncreasingCrossing mu nu x h ∨
            IsGoodDecreasingCrossing mu nu x h := by
  obtain ⟨g, hg, hFactor, hExceptionalNull,
      hFinite, _hParameterization⟩ :=
    existsSignedCumulativeMassClockRegularityPackage
      mu nu hAtomless
  rw [measure_eq_zero_iff_ae_notMem] at hExceptionalNull
  filter_upwards [hFinite, hExceptionalNull] with
      h hFiniteLevel hRegular
  exact ⟨hFiniteLevel,
    massClockRegularityOutsideExceptionalLevels
      mu nu hAtomless g hg hFactor hRegular⟩

/-- Every completed signed-cumulative graph hit is a good crossing for
Lebesgue-almost every level. This is the regularity input used by C157. -/
theorem generalizedCumulativeGraphRegularAe
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu) :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ x : Real,
        (x, h) ∈ generalizedCumulativeGraph mu nu →
          IsGoodIncreasingCrossing mu nu x h ∨
            IsGoodDecreasingCrossing mu nu x h :=
  (generalizedCumulativeGraphFiniteAndRegularAe
    mu nu hAtomless).mono fun _ hRegular => hRegular.2

end ConcaveOTLimit
