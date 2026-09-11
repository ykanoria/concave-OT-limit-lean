import Theorems.Thm_ConcaveOTLimit_measurablePositiveCrossingDecomposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace ConcaveOTLimit

noncomputable section

private def occupationGrid (m k i : Nat) : Real :=
  -((m : Real) + 1) +
    2 * ((m : Real) + 1) * (i : Real) / ((k : Real) + 1)

private def occupationMesh (m k : Nat) : Real :=
  2 * ((m : Real) + 1) / ((k : Real) + 1)

private lemma occupationGrid_monotone (m k : Nat) :
    Monotone (occupationGrid m k) := by
  intro i j hij
  unfold occupationGrid
  gcongr

private lemma occupationGrid_succ (m k i : Nat) :
    occupationGrid m k (i + 1) - occupationGrid m k i =
      occupationMesh m k := by
  unfold occupationGrid occupationMesh
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private lemma exists_occupationGrid_cell
    (m k : Nat) {x : Real}
    (hx : x ∈ Icc (-(m : Real)) (m : Real)) :
    ∃ i < k + 1,
      occupationGrid m k i < x ∧
        x ≤ occupationGrid m k (i + 1) := by
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

private lemma occupationMesh_tendsto_zero (m : Nat) :
    Tendsto (occupationMesh m) atTop (𝓝 0) := by
  simpa [occupationMesh, Function.comp_def, Nat.cast_add,
    Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat
      (2 * ((m : Real) + 1))).comp (tendsto_add_atTop_nat 1)

private lemma completedGraph_mem_occupationCell
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

private def occupationCellLevels
    (f : Real → Real) (m k i : Nat) : Set Real :=
  Metric.closedBall (f (occupationGrid m k i))
    (eVariationOn f
      (Icc (occupationGrid m k i)
        (occupationGrid m k (i + 1)))).toReal

private def occupationGridCount
    (f : Real → Real) (m k : Nat) (h : Real) : ENNReal :=
  ∑ i ∈ Finset.range (k + 1),
    (occupationCellLevels f m k i).indicator
      (fun _ => (1 : ENNReal)) h

private lemma measurable_occupationGridCount
    (f : Real → Real) (m k : Nat) :
    Measurable (occupationGridCount f m k) := by
  unfold occupationGridCount occupationCellLevels
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator
    Metric.isClosed_closedBall.measurableSet

private lemma volume_occupationCellLevels
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m k i : Nat) :
    volume (occupationCellLevels f m k i) =
      2 * eVariationOn f
        (Icc (occupationGrid m k i)
          (occupationGrid m k (i + 1))) := by
  have hCell :
      BoundedVariationOn f
        (Icc (occupationGrid m k i)
          (occupationGrid m k (i + 1))) :=
    hBV.mono (subset_univ _)
  rw [occupationCellLevels, Real.volume_closedBall,
    ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hCell]

private lemma lintegral_occupationGridCount_le
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m k : Nat) :
    ∫⁻ h, occupationGridCount f m k h ∂volume ≤
      2 * eVariationOn f univ := by
  calc
    (∫⁻ h, occupationGridCount f m k h ∂volume) =
        ∑ i ∈ Finset.range (k + 1),
          volume (occupationCellLevels f m k i) := by
      simp only [occupationGridCount]
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
            (Icc (occupationGrid m k i)
              (occupationGrid m k (i + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact volume_occupationCellLevels hBV m k i
    _ = 2 * eVariationOn f
          (Icc (occupationGrid m k 0)
            (occupationGrid m k (k + 1))) := by
      rw [eVariationOn.sum' f (occupationGrid_monotone m k)]
    _ ≤ 2 * eVariationOn f univ := by
      gcongr
      exact eVariationOn.mono f (subset_univ _)

private lemma finite_completedGraph_points_le_liminf_grid
    {f : Real → Real} (hBV : BoundedVariationOn f univ)
    (m : Nat) (h : Real) (points : Set Real)
    (hFinite : points.Finite)
    (hBounded : points ⊆ Icc (-(m : Real)) (m : Real))
    (hGraph :
      ∀ x ∈ points,
        h ∈ uIcc (Function.leftLim f x) (f x)) :
    (points.encard : ENNReal) ≤
      liminf (fun k => occupationGridCount f m k h) atTop := by
  letI : Fintype points := hFinite.fintype
  let x : Fin (Fintype.card points) → Real :=
    fun j => ((Fintype.equivFin points).symm j).1
  have hxInjective : Function.Injective x := by
    intro i j hij
    apply (Fintype.equivFin points).symm.injective
    apply Subtype.ext
    exact hij
  have hxMem (j : Fin (Fintype.card points)) :
      x j ∈ points :=
    ((Fintype.equivFin points).symm j).2
  have hCellExists (k : Nat) (j : Fin (Fintype.card points)) :
      ∃ i, i < k + 1 ∧
        occupationGrid m k i < x j ∧
        x j ≤ occupationGrid m k (i + 1) := by
    simpa only [exists_and_left] using
      exists_occupationGrid_cell m k (hBounded (hxMem j))
  choose cell hCellLt hCellLeft hCellRight using hCellExists
  have hCellGraph (k : Nat) (j : Fin (Fintype.card points)) :
      h ∈ occupationCellLevels f m k (cell k j) := by
    unfold occupationCellLevels
    exact completedGraph_mem_occupationCell hBV
      (hCellLeft k j) (hCellRight k j) (hGraph (x j) (hxMem j))
  have hCellsEventuallyInjective :
      ∀ᶠ k in atTop, Function.Injective (cell k) := by
    have hPair (j l : Fin (Fintype.card points)) (hjl : j ≠ l) :
        ∀ᶠ k in atTop, cell k j ≠ cell k l := by
      have hDistance : 0 < |x j - x l| :=
        abs_pos.mpr (sub_ne_zero.mpr (hxInjective.ne hjl))
      filter_upwards [
        (occupationMesh_tendsto_zero m).eventually_lt_const hDistance
      ] with k hk hEq
      have hSameRight :
          occupationGrid m k (cell k j + 1) =
            occupationGrid m k (cell k l + 1) := by
        rw [hEq]
      have hSameLeft :
          occupationGrid m k (cell k j) =
            occupationGrid m k (cell k l) := by
        rw [hEq]
      have hTooClose :
          |x j - x l| < occupationMesh m k := by
        rw [abs_lt]
        constructor
        · calc
            -occupationMesh m k =
                occupationGrid m k (cell k j) -
                  occupationGrid m k (cell k j + 1) := by
                    rw [← occupationGrid_succ]
                    ring
            _ < x j - x l := by
              rw [hSameLeft, hSameRight]
              linarith [hCellLeft k j, hCellRight k l]
        · calc
            x j - x l <
                occupationGrid m k (cell k j + 1) -
                  occupationGrid m k (cell k j) := by
              rw [hSameLeft, hSameRight]
              linarith [hCellRight k j, hCellLeft k l]
            _ = occupationMesh m k :=
              occupationGrid_succ m k (cell k j)
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
  have hCount (k : Nat) (hCellInjective : Function.Injective (cell k)) :
      (points.encard : ENNReal) ≤ occupationGridCount f m k h := by
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
    rw [occupationGridCount]
    calc
      (points.encard : ENNReal) =
          ∑ i ∈ selected, (1 : ENNReal) := by
        rw [← points.coe_fintypeCard]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hSelectedCard.symm
      _ = ∑ i ∈ selected,
          (occupationCellLevels f m k i).indicator
            (fun _ => (1 : ENNReal)) h := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        rw [indicator_of_mem (hCellGraph k j)]
      _ ≤ ∑ i ∈ Finset.range (k + 1),
          (occupationCellLevels f m k i).indicator
            (fun _ => (1 : ENNReal)) h :=
        Finset.sum_le_sum_of_subset_of_nonneg hSelectedSubset
          (fun _ _ _ => zero_le)
  exact le_liminf_of_le (by isBoundedDefault)
    (hCellsEventuallyInjective.mono fun k hk => hCount k hk)

private def crossingLevelSet
    {mu nu : FiniteMeasure Real}
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (s : Set Real) (n : Nat) : Set Real :=
  Prod.snd ''
    (decomposition.piece n ∩ Prod.fst ⁻¹' s)

private lemma measurableSet_crossingLevelSet
    {mu nu : FiniteMeasure Real}
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    {s : Set Real} (hs : MeasurableSet s) (n : Nat) :
    MeasurableSet (crossingLevelSet decomposition s n) := by
  exact
    ((decomposition.measurable_piece n).inter
      (hs.preimage measurable_fst)).image_of_measurable_injOn
        measurable_snd
        ((decomposition.snd_injOn n).mono inter_subset_left)

private def decomposedCrossingCount
    {mu nu : FiniteMeasure Real}
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (s : Set Real) (h : Real) : ENNReal :=
  ∑' n,
    (crossingLevelSet decomposition s n).indicator
      (fun _ => (1 : ENNReal)) h

private lemma decomposedCrossingCount_eq
    {mu nu : FiniteMeasure Real}
    (decomposition : MeasurablePositiveCrossingDecomposition mu nu)
    (s : Set Real) (h : Real) :
    decomposedCrossingCount decomposition s h =
      ((positiveCrossingFiber mu nu s h).encard : ENNReal) := by
  let active : Set Nat :=
    {n | h ∈ crossingLevelSet decomposition s n}
  let point : active → positiveCrossingFiber mu nu s h :=
    fun n => by
      let p : Real × Real := Classical.choose n.2
      have hp :
          p ∈ decomposition.piece n.1 ∩ Prod.fst ⁻¹' s ∧
            p.2 = h :=
        Classical.choose_spec n.2
      refine ⟨p.1, hp.1.2, ?_⟩
      change (p.1, h) ∈ positiveCrossingRelation mu nu
      rw [← hp.2]
      rw [← decomposition.iUnion_piece]
      exact mem_iUnion.2 ⟨n.1, hp.1.1⟩
  have hPointInjective : Function.Injective point := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    let p : Real × Real := Classical.choose i.2
    let q : Real × Real := Classical.choose j.2
    have hp :
        p ∈ decomposition.piece i.1 ∩ Prod.fst ⁻¹' s ∧
          p.2 = h :=
      Classical.choose_spec i.2
    have hq :
        q ∈ decomposition.piece j.1 ∩ Prod.fst ⁻¹' s ∧
          q.2 = h :=
      Classical.choose_spec j.2
    have hpq : p = q := by
      apply Prod.ext
      · exact congrArg Subtype.val hij
      · exact hp.2.trans hq.2.symm
    exact (Set.disjoint_left.1
      (decomposition.pairwise_disjoint hne))
        hp.1.1 (hpq ▸ hq.1.1)
  have hPointSurjective : Function.Surjective point := by
    intro x
    have hxUnion :
        (x.1, h) ∈ ⋃ n, decomposition.piece n := by
      rw [decomposition.iUnion_piece]
      exact x.2.2
    rcases mem_iUnion.1 hxUnion with ⟨n, hn⟩
    have hnActive : n ∈ active := by
      refine ⟨(x.1, h), ⟨hn, x.2.1⟩, rfl⟩
    let i : active := ⟨n, hnActive⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    let p : Real × Real := Classical.choose i.2
    have hp :
        p ∈ decomposition.piece i.1 ∩ Prod.fst ⁻¹' s ∧
          p.2 = h :=
      Classical.choose_spec i.2
    have hpEq : p = (x.1, h) :=
      decomposition.snd_injOn n hp.1.1 hn hp.2
    exact congrArg Prod.fst hpEq
  let equivalence :
      active ≃ positiveCrossingFiber mu nu s h :=
    Equiv.ofBijective point ⟨hPointInjective, hPointSurjective⟩
  calc
    decomposedCrossingCount decomposition s h =
        ∑' _ : active, (1 : ENNReal) := by
      symm
      simpa only [decomposedCrossingCount, active, Set.mem_setOf_eq] using
        (tsum_subtype active (fun _ : Nat => (1 : ENNReal)))
    _ = (active.encard : ENNReal) :=
      ENNReal.tsum_set_one active
    _ = ((positiveCrossingFiber mu nu s h).encard : ENNReal) := by
      rw [Set.encard_congr equivalence]

private lemma measurable_positiveCrossingFiberEncard
    (mu nu : FiniteMeasure Real)
    {s : Set Real} (hs : MeasurableSet s) :
    Measurable
      (fun h =>
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)) := by
  let decomposition :=
    measurablePositiveCrossingDecomposition mu nu
  have hMeasurable :
      Measurable (decomposedCrossingCount decomposition s) := by
    apply Measurable.tsum
    intro n
    exact measurable_const.indicator
      (measurableSet_crossingLevelSet decomposition hs n)
  rw [show
    (fun h =>
      ((positiveCrossingFiber mu nu s h).encard : ENNReal)) =
        decomposedCrossingCount decomposition s by
      funext h
      exact (decomposedCrossingCount_eq decomposition s h).symm]
  exact hMeasurable

private theorem positiveCrossingOccupation_Icc_le
    (mu nu : FiniteMeasure Real) (m : Nat) :
    (∫⁻ h,
        ((positiveCrossingFiber mu nu
          (Icc (-(m : Real)) (m : Real)) h).encard : ENNReal)
      ∂(volume : Measure Real)) ≤
      2 * eVariationOn (signedCumulative mu nu) univ := by
  let f := signedCumulative mu nu
  have hBV : BoundedVariationOn f univ :=
    signedCumulativeBoundedVariation mu nu
  have hFinite :=
    positiveCrossingFiberFiniteAe mu nu
      (Icc (-(m : Real)) (m : Real))
  have hPointwise :
      ∀ᵐ h ∂(volume : Measure Real),
        ((positiveCrossingFiber mu nu
          (Icc (-(m : Real)) (m : Real)) h).encard : ENNReal) ≤
          liminf (fun k => occupationGridCount f m k h) atTop := by
    filter_upwards [hFinite] with h hFinite
    let points :=
      positiveCrossingFiber mu nu
        (Icc (-(m : Real)) (m : Real)) h
    apply finite_completedGraph_points_le_liminf_grid
      hBV m h points hFinite
    · intro x hx
      exact hx.1
    · intro x hx
      simpa only [f, generalizedCumulativeGraph, mem_setOf_eq,
        (signedCumulativeRightContinuousAndLeftLim mu nu).2] using
        hx.2.1
  calc
    (∫⁻ h,
        ((positiveCrossingFiber mu nu
          (Icc (-(m : Real)) (m : Real)) h).encard : ENNReal)
      ∂(volume : Measure Real)) ≤
        ∫⁻ h,
          liminf (fun k => occupationGridCount f m k h) atTop
        ∂(volume : Measure Real) :=
      lintegral_mono_ae hPointwise
    _ ≤ liminf
          (fun k =>
            ∫⁻ h, occupationGridCount f m k h
              ∂(volume : Measure Real))
          atTop :=
      lintegral_liminf_le
        (fun k => measurable_occupationGridCount f m k)
    _ ≤ 2 * eVariationOn f univ :=
      liminf_le_of_frequently_le'
        (Frequently.of_forall fun k =>
          lintegral_occupationGridCount_le hBV m k)

private lemma positiveCrossingFiber_Icc_mono
    (mu nu : FiniteMeasure Real) :
    Monotone
      (fun (m : Nat) h =>
        ((positiveCrossingFiber mu nu
          (Icc (-(m : Real)) (m : Real)) h).encard : ENNReal)) := by
  intro m n hmn h
  apply ENat.toENNReal_mono
  apply Set.encard_le_encard
  intro x hx
  refine ⟨?_, hx.2⟩
  have hmnReal : (m : Real) ≤ (n : Real) := by
    exact_mod_cast hmn
  constructor
  · exact (neg_le_neg hmnReal).trans hx.1.1
  · exact hx.1.2.trans hmnReal

private lemma positiveCrossingFiber_univ_eq_iSup_Icc
    (mu nu : FiniteMeasure Real) :
    ∀ᵐ h ∂(volume : Measure Real),
      ((positiveCrossingFiber mu nu univ h).encard : ENNReal) =
        ⨆ m : Nat,
          ((positiveCrossingFiber mu nu
            (Icc (-(m : Real)) (m : Real)) h).encard : ENNReal) := by
  filter_upwards [positiveCrossingFiberFiniteAe mu nu univ] with h hFinite
  apply le_antisymm
  · obtain ⟨m : Nat, hm⟩ :=
      exists_nat_gt
        (∑ x ∈ hFinite.toFinset, |x|)
    apply le_iSup_of_le m
    apply ENat.toENNReal_mono
    apply Set.encard_le_encard
    intro x hx
    have hxSum :
        |x| ≤ ∑ y ∈ hFinite.toFinset, |y| := by
      exact Finset.single_le_sum
        (fun y _ => abs_nonneg y)
        (hFinite.mem_toFinset.mpr hx)
    have hxm : |x| ≤ (m : Real) :=
      hxSum.trans hm.le
    exact ⟨abs_le.mp hxm, hx.2⟩
  · apply iSup_le
    intro m
    apply ENat.toENNReal_mono
    apply Set.encard_le_encard
    intro x hx
    exact ⟨mem_univ x, hx.2⟩

/-- The total occupation of good increasing crossings is uniformly bounded
by twice the global variation of the signed cumulative path.  The bound is
valid for every spatial restriction, without atomlessness, singularity,
equal mass, or stochastic order assumptions. -/
theorem positiveCrossingOccupation_le_two_mul_eVariationOn
    (mu nu : FiniteMeasure Real) (s : Set Real) :
    (∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)
      ∂(volume : Measure Real)) ≤
      2 * eVariationOn (signedCumulative mu nu) univ := by
  calc
    (∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)
      ∂(volume : Measure Real)) ≤
        ∫⁻ h,
          ((positiveCrossingFiber mu nu univ h).encard : ENNReal)
        ∂(volume : Measure Real) := by
      apply lintegral_mono
      intro h
      apply ENat.toENNReal_mono
      apply Set.encard_le_encard
      intro x hx
      exact ⟨mem_univ x, hx.2⟩
    _ = ⨆ m : Nat,
          ∫⁻ h,
            ((positiveCrossingFiber mu nu
              (Icc (-(m : Real)) (m : Real)) h).encard : ENNReal)
          ∂(volume : Measure Real) := by
      rw [lintegral_congr_ae
        (positiveCrossingFiber_univ_eq_iSup_Icc mu nu)]
      exact lintegral_iSup
        (fun m =>
          measurable_positiveCrossingFiberEncard mu nu measurableSet_Icc)
        (positiveCrossingFiber_Icc_mono mu nu)
    _ ≤ 2 * eVariationOn (signedCumulative mu nu) univ :=
      iSup_le fun m => positiveCrossingOccupation_Icc_le mu nu m

/-- In particular, every positive-crossing occupation integral is finite.
This rules out an `∞ = ∞` cancellation in subsequent Jordan-balance
arguments. -/
theorem positiveCrossingOccupationFinite
    (mu nu : FiniteMeasure Real) (s : Set Real) :
    (∫⁻ h,
        ((positiveCrossingFiber mu nu s h).encard : ENNReal)
      ∂(volume : Measure Real)) ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num)
      (signedCumulativeBoundedVariation mu nu))
    (positiveCrossingOccupation_le_two_mul_eVariationOn mu nu s)

end

end ConcaveOTLimit
