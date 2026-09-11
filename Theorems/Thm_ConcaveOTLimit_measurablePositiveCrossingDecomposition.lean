import Theorems.Thm_ConcaveOTLimit_existsPositiveCrossingOccupationEnumeration
import Mathlib.Logic.Equiv.Nat
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.SigmaCompact

open Filter Function MeasureTheory Set Topology

namespace ConcaveOTLimit

noncomputable section

private theorem eventually_completedGraph_above
    {f : Real → Real}
    (hBV : BoundedVariationOn f univ)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    {x c : Real}
    (hLeftValue : c < leftLim f x)
    (hRightValue : c < f x) :
    ∀ᶠ y in 𝓝 x, c < leftLim f y ∧ c < f y := by
  have hfLeft :
      ∀ᶠ y in 𝓝[<] x, c < f y :=
    (tendsto_order.1 (hBV.tendsto_leftLim x)).1 c hLeftValue
  have hfRight :
      ∀ᶠ y in 𝓝[≥] x, c < f y :=
    (tendsto_order.1 (hRight x).tendsto).1 c hRightValue
  have hf :
      ∀ᶠ y in 𝓝 x, c < f y := by
    rw [← nhdsWithin_univ, ← Iio_union_Ici, nhdsWithin_union,
      eventually_sup]
    exact ⟨hfLeft, hfRight⟩
  have hLeftLimLeft :
      ∀ᶠ y in 𝓝[≤] x, c < leftLim f y :=
    (tendsto_order.1 hBV.continuousWithinAt_leftLim.tendsto).1
      c hLeftValue
  have hLeftLimRightTendsto :
      Tendsto (leftLim f) (𝓝[>] x) (𝓝 (f x)) := by
    have h :=
      hBV.leftLim.tendsto_rightLim x
    rw [rightLim_leftLim (hBV.tendsto_rightLim x),
      (hRight x).rightLim_eq] at h
    exact h
  have hLeftLimRight :
      ∀ᶠ y in 𝓝[>] x, c < leftLim f y :=
    (tendsto_order.1 hLeftLimRightTendsto).1 c hRightValue
  have hLeftLim :
      ∀ᶠ y in 𝓝 x, c < leftLim f y := by
    rw [← nhdsWithin_univ, ← Iic_union_Ioi, nhdsWithin_union,
      eventually_sup]
    exact ⟨hLeftLimLeft, hLeftLimRight⟩
  exact hLeftLim.and hf

private theorem eventually_completedGraph_below
    {f : Real → Real}
    (hBV : BoundedVariationOn f univ)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    {x c : Real}
    (hLeftValue : leftLim f x < c)
    (hRightValue : f x < c) :
    ∀ᶠ y in 𝓝 x, leftLim f y < c ∧ f y < c := by
  have hfLeft :
      ∀ᶠ y in 𝓝[<] x, f y < c :=
    (tendsto_order.1 (hBV.tendsto_leftLim x)).2 c hLeftValue
  have hfRight :
      ∀ᶠ y in 𝓝[≥] x, f y < c :=
    (tendsto_order.1 (hRight x).tendsto).2 c hRightValue
  have hf :
      ∀ᶠ y in 𝓝 x, f y < c := by
    rw [← nhdsWithin_univ, ← Iio_union_Ici, nhdsWithin_union,
      eventually_sup]
    exact ⟨hfLeft, hfRight⟩
  have hLeftLimLeft :
      ∀ᶠ y in 𝓝[≤] x, leftLim f y < c :=
    (tendsto_order.1 hBV.continuousWithinAt_leftLim.tendsto).2
      c hLeftValue
  have hLeftLimRightTendsto :
      Tendsto (leftLim f) (𝓝[>] x) (𝓝 (f x)) := by
    have h :=
      hBV.leftLim.tendsto_rightLim x
    rw [rightLim_leftLim (hBV.tendsto_rightLim x),
      (hRight x).rightLim_eq] at h
    exact h
  have hLeftLimRight :
      ∀ᶠ y in 𝓝[>] x, leftLim f y < c :=
    (tendsto_order.1 hLeftLimRightTendsto).2 c hRightValue
  have hLeftLim :
      ∀ᶠ y in 𝓝 x, leftLim f y < c := by
    rw [← nhdsWithin_univ, ← Iic_union_Ioi, nhdsWithin_union,
      eventually_sup]
    exact ⟨hLeftLimLeft, hLeftLimRight⟩
  exact hLeftLim.and hf

private theorem isClosed_completedGraph
    {f : Real → Real}
    (hBV : BoundedVariationOn f univ)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x) :
    IsClosed {p : Real × Real |
      p.2 ∈ uIcc (leftLim f p.1) (f p.1)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  change p.2 ∉ uIcc (leftLim f p.1) (f p.1) at hp
  change ¬
    ((leftLim f p.1 ⊓ f p.1) ≤ p.2 ∧
      p.2 ≤ (leftLim f p.1 ⊔ f p.1)) at hp
  rw [not_and_or, not_le, not_le] at hp
  rcases hp with hp | hp
  · obtain ⟨c, hpc, hc⟩ := exists_between hp
    have hcLeft : c < leftLim f p.1 :=
      hc.trans_le inf_le_left
    have hcRight : c < f p.1 :=
      hc.trans_le inf_le_right
    have hHorizontal :=
      eventually_completedGraph_above hBV hRight hcLeft hcRight
    have hHorizontal' :
        ∀ᶠ q in 𝓝 p,
          c < leftLim f q.1 ∧ c < f q.1 :=
      continuousAt_fst.tendsto hHorizontal
    have hVertical :
        ∀ᶠ q in 𝓝 p, q.2 < c :=
      continuousAt_snd.tendsto (Iio_mem_nhds hpc)
    filter_upwards [hHorizontal', hVertical] with q hq hqc
    change q.2 ∉ uIcc (leftLim f q.1) (f q.1)
    exact Set.notMem_uIcc_of_lt (hqc.trans hq.1) (hqc.trans hq.2)
  · obtain ⟨c, hc, hcp⟩ := exists_between hp
    have hLeftC : leftLim f p.1 < c :=
      le_sup_left.trans_lt hc
    have hRightC : f p.1 < c :=
      le_sup_right.trans_lt hc
    have hHorizontal :=
      eventually_completedGraph_below hBV hRight hLeftC hRightC
    have hHorizontal' :
        ∀ᶠ q in 𝓝 p,
          leftLim f q.1 < c ∧ f q.1 < c :=
      continuousAt_fst.tendsto hHorizontal
    have hVertical :
        ∀ᶠ q in 𝓝 p, c < q.2 :=
      continuousAt_snd.tendsto (Ioi_mem_nhds hcp)
    filter_upwards [hHorizontal', hVertical] with q hq hcq
    change q.2 ∉ uIcc (leftLim f q.1) (f q.1)
    exact Set.notMem_uIcc_of_gt (hq.1.trans hcq) (hq.2.trans hcq)

/-- The completed graph of the signed cumulative function is closed. -/
theorem isClosed_generalizedCumulativeGraph
    (mu nu : FiniteMeasure Real) :
    IsClosed (generalizedCumulativeGraph mu nu) := by
  simpa only [generalizedCumulativeGraph, mem_setOf_eq,
    (signedCumulativeRightContinuousAndLeftLim mu nu).2] using
    isClosed_completedGraph
      (signedCumulativeBoundedVariation mu nu)
      (signedCumulativeRightContinuousAndLeftLim mu nu).1

private def crossingViolationCompact
    (mu nu : FiniteMeasure Real) (r : Real) (m k l : Nat) :
    Set ((Real × Real) × (Real × Real)) :=
  Metric.closedBall 0 (m : Real) ∩
    (Prod.snd ⁻¹' generalizedCumulativeGraph mu nu) ∩
      {z |
        1 / ((l : Real) + 1) ≤ |z.2.1 - z.1.1|} ∩
        {z |
          |z.2.1 - z.1.1| ≤ r - 1 / ((k : Real) + 1)} ∩
          {z |
            (z.2.2 - z.1.2) * (z.2.1 - z.1.1) ≤ 0}

private theorem isClosed_crossingViolationCompact
    (mu nu : FiniteMeasure Real) (r : Real) (m k l : Nat) :
    IsClosed (crossingViolationCompact mu nu r m k l) := by
  have hGraph :
      IsClosed
        (Prod.snd ⁻¹' generalizedCumulativeGraph mu nu) :=
    (isClosed_generalizedCumulativeGraph mu nu).preimage
      (continuous_snd :
        Continuous (fun z :
          (Real × Real) × (Real × Real) => z.2))
  have hLower :
      IsClosed
        {z : (Real × Real) × (Real × Real) |
          1 / ((l : Real) + 1) ≤ |z.2.1 - z.1.1|} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hUpper :
      IsClosed
        {z : (Real × Real) × (Real × Real) |
          |z.2.1 - z.1.1| ≤ r - 1 / ((k : Real) + 1)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hSign :
      IsClosed
        {z : (Real × Real) × (Real × Real) |
          (z.2.2 - z.1.2) * (z.2.1 - z.1.1) ≤ 0} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact
    ((((Metric.isClosed_closedBall.inter hGraph).inter hLower).inter
      hUpper).inter hSign)

private theorem isCompact_crossingViolationCompact
    (mu nu : FiniteMeasure Real) (r : Real) (m k l : Nat) :
    IsCompact (crossingViolationCompact mu nu r m k l) := by
  apply (isCompact_closedBall (0 :
    (Real × Real) × (Real × Real)) (m : Real)).of_isClosed_subset
    (isClosed_crossingViolationCompact mu nu r m k l)
  intro z hz
  exact hz.1.1.1.1

private def positiveCrossingViolation
    (mu nu : FiniteMeasure Real) (r : Real) :
    Set (Real × Real) :=
  {p |
    ∃ q : Real × Real,
      q ∈ generalizedCumulativeGraph mu nu ∧
        |q.1 - p.1| < r ∧
          q.1 ≠ p.1 ∧
            (q.2 - p.2) * (q.1 - p.1) ≤ 0}

private theorem positiveCrossingViolation_eq_iUnion
    (mu nu : FiniteMeasure Real) (r : Real) :
    positiveCrossingViolation mu nu r =
      ⋃ m, ⋃ k, ⋃ l,
        Prod.fst '' crossingViolationCompact mu nu r m k l := by
  ext p
  constructor
  · rintro ⟨q, hqGraph, hqNear, hqNe, hqSign⟩
    obtain ⟨m : Nat, hm⟩ :=
      exists_nat_gt (dist (p, q)
        (0 : (Real × Real) × (Real × Real)))
    obtain ⟨k : Nat, hk⟩ :=
      exists_nat_one_div_lt (sub_pos.mpr hqNear)
    obtain ⟨l : Nat, hl⟩ :=
      exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr hqNe))
    refine mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨k,
      mem_iUnion.2 ⟨l, ?_⟩⟩⟩
    refine ⟨(p, q), ?_, rfl⟩
    refine ⟨⟨⟨⟨Metric.mem_closedBall.mpr hm.le, hqGraph⟩,
      hl.le⟩, ?_⟩, hqSign⟩
    change |q.1 - p.1| ≤ r - 1 / ((k : Real) + 1)
    rw [le_sub_iff_add_le]
    have hsum :=
      ((lt_sub_iff_add_lt).1 hk).le
    simpa only [add_comm] using hsum
  · intro hp
    rcases mem_iUnion.1 hp with ⟨m, hp⟩
    rcases mem_iUnion.1 hp with ⟨k, hp⟩
    rcases mem_iUnion.1 hp with ⟨l, hp⟩
    rcases hp with ⟨z, hz, rfl⟩
    rcases hz with
      ⟨⟨⟨⟨_hzBall, hzGraph⟩, hzLower⟩, hzUpper⟩, hzSign⟩
    have hkPos : 0 < 1 / ((k : Real) + 1) := by positivity
    have hlPos : 0 < 1 / ((l : Real) + 1) := by positivity
    change |z.2.1 - z.1.1| ≤
      r - 1 / ((k : Real) + 1) at hzUpper
    change 1 / ((l : Real) + 1) ≤
      |z.2.1 - z.1.1| at hzLower
    refine ⟨z.2, hzGraph, ?_, ?_, hzSign⟩
    · exact hzUpper.trans_lt (sub_lt_self r hkPos)
    · exact sub_ne_zero.mp (abs_pos.mp (hlPos.trans_le hzLower))

private theorem measurableSet_positiveCrossingViolation
    (mu nu : FiniteMeasure Real) (r : Real) :
    MeasurableSet (positiveCrossingViolation mu nu r) := by
  rw [positiveCrossingViolation_eq_iUnion]
  exact MeasurableSet.iUnion fun m =>
    MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun l =>
        ((isCompact_crossingViolationCompact mu nu r m k l).image
          continuous_fst).isClosed.measurableSet

private def positiveCrossingAtRadius
    (mu nu : FiniteMeasure Real) (r : Real) :
    Set (Real × Real) :=
  generalizedCumulativeGraph mu nu \
    positiveCrossingViolation mu nu r

private theorem mem_positiveCrossingAtRadius_iff
    {mu nu : FiniteMeasure Real} {r : Real} {p : Real × Real} :
    p ∈ positiveCrossingAtRadius mu nu r ↔
      p ∈ generalizedCumulativeGraph mu nu ∧
        ∀ q ∈ generalizedCumulativeGraph mu nu,
          |q.1 - p.1| < r →
            q.1 ≠ p.1 →
              0 < (q.2 - p.2) * (q.1 - p.1) := by
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro q hqGraph hqNear hqNe
    by_contra hq
    exact hp.2 ⟨q, hqGraph, hqNear, hqNe, le_of_not_gt hq⟩
  · rintro ⟨hpGraph, hp⟩
    refine ⟨hpGraph, ?_⟩
    rintro ⟨q, hqGraph, hqNear, hqNe, hqSign⟩
    exact (not_lt_of_ge hqSign) (hp q hqGraph hqNear hqNe)

private theorem measurableSet_positiveCrossingAtRadius
    (mu nu : FiniteMeasure Real) (r : Real) :
    MeasurableSet (positiveCrossingAtRadius mu nu r) :=
  (isClosed_generalizedCumulativeGraph mu nu).measurableSet.diff
    (measurableSet_positiveCrossingViolation mu nu r)

private lemma mem_Ioo_of_abs_sub_lt
    {x y epsilon : Real} (h : |y - x| < epsilon) :
    y ∈ Ioo (x - epsilon) (x + epsilon) := by
  rw [mem_Ioo]
  rcases abs_lt.mp h with ⟨hLower, hUpper⟩
  constructor <;> linarith

private lemma abs_sub_lt_of_mem_Ioo
    {x y epsilon : Real}
    (h : y ∈ Ioo (x - epsilon) (x + epsilon)) :
    |y - x| < epsilon := by
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2]

private theorem positiveCrossingRelation_eq_iUnion
    (mu nu : FiniteMeasure Real) :
    positiveCrossingRelation mu nu =
      ⋃ n : Nat,
        positiveCrossingAtRadius mu nu
          (1 / ((n : Real) + 1)) := by
  ext p
  constructor
  · intro hp
    change IsGoodIncreasingCrossing mu nu p.1 p.2 at hp
    rcases hp with ⟨hpGraph, epsilon, hEpsilon, hpLocal⟩
    obtain ⟨n : Nat, hn⟩ := exists_nat_one_div_lt hEpsilon
    refine mem_iUnion.2 ⟨n,
      mem_positiveCrossingAtRadius_iff.2 ⟨hpGraph, ?_⟩⟩
    intro q hqGraph hqNear hqNe
    exact hpLocal (mem_Ioo_of_abs_sub_lt (hqNear.trans hn))
      hqNe hqGraph
  · intro hp
    rcases mem_iUnion.1 hp with ⟨n, hp⟩
    rcases mem_positiveCrossingAtRadius_iff.1 hp with
      ⟨hpGraph, hpLocal⟩
    change IsGoodIncreasingCrossing mu nu p.1 p.2
    refine ⟨hpGraph, 1 / ((n : Real) + 1), by positivity, ?_⟩
    intro x' h' hx' hxNe hx'Graph
    exact hpLocal (x', h') hx'Graph
      (abs_sub_lt_of_mem_Ioo hx') hxNe

/-- The relation of good increasing completed-graph crossings is Borel. -/
theorem measurableSet_positiveCrossingRelation
    (mu nu : FiniteMeasure Real) :
    MeasurableSet (positiveCrossingRelation mu nu) := by
  rw [positiveCrossingRelation_eq_iUnion]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_positiveCrossingAtRadius mu nu
      (1 / ((n : Real) + 1))

/-- Every level fiber of the positive-crossing relation is countable. -/
theorem positiveCrossingRelation_countable_sndFiber
    (mu nu : FiniteMeasure Real) (h : Real) :
    {x : Real | (x, h) ∈ positiveCrossingRelation mu nu}.Countable := by
  let s : Set Real :=
    {x : Real | (x, h) ∈ positiveCrossingRelation mu nu}
  have hDiscrete : DiscreteTopology s := by
    rw [discreteTopology_subtype_iff']
    intro x hx
    change IsGoodIncreasingCrossing mu nu x h at hx
    rcases hx with ⟨hxGraph, epsilon, hEpsilon, hxLocal⟩
    refine ⟨Ioo (x - epsilon) (x + epsilon), isOpen_Ioo, ?_⟩
    ext y
    constructor
    · rintro ⟨hyNear, hy⟩
      by_contra hyx
      change IsGoodIncreasingCrossing mu nu y h at hy
      have hPositive :=
        hxLocal hyNear hyx hy.1
      simp only [sub_self, zero_mul, lt_self_iff_false] at hPositive
    · intro hy
      have hyx : y = x := by simpa only [mem_singleton_iff] using hy
      subst y
      exact ⟨⟨by linarith, by linarith⟩, ⟨hxGraph,
        epsilon, hEpsilon, hxLocal⟩⟩
  letI : DiscreteTopology s := hDiscrete
  haveI : Countable s :=
    TopologicalSpace.separableSpace_iff_countable.mp
      (inferInstance : TopologicalSpace.SeparableSpace s)
  simpa only [s] using Set.to_countable s

private def crossingRadius (n : Nat) : Real :=
  1 / ((n : Real) + 1)

private def crossingCellWidth (n : Nat) : Real :=
  crossingRadius n / 2

private def crossingCellIndex (j : Nat) : Int :=
  Equiv.intEquivNat.symm j

private def crossingCell (n j : Nat) : Set Real :=
  Ico
    ((crossingCellIndex j : Real) * crossingCellWidth n)
    (((crossingCellIndex j : Real) + 1) * crossingCellWidth n)

private theorem crossingRadius_pos (n : Nat) :
    0 < crossingRadius n := by
  unfold crossingRadius
  positivity

private theorem crossingCellWidth_pos (n : Nat) :
    0 < crossingCellWidth n := by
  unfold crossingCellWidth
  exact div_pos (crossingRadius_pos n) (by norm_num)

private theorem exists_mem_crossingCell (n : Nat) (x : Real) :
    ∃ j : Nat, x ∈ crossingCell n j := by
  let w := crossingCellWidth n
  have hw : 0 < w := crossingCellWidth_pos n
  let k : Int := ⌊x / w⌋
  let j : Nat := Equiv.intEquivNat k
  have hj : crossingCellIndex j = k := by
    simp only [crossingCellIndex, j, Equiv.symm_apply_apply]
  refine ⟨j, ?_⟩
  rw [crossingCell, hj, mem_Ico]
  constructor
  · calc
      (k : Real) * w ≤ (x / w) * w :=
        mul_le_mul_of_nonneg_right (Int.floor_le (x / w)) hw.le
      _ = x := div_mul_cancel₀ x hw.ne'
  · calc
      x = (x / w) * w := (div_mul_cancel₀ x hw.ne').symm
      _ < ((k : Real) + 1) * w :=
        mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / w)) hw

private theorem abs_sub_lt_crossingRadius_of_mem_cell
    {n j : Nat} {x y : Real}
    (hx : x ∈ crossingCell n j)
    (hy : y ∈ crossingCell n j) :
    |y - x| < crossingRadius n := by
  have hw : 0 < crossingCellWidth n :=
    crossingCellWidth_pos n
  have hr : 0 < crossingRadius n :=
    crossingRadius_pos n
  rw [crossingCell, mem_Ico] at hx hy
  have hAbs : |y - x| < crossingCellWidth n := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hWidth : crossingCellWidth n < crossingRadius n := by
    unfold crossingCellWidth
    linarith
  exact hAbs.trans hWidth

private def crossingRawPiece
    (mu nu : FiniteMeasure Real) (a : Nat) :
    Set (Real × Real) :=
  let index := Nat.pairEquiv.symm a
  positiveCrossingAtRadius mu nu (crossingRadius index.1) ∩
    Prod.fst ⁻¹' crossingCell index.1 index.2

private theorem measurableSet_crossingRawPiece
    (mu nu : FiniteMeasure Real) (a : Nat) :
    MeasurableSet (crossingRawPiece mu nu a) := by
  let index := Nat.pairEquiv.symm a
  exact
    (measurableSet_positiveCrossingAtRadius
      mu nu (crossingRadius index.1)).inter
      (measurableSet_Ico.preimage measurable_fst)

private theorem snd_injOn_crossingRawPiece
    (mu nu : FiniteMeasure Real) (a : Nat) :
    InjOn Prod.snd (crossingRawPiece mu nu a) := by
  let index := Nat.pairEquiv.symm a
  intro p hp q hq hpq
  apply Prod.ext ?_ hpq
  by_contra hne
  have hqNe : q.1 ≠ p.1 := fun h => hne h.symm
  have hNear :
      |q.1 - p.1| < crossingRadius index.1 :=
    abs_sub_lt_crossingRadius_of_mem_cell hp.2 hq.2
  have hpLocal :=
    (mem_positiveCrossingAtRadius_iff.1 hp.1).2
  have hqGraph :=
    (mem_positiveCrossingAtRadius_iff.1 hq.1).1
  have hPositive := hpLocal q hqGraph hNear hqNe
  rw [hpq, sub_self, zero_mul] at hPositive
  exact (lt_irrefl 0 hPositive).elim

private theorem iUnion_crossingRawPiece
    (mu nu : FiniteMeasure Real) :
    (⋃ a, crossingRawPiece mu nu a) =
      positiveCrossingRelation mu nu := by
  ext p
  constructor
  · intro hp
    rcases mem_iUnion.1 hp with ⟨a, hp⟩
    let index := Nat.pairEquiv.symm a
    rw [positiveCrossingRelation_eq_iUnion]
    exact mem_iUnion.2 ⟨index.1, hp.1⟩
  · intro hp
    rw [positiveCrossingRelation_eq_iUnion] at hp
    rcases mem_iUnion.1 hp with ⟨n, hp⟩
    obtain ⟨j, hj⟩ := exists_mem_crossingCell n p.1
    refine mem_iUnion.2 ⟨Nat.pairEquiv (n, j), ?_⟩
    simpa only [crossingRawPiece, Equiv.symm_apply_apply,
      crossingRadius] using
      And.intro hp hj

private def crossingPiece
    (mu nu : FiniteMeasure Real) (n : Nat) :
    Set (Real × Real) :=
  crossingRawPiece mu nu n \
    ⋃ m : Nat, ⋃ (_ : m < n), crossingRawPiece mu nu m

private theorem measurableSet_crossingPiece
    (mu nu : FiniteMeasure Real) (n : Nat) :
    MeasurableSet (crossingPiece mu nu n) :=
  (measurableSet_crossingRawPiece mu nu n).diff
    (MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun (_ : m < n) =>
        measurableSet_crossingRawPiece mu nu m)

private theorem pairwise_disjoint_crossingPiece
    (mu nu : FiniteMeasure Real) :
    Pairwise (Disjoint on crossingPiece mu nu) := by
  intro i j hij
  change Disjoint (crossingPiece mu nu i) (crossingPiece mu nu j)
  rw [Set.disjoint_left]
  intro p hpi hpj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hpj.2
      (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hij, hpi.1⟩⟩)
  · exact hpi.2
      (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hji, hpj.1⟩⟩)

private theorem iUnion_crossingPiece
    (mu nu : FiniteMeasure Real) :
    (⋃ n, crossingPiece mu nu n) =
      ⋃ n, crossingRawPiece mu nu n := by
  classical
  apply subset_antisymm
  · intro p hp
    rcases mem_iUnion.1 hp with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hn.1⟩
  · intro p hp
    have hExists :
        ∃ n : Nat, p ∈ crossingRawPiece mu nu n := by
      simpa only [mem_iUnion] using hp
    let n := Nat.find hExists
    have hnRaw :
        p ∈ crossingRawPiece mu nu n :=
      Nat.find_spec hExists
    have hnEarlier :
        p ∉ ⋃ m : Nat, ⋃ (_ : m < n),
          crossingRawPiece mu nu m := by
      intro hpEarlier
      rcases mem_iUnion.1 hpEarlier with ⟨m, hpEarlier⟩
      rcases mem_iUnion.1 hpEarlier with ⟨hmn, hmRaw⟩
      have hnm : n ≤ m :=
        Nat.find_min' hExists hmRaw
      exact (not_le_of_gt hmn) hnm
    exact mem_iUnion.2 ⟨n, ⟨hnRaw, hnEarlier⟩⟩

private theorem snd_injOn_crossingPiece
    (mu nu : FiniteMeasure Real) (n : Nat) :
    InjOn Prod.snd (crossingPiece mu nu n) :=
  (snd_injOn_crossingRawPiece mu nu n).mono diff_subset

/-- An explicit Borel graph decomposition of all good increasing crossings. -/
noncomputable def measurablePositiveCrossingDecomposition
    (mu nu : FiniteMeasure Real) :
    MeasurablePositiveCrossingDecomposition mu nu where
  piece := crossingPiece mu nu
  measurable_piece := measurableSet_crossingPiece mu nu
  pairwise_disjoint := pairwise_disjoint_crossingPiece mu nu
  iUnion_piece := by
    rw [iUnion_crossingPiece, iUnion_crossingRawPiece]
  snd_injOn := snd_injOn_crossingPiece mu nu

/-- The positive-crossing relation always admits a countable Borel graph
decomposition over its level coordinate. -/
theorem existsMeasurablePositiveCrossingDecomposition
    (mu nu : FiniteMeasure Real) :
    Nonempty (MeasurablePositiveCrossingDecomposition mu nu) :=
  ⟨measurablePositiveCrossingDecomposition mu nu⟩

end

end ConcaveOTLimit
