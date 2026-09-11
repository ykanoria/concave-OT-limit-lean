import Definitions.Def_LiteralJuilletExcursion
import Theorems.Thm_ConcaveOTLimit_literalJuilletRegularLevels
import Theorems.Thm_ConcaveOTLimit_signedCumulativeBoundedVariation
import Theorems.Thm_ConcaveOTLimit_signedCumulativeRightContinuousAndLeftLim

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace ConcaveOTLimit

private theorem iInter_Iic_real :
    (⋂ x : Real, Iic x) = (∅ : Set Real) := by
  ext z
  simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
  push Not
  exact ⟨z - 1, by linarith⟩

/-- The signed cumulative function tends to zero at the left tail. -/
theorem tendsto_signedCumulative_atBot
    (mu nu : FiniteMeasure Real) :
    Tendsto (signedCumulative mu nu) atBot (nhds 0) := by
  have hMeasure
      (eta : FiniteMeasure Real) :
      Tendsto (fun x : Real => (eta : Measure Real) (Iic x))
        atBot (nhds 0) := by
    have h :=
      tendsto_measure_iInter_atBot
        (μ := (eta : Measure Real))
        (s := fun x : Real => Iic x)
        (fun _ => measurableSet_Iic.nullMeasurableSet)
        (fun _ _ hxy => Iic_subset_Iic.mpr hxy)
        ⟨0, measure_ne_top (eta : Measure Real) (Iic 0)⟩
    simpa only [Function.comp_apply, iInter_Iic_real, measure_empty] using h
  have hReal
      (eta : FiniteMeasure Real) :
      Tendsto (fun x : Real =>
          ((eta : Measure Real) (Iic x)).toReal)
        atBot (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hMeasure eta)
  simpa only [signedCumulative, sub_zero] using
    (hReal mu).sub (hReal nu)

/-- Equal finite masses force the signed cumulative function to tend to zero
at the right tail. -/
theorem tendsto_signedCumulative_atTop_of_mass_eq
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass) :
    Tendsto (signedCumulative mu nu) atTop (nhds 0) := by
  have hReal
      (eta : FiniteMeasure Real) :
      Tendsto (fun x : Real =>
          ((eta : Measure Real) (Iic x)).toReal)
        atTop
        (nhds ((eta : Measure Real) univ).toReal) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (eta : Measure Real) univ)).comp
        (tendsto_measure_Iic_atTop (eta : Measure Real))
  have hMassReal :
      ((mu : Measure Real) univ).toReal =
        ((nu : Measure Real) univ).toReal := by
    rw [← FiniteMeasure.ennreal_mass, ← FiniteMeasure.ennreal_mass]
    exact congrArg (fun r : NNReal => (r : Real)) hMass
  simpa only [signedCumulative, hMassReal, sub_self] using
    (hReal mu).sub (hReal nu)

private theorem signedCumulative_value_mem_graph
    (mu nu : FiniteMeasure Real) (x : Real) :
    (x, signedCumulative mu nu x) ∈
      generalizedCumulativeGraph mu nu := by
  change
    signedCumulative mu nu x ∈
      uIcc (signedCumulativeLeft mu nu x)
        (signedCumulative mu nu x)
  exact right_mem_uIcc

/-- On a preconnected set avoiding one horizontal completed-graph level, the
right-continuous cumulative value stays on one fixed side of that level. -/
theorem signedCumulative_side_constant_on_preconnected
    (mu nu : FiniteMeasure Real) (h : Real)
    {s : Set Real}
    (hs : IsPreconnected s)
    (hAvoid :
      ∀ x ∈ s, (x, h) ∉ generalizedCumulativeGraph mu nu)
    {x y : Real} (hx : x ∈ s) (hy : y ∈ s) :
    signedCumulative mu nu x < h ↔
      signedCumulative mu nu y < h := by
  let F := signedCumulative mu nu
  have hLeftTendsto (z : Real) :
      Tendsto F (nhdsWithin z (Iio z))
        (nhds (signedCumulativeLeft mu nu z)) := by
    have hz :=
      (signedCumulativeBoundedVariation mu nu).tendsto_leftLim z
    rw [(signedCumulativeRightContinuousAndLeftLim mu nu).2 z] at hz
    exact hz
  have hRightTendsto (z : Real) :
      Tendsto F (nhdsWithin z (Ici z)) (nhds (F z)) :=
    ((signedCumulativeRightContinuousAndLeftLim mu nu).1 z).tendsto
  apply hs.induction₂
    (fun a b => F a < h ↔ F b < h)
  · intro z hz
    have hzNe : F z ≠ h := by
      intro hzEq
      apply hAvoid z hz
      change h ∈
        uIcc (signedCumulativeLeft mu nu z) (F z)
      rw [hzEq]
      exact right_mem_uIcc
    rcases lt_or_gt_of_ne hzNe with hzBelow | hzAbove
    · have hLeftBelow :
          signedCumulativeLeft mu nu z < h := by
        by_contra hNot
        have hhLeft :
            h ≤ signedCumulativeLeft mu nu z :=
          le_of_not_gt hNot
        apply hAvoid z hz
        change h ∈
          uIcc (signedCumulativeLeft mu nu z) (F z)
        rw [uIcc_of_ge (hzBelow.le.trans hhLeft)]
        exact ⟨hzBelow.le, hhLeft⟩
      have hEventuallyLeft :
          ∀ᶠ w in nhdsWithin z (Iio z), F w < h :=
        (hLeftTendsto z).eventually_lt_const hLeftBelow
      have hEventuallyRight :
          ∀ᶠ w in nhdsWithin z (Ici z), F w < h :=
        (hRightTendsto z).eventually_lt_const hzBelow
      have hEventually :
          ∀ᶠ w in nhds z, F w < h := by
        rw [← nhdsLT_sup_nhdsGE]
        exact Filter.mem_sup.mpr
          ⟨hEventuallyLeft, hEventuallyRight⟩
      filter_upwards [hEventually.filter_mono inf_le_left] with w hw
      exact iff_of_true hzBelow hw
    · have hLeftAbove :
          h < signedCumulativeLeft mu nu z := by
        by_contra hNot
        have hLeftLe :
            signedCumulativeLeft mu nu z ≤ h :=
          le_of_not_gt hNot
        apply hAvoid z hz
        change h ∈
          uIcc (signedCumulativeLeft mu nu z) (F z)
        rw [uIcc_of_le (hLeftLe.trans hzAbove.le)]
        exact ⟨hLeftLe, hzAbove.le⟩
      have hEventuallyLeft :
          ∀ᶠ w in nhdsWithin z (Iio z), h < F w :=
        (hLeftTendsto z).eventually_const_lt hLeftAbove
      have hEventuallyRight :
          ∀ᶠ w in nhdsWithin z (Ici z), h < F w :=
        (hRightTendsto z).eventually_const_lt hzAbove
      have hEventually :
          ∀ᶠ w in nhds z, h < F w := by
        rw [← nhdsLT_sup_nhdsGE]
        exact Filter.mem_sup.mpr
          ⟨hEventuallyLeft, hEventuallyRight⟩
      filter_upwards [hEventually.filter_mono inf_le_left] with w hw
      exact iff_of_false (not_lt_of_ge hzAbove.le)
        (not_lt_of_ge hw.le)
  · intro a b c _ha _hb _hc hab hbc
    exact hab.trans hbc
  · intro a b _ha _hb hab
    exact hab.symm
  · exact hx
  · exact hy

private theorem exists_left_tail_below
    (mu nu : FiniteMeasure Real) {h x : Real}
    (hPositive : 0 < h) :
    ∃ a < x, signedCumulative mu nu a < h := by
  rcases
      (((tendsto_signedCumulative_atBot mu nu).eventually_lt_const
        hPositive).and (eventually_lt_atBot x)).exists with
    ⟨a, haBelow, hax⟩
  exact ⟨a, hax, haBelow⟩

private theorem exists_right_tail_below
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    {h x : Real} (hPositive : 0 < h) :
    ∃ b > x, signedCumulative mu nu b < h := by
  rcases
      (((tendsto_signedCumulative_atTop_of_mass_eq
        mu nu hMass).eventually_lt_const hPositive).and
        (eventually_gt_atTop x)).exists with
    ⟨b, hbBelow, hxb⟩
  exact ⟨b, hxb, hbBelow⟩

private theorem goodIncreasingCrossing_right_point
    {mu nu : FiniteMeasure Real} {x y h : Real}
    (hx : IsGoodIncreasingCrossing mu nu x h)
    (hxy : x < y) :
    ∃ z ∈ Ioo x y, h < signedCumulative mu nu z := by
  obtain ⟨_hxGraph, epsilon, hEpsilon, hLocal⟩ := hx
  have hBound :
      x < min y (x + epsilon) :=
    lt_min hxy (lt_add_of_pos_right x hEpsilon)
  obtain ⟨z, hxz, hzBound⟩ := exists_between hBound
  have hzy : z < y :=
    hzBound.trans_le (min_le_left y (x + epsilon))
  have hzNearUpper : z < x + epsilon :=
    hzBound.trans_le (min_le_right y (x + epsilon))
  have hzNear : z ∈ Ioo (x - epsilon) (x + epsilon) :=
    ⟨(sub_lt_self x hEpsilon).trans hxz, hzNearUpper⟩
  have hProduct :=
    hLocal hzNear hxz.ne'
      (signedCumulative_value_mem_graph mu nu z)
  have hAbove :
      h < signedCumulative mu nu z := by
    rcases mul_pos_iff.mp hProduct with hSigns | hSigns
    · linarith [hSigns.1]
    · linarith [hSigns.2]
  exact ⟨z, ⟨hxz, hzy⟩, hAbove⟩

private theorem goodIncreasingCrossing_left_point
    {mu nu : FiniteMeasure Real} {x y h : Real}
    (hx : IsGoodIncreasingCrossing mu nu y h)
    (hxy : x < y) :
    ∃ z ∈ Ioo x y, signedCumulative mu nu z < h := by
  obtain ⟨_hyGraph, epsilon, hEpsilon, hLocal⟩ := hx
  have hBound :
      max x (y - epsilon) < y :=
    max_lt hxy (sub_lt_self y hEpsilon)
  obtain ⟨z, hzBound, hzy⟩ := exists_between hBound
  have hxz : x < z :=
    (le_max_left x (y - epsilon)).trans_lt hzBound
  have hzNearLower : y - epsilon < z :=
    (le_max_right x (y - epsilon)).trans_lt hzBound
  have hzNear : z ∈ Ioo (y - epsilon) (y + epsilon) :=
    ⟨hzNearLower, hzy.trans (lt_add_of_pos_right y hEpsilon)⟩
  have hProduct :=
    hLocal hzNear hzy.ne
      (signedCumulative_value_mem_graph mu nu z)
  have hBelow :
      signedCumulative mu nu z < h := by
    rcases mul_pos_iff.mp hProduct with hSigns | hSigns
    · linarith [hSigns.2]
    · linarith [hSigns.1]
  exact ⟨z, ⟨hxz, hzy⟩, hBelow⟩

private theorem goodDecreasingCrossing_right_point
    {mu nu : FiniteMeasure Real} {x y h : Real}
    (hx : IsGoodDecreasingCrossing mu nu x h)
    (hxy : x < y) :
    ∃ z ∈ Ioo x y, signedCumulative mu nu z < h := by
  obtain ⟨_hxGraph, epsilon, hEpsilon, hLocal⟩ := hx
  have hBound :
      x < min y (x + epsilon) :=
    lt_min hxy (lt_add_of_pos_right x hEpsilon)
  obtain ⟨z, hxz, hzBound⟩ := exists_between hBound
  have hzy : z < y :=
    hzBound.trans_le (min_le_left y (x + epsilon))
  have hzNearUpper : z < x + epsilon :=
    hzBound.trans_le (min_le_right y (x + epsilon))
  have hzNear : z ∈ Ioo (x - epsilon) (x + epsilon) :=
    ⟨(sub_lt_self x hEpsilon).trans hxz, hzNearUpper⟩
  have hProduct :=
    hLocal hzNear hxz.ne'
      (signedCumulative_value_mem_graph mu nu z)
  have hBelow :
      signedCumulative mu nu z < h := by
    rcases mul_neg_iff.mp hProduct with hSigns | hSigns
    · linarith [hSigns.2]
    · linarith [hSigns.1]
  exact ⟨z, ⟨hxz, hzy⟩, hBelow⟩

private theorem goodDecreasingCrossing_left_point
    {mu nu : FiniteMeasure Real} {x y h : Real}
    (hy : IsGoodDecreasingCrossing mu nu y h)
    (hxy : x < y) :
    ∃ z ∈ Ioo x y, h < signedCumulative mu nu z := by
  obtain ⟨_hyGraph, epsilon, hEpsilon, hLocal⟩ := hy
  have hBound :
      max x (y - epsilon) < y :=
    max_lt hxy (sub_lt_self y hEpsilon)
  obtain ⟨z, hzBound, hzy⟩ := exists_between hBound
  have hxz : x < z :=
    (le_max_left x (y - epsilon)).trans_lt hzBound
  have hzNearLower : y - epsilon < z :=
    (le_max_right x (y - epsilon)).trans_lt hzBound
  have hzNear : z ∈ Ioo (y - epsilon) (y + epsilon) :=
    ⟨hzNearLower, hzy.trans (lt_add_of_pos_right y hEpsilon)⟩
  have hProduct :=
    hLocal hzNear hzy.ne
      (signedCumulative_value_mem_graph mu nu z)
  have hAbove :
      h < signedCumulative mu nu z := by
    rcases mul_neg_iff.mp hProduct with hSigns | hSigns
    · linarith [hSigns.1]
    · linarith [hSigns.2]
  exact ⟨z, ⟨hxz, hzy⟩, hAbove⟩

/-- Consecutive classified hits have opposite crossing orientations. -/
theorem literalJuilletConsecutiveCrossingsAlternate
    {mu nu : FiniteMeasure Real} {h x y : Real}
    (hClassified :
      ∀ z, (z, h) ∈ generalizedCumulativeGraph mu nu ->
        Xor (IsGoodIncreasingCrossing mu nu z h)
          (IsGoodDecreasingCrossing mu nu z h))
    (hxy : AreConsecutiveAtLevel mu nu h x y) :
    Xor
      (IsGoodIncreasingCrossing mu nu x h /\
        IsGoodDecreasingCrossing mu nu y h)
      (IsGoodDecreasingCrossing mu nu x h /\
        IsGoodIncreasingCrossing mu nu y h) := by
  have hSide {a b : Real}
      (ha : a ∈ Ioo x y) (hb : b ∈ Ioo x y) :
      signedCumulative mu nu a < h ↔
        signedCumulative mu nu b < h :=
    signedCumulative_side_constant_on_preconnected
      mu nu h isPreconnected_Ioo
      (fun z hz => hxy.2.2.2 z hz) ha hb
  rcases hClassified x hxy.2.1 with
      ⟨hxIncreasing, hxNotDecreasing⟩ |
      ⟨hxDecreasing, hxNotIncreasing⟩
  · rcases hClassified y hxy.2.2.1 with
        ⟨hyIncreasing, hyNotDecreasing⟩ |
        ⟨hyDecreasing, hyNotIncreasing⟩
    · obtain ⟨a, ha, haAbove⟩ :=
        goodIncreasingCrossing_right_point hxIncreasing hxy.1
      obtain ⟨b, hb, hbBelow⟩ :=
        goodIncreasingCrossing_left_point hyIncreasing hxy.1
      exact ((not_lt_of_ge haAbove.le) ((hSide ha hb).mpr hbBelow)).elim
    · exact Or.inl
        ⟨⟨hxIncreasing, hyDecreasing⟩,
          fun hOpposite => hxNotDecreasing hOpposite.1⟩
  · rcases hClassified y hxy.2.2.1 with
        ⟨hyIncreasing, hyNotDecreasing⟩ |
        ⟨hyDecreasing, hyNotIncreasing⟩
    · exact Or.inr
        ⟨⟨hxDecreasing, hyIncreasing⟩,
          fun hOpposite => hxNotIncreasing hOpposite.1⟩
    · obtain ⟨a, ha, haBelow⟩ :=
        goodDecreasingCrossing_right_point hxDecreasing hxy.1
      obtain ⟨b, hb, hbAbove⟩ :=
        goodDecreasingCrossing_left_point hyDecreasing hxy.1
      exact ((not_lt_of_ge hbAbove.le) ((hSide ha hb).mp haBelow)).elim

/-- A least classified hit of a positive completed-graph level is increasing. -/
theorem literalJuilletFirstCrossingIncreasing
    {mu nu : FiniteMeasure Real} {h x : Real}
    (hPositive : 0 < h)
    (hClassified :
      ∀ z, (z, h) ∈ generalizedCumulativeGraph mu nu ->
        Xor (IsGoodIncreasingCrossing mu nu z h)
          (IsGoodDecreasingCrossing mu nu z h))
    (hx :
      IsLeast
        {z : Real | (z, h) ∈ generalizedCumulativeGraph mu nu} x) :
    IsGoodIncreasingCrossing mu nu x h := by
  rcases hClassified x hx.1 with
      ⟨hxIncreasing, _hxNotDecreasing⟩ |
      ⟨hxDecreasing, _hxNotIncreasing⟩
  · exact hxIncreasing
  · obtain ⟨z, hz, hzAbove⟩ :=
      goodDecreasingCrossing_left_point hxDecreasing
        (sub_lt_self x one_pos)
    obtain ⟨a, haz, haBelow⟩ :=
      exists_left_tail_below mu nu hPositive (x := z)
    have hAvoid :
        ∀ q ∈ Iio x,
          (q, h) ∉ generalizedCumulativeGraph mu nu := by
      intro q hqx hqGraph
      exact (not_lt_of_ge (hx.2 hqGraph)) hqx
    have hSide :=
      signedCumulative_side_constant_on_preconnected
        mu nu h isPreconnected_Iio hAvoid
        (show a ∈ Iio x from haz.trans hz.2)
        (show z ∈ Iio x from hz.2)
    exact ((not_lt_of_ge hzAbove.le) (hSide.mp haBelow)).elim

/-- A greatest classified hit of a positive level is decreasing when the
finite marginals have equal total mass. -/
theorem literalJuilletLastCrossingDecreasing
    {mu nu : FiniteMeasure Real} {h y : Real}
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < h)
    (hClassified :
      ∀ z, (z, h) ∈ generalizedCumulativeGraph mu nu ->
        Xor (IsGoodIncreasingCrossing mu nu z h)
          (IsGoodDecreasingCrossing mu nu z h))
    (hy :
      IsGreatest
        {z : Real | (z, h) ∈ generalizedCumulativeGraph mu nu} y) :
    IsGoodDecreasingCrossing mu nu y h := by
  rcases hClassified y hy.1 with
      ⟨hyIncreasing, _hyNotDecreasing⟩ |
      ⟨hyDecreasing, _hyNotIncreasing⟩
  · obtain ⟨z, hz, hzAbove⟩ :=
      goodIncreasingCrossing_right_point hyIncreasing
        (lt_add_of_pos_right y one_pos)
    obtain ⟨b, hzb, hbBelow⟩ :=
      exists_right_tail_below mu nu hMass hPositive (x := z)
    have hAvoid :
        ∀ q ∈ Ioi y,
          (q, h) ∉ generalizedCumulativeGraph mu nu := by
      intro q hyq hqGraph
      exact (not_lt_of_ge (hy.2 hqGraph)) hyq
    have hSide :=
      signedCumulative_side_constant_on_preconnected
        mu nu h isPreconnected_Ioi hAvoid
        (show z ∈ Ioi y from hz.1)
        (show b ∈ Ioi y from hz.1.trans hzb)
    exact ((not_lt_of_ge hzAbove.le) (hSide.mpr hbBelow)).elim
  · exact hyDecreasing

/-- The left endpoint consecutive to a fixed right endpoint is unique. -/
theorem consecutiveAtLevelLeftUnique
    (mu nu : FiniteMeasure Real) (h x x' y : Real)
    (hxy : AreConsecutiveAtLevel mu nu h x y)
    (hx'y : AreConsecutiveAtLevel mu nu h x' y) :
    x = x' := by
  rcases lt_trichotomy x x' with hxx' | hEq | hx'x
  · exact
      (hxy.2.2.2 x' ⟨hxx', hx'y.1⟩ hx'y.2.1).elim
  · exact hEq
  · exact
      (hx'y.2.2.2 x ⟨hx'x, hxy.1⟩ hxy.2.1).elim

private theorem consecutiveAtLevelRightUnique'
    (mu nu : FiniteMeasure Real) (h x y y' : Real)
    (hxy : AreConsecutiveAtLevel mu nu h x y)
    (hxy' : AreConsecutiveAtLevel mu nu h x y') :
    y = y' := by
  rcases lt_trichotomy y y' with hyy' | hEq | hy'y
  · exact
      (hxy'.2.2.2 y ⟨hxy.1, hyy'⟩ hxy.2.2.1).elim
  · exact hEq
  · exact
      (hxy.2.2.2 y' ⟨hxy'.1, hy'y⟩ hxy'.2.2.1).elim

private theorem exists_level_hit_right_of_increasing
    {mu nu : FiniteMeasure Real} {h x : Real}
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < h)
    (hxIncreasing : IsGoodIncreasingCrossing mu nu x h) :
    ∃ y, x < y /\
      (y, h) ∈ generalizedCumulativeGraph mu nu := by
  by_contra hNone
  push Not at hNone
  obtain ⟨z, hz, hzAbove⟩ :=
    goodIncreasingCrossing_right_point hxIncreasing
      (lt_add_of_pos_right x one_pos)
  obtain ⟨b, hzb, hbBelow⟩ :=
    exists_right_tail_below mu nu hMass hPositive (x := z)
  have hAvoid :
      ∀ q ∈ Ioi x,
        (q, h) ∉ generalizedCumulativeGraph mu nu :=
    fun q hxq => hNone q hxq
  have hSide :=
    signedCumulative_side_constant_on_preconnected
      mu nu h isPreconnected_Ioi hAvoid
      (show z ∈ Ioi x from hz.1)
      (show b ∈ Ioi x from hz.1.trans hzb)
  exact (not_lt_of_ge hzAbove.le) (hSide.mpr hbBelow)

private theorem exists_level_hit_left_of_decreasing
    {mu nu : FiniteMeasure Real} {h y : Real}
    (hPositive : 0 < h)
    (hyDecreasing : IsGoodDecreasingCrossing mu nu y h) :
    ∃ x, x < y /\
      (x, h) ∈ generalizedCumulativeGraph mu nu := by
  by_contra hNone
  push Not at hNone
  obtain ⟨z, hz, hzAbove⟩ :=
    goodDecreasingCrossing_left_point hyDecreasing
      (sub_lt_self y one_pos)
  obtain ⟨a, haz, haBelow⟩ :=
    exists_left_tail_below mu nu hPositive (x := z)
  have hAvoid :
      ∀ q ∈ Iio y,
        (q, h) ∉ generalizedCumulativeGraph mu nu := by
    intro q hqy hqGraph
    exact hNone q hqy hqGraph
  have hSide :=
    signedCumulative_side_constant_on_preconnected
      mu nu h isPreconnected_Iio hAvoid
      (show a ∈ Iio y from haz.trans hz.2)
      (show z ∈ Iio y from hz.2)
  exact (not_lt_of_ge hzAbove.le) (hSide.mp haBelow)

/-- Every increasing crossing in a finite classified positive level has one
and only one consecutive decreasing crossing to its right. -/
theorem goodIncreasingCrossing_existsUnique_consecutiveDecreasing
    {mu nu : FiniteMeasure Real} {h x : Real}
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < h)
    (hFinite :
      {z : Real |
        (z, h) ∈ generalizedCumulativeGraph mu nu}.Finite)
    (hClassified :
      ∀ z, (z, h) ∈ generalizedCumulativeGraph mu nu ->
        Xor (IsGoodIncreasingCrossing mu nu z h)
          (IsGoodDecreasingCrossing mu nu z h))
    (hxIncreasing : IsGoodIncreasingCrossing mu nu x h) :
    ∃! y,
      IsGoodDecreasingCrossing mu nu y h /\
        AreConsecutiveAtLevel mu nu h x y := by
  let rightHits : Set Real :=
    {y |
      x < y /\
        (y, h) ∈ generalizedCumulativeGraph mu nu}
  have hRightFinite : rightHits.Finite :=
    hFinite.subset fun y hy => hy.2
  have hRightNonempty : rightHits.Nonempty :=
    exists_level_hit_right_of_increasing
      hMass hPositive hxIncreasing
  have hRightFinsetNonempty :
      hRightFinite.toFinset.Nonempty :=
    hRightFinite.toFinset_nonempty.mpr hRightNonempty
  let y :=
    hRightFinite.toFinset.min' hRightFinsetNonempty
  have hyRight : y ∈ rightHits := by
    exact hRightFinite.mem_toFinset.mp
      (Finset.min'_mem _ hRightFinsetNonempty)
  have hyLeast :
      ∀ z ∈ rightHits, y ≤ z := by
    intro z hz
    exact Finset.min'_le _ z
      (hRightFinite.mem_toFinset.mpr hz)
  have hConsecutive :
      AreConsecutiveAtLevel mu nu h x y := by
    refine ⟨hyRight.1, hxIncreasing.1, hyRight.2, ?_⟩
    intro z hz hGraph
    have hyz := hyLeast z ⟨hz.1, hGraph⟩
    exact (not_lt_of_ge hyz) hz.2
  have hyDecreasing :
      IsGoodDecreasingCrossing mu nu y h := by
    rcases
        literalJuilletConsecutiveCrossingsAlternate
          hClassified hConsecutive with
      ⟨hPair, _hNotOpposite⟩ | ⟨hPair, _hNotForward⟩
    · exact hPair.2
    · exact
        (goodIncreasingCrossing_not_goodDecreasingCrossing
          mu nu x h hxIncreasing hPair.1).elim
  refine ⟨y, ⟨hyDecreasing, hConsecutive⟩, ?_⟩
  intro y' hy'
  exact consecutiveAtLevelRightUnique'
    mu nu h x y' y hy'.2 hConsecutive

/-- Every decreasing crossing in a finite classified positive level is the
target of one and only one consecutive increasing crossing. -/
theorem goodDecreasingCrossing_existsUnique_consecutiveIncreasing
    {mu nu : FiniteMeasure Real} {h y : Real}
    (hPositive : 0 < h)
    (hFinite :
      {z : Real |
        (z, h) ∈ generalizedCumulativeGraph mu nu}.Finite)
    (hClassified :
      ∀ z, (z, h) ∈ generalizedCumulativeGraph mu nu ->
        Xor (IsGoodIncreasingCrossing mu nu z h)
          (IsGoodDecreasingCrossing mu nu z h))
    (hyDecreasing : IsGoodDecreasingCrossing mu nu y h) :
    ∃! x,
      IsGoodIncreasingCrossing mu nu x h /\
        AreConsecutiveAtLevel mu nu h x y := by
  let leftHits : Set Real :=
    {x |
      x < y /\
        (x, h) ∈ generalizedCumulativeGraph mu nu}
  have hLeftFinite : leftHits.Finite :=
    hFinite.subset fun x hx => hx.2
  have hLeftNonempty : leftHits.Nonempty :=
    exists_level_hit_left_of_decreasing
      hPositive hyDecreasing
  have hLeftFinsetNonempty :
      hLeftFinite.toFinset.Nonempty :=
    hLeftFinite.toFinset_nonempty.mpr hLeftNonempty
  let x :=
    hLeftFinite.toFinset.max' hLeftFinsetNonempty
  have hxLeft : x ∈ leftHits := by
    exact hLeftFinite.mem_toFinset.mp
      (Finset.max'_mem _ hLeftFinsetNonempty)
  have hxGreatest :
      ∀ z ∈ leftHits, z ≤ x := by
    intro z hz
    exact Finset.le_max' _ z
      (hLeftFinite.mem_toFinset.mpr hz)
  have hConsecutive :
      AreConsecutiveAtLevel mu nu h x y := by
    refine ⟨hxLeft.1, hxLeft.2, hyDecreasing.1, ?_⟩
    intro z hz hGraph
    have hzx := hxGreatest z ⟨hz.2, hGraph⟩
    exact (not_lt_of_ge hzx) hz.1
  have hxIncreasing :
      IsGoodIncreasingCrossing mu nu x h := by
    rcases
        literalJuilletConsecutiveCrossingsAlternate
          hClassified hConsecutive with
      ⟨hPair, _hNotOpposite⟩ | ⟨hPair, _hNotForward⟩
    · exact hPair.1
    · exact
        (goodIncreasingCrossing_not_goodDecreasingCrossing
          mu nu y h hPair.2 hyDecreasing).elim
  refine ⟨x, ⟨hxIncreasing, hConsecutive⟩, ?_⟩
  intro x' hx'
  exact consecutiveAtLevelLeftUnique
    mu nu h x' x y hx'.2 hConsecutive

/-- The finite ordered facts needed by the literal Juillet pairing at one
positive completed-graph level. -/
structure LiteralJuilletLevelAlternationFacts
    (mu nu : FiniteMeasure Real) (h : Real) : Prop where
  first_increasing :
    ∀ x,
      IsLeast
        {z : Real |
          (z, h) ∈ generalizedCumulativeGraph mu nu} x ->
        IsGoodIncreasingCrossing mu nu x h
  last_decreasing :
    ∀ y,
      IsGreatest
        {z : Real |
          (z, h) ∈ generalizedCumulativeGraph mu nu} y ->
        IsGoodDecreasingCrossing mu nu y h
  consecutive_alternates :
    ∀ x y, AreConsecutiveAtLevel mu nu h x y ->
      Xor
        (IsGoodIncreasingCrossing mu nu x h /\
          IsGoodDecreasingCrossing mu nu y h)
        (IsGoodDecreasingCrossing mu nu x h /\
          IsGoodIncreasingCrossing mu nu y h)
  increasing_pairs :
    ∀ x, IsGoodIncreasingCrossing mu nu x h ->
      ∃! y,
        IsGoodDecreasingCrossing mu nu y h /\
          AreConsecutiveAtLevel mu nu h x y
  decreasing_is_paired :
    ∀ y, IsGoodDecreasingCrossing mu nu y h ->
      ∃! x,
        IsGoodIncreasingCrossing mu nu x h /\
          AreConsecutiveAtLevel mu nu h x y

/-- Equal mass and regularity give start-increasing, strict alternation,
end-decreasing, and the two unique pairing statements. Stochastic order is
retained in the signature used by the literal Juillet construction; the
levelwise conclusion is in fact stronger and does not need it. -/
theorem literalJuilletLevelAlternation
    {mu nu : FiniteMeasure Real} {h : Real}
    (hMass : mu.mass = nu.mass)
    (_hOrder : StochasticallyDominates nu mu)
    (hRegular : IsJuilletRegularPositiveLevel mu nu h) :
    LiteralJuilletLevelAlternationFacts mu nu h where
  first_increasing :=
    fun _ hx =>
      literalJuilletFirstCrossingIncreasing
        hRegular.1 hRegular.2.2 hx
  last_decreasing :=
    fun _ hy =>
      literalJuilletLastCrossingDecreasing
        hMass hRegular.1 hRegular.2.2 hy
  consecutive_alternates :=
    fun _ _ hxy =>
      literalJuilletConsecutiveCrossingsAlternate
        hRegular.2.2 hxy
  increasing_pairs :=
    fun _ hx =>
      goodIncreasingCrossing_existsUnique_consecutiveDecreasing
        hMass hRegular.1 hRegular.2.1 hRegular.2.2 hx
  decreasing_is_paired :=
    fun _ hy =>
      goodDecreasingCrossing_existsUnique_consecutiveIncreasing
        hRegular.1 hRegular.2.1 hRegular.2.2 hy

private theorem finiteCouplingMarginalsHaveEqualMass
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) :
    mu.mass = nu.mass := by
  have hFirst :
      (firstMarginal gamma.plan).mass = gamma.plan.mass := by
    simp [firstMarginal, FiniteMeasure.mass,
      FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ]
  have hSecond :
      (secondMarginal gamma.plan).mass = gamma.plan.mass := by
    simp [secondMarginal, FiniteMeasure.mass,
      FiniteMeasure.map_apply _ measurable_snd MeasurableSet.univ]
  calc
    mu.mass = (firstMarginal gamma.plan).mass :=
      congrArg FiniteMeasure.mass gamma.property.1.symm
    _ = gamma.plan.mass := hFirst
    _ = (secondMarginal gamma.plan).mass := hSecond.symm
    _ = nu.mass :=
      congrArg FiniteMeasure.mass gamma.property.2

/-- Coupling marginals automatically satisfy the equal-mass hypothesis of
the finite regular-level alternation theorem. -/
theorem literalJuilletLevelAlternation_of_coupling
    {mu nu : FiniteMeasure Real} {h : Real}
    (gamma : FiniteCoupling mu nu)
    (hOrder : StochasticallyDominates nu mu)
    (hRegular : IsJuilletRegularPositiveLevel mu nu h) :
    LiteralJuilletLevelAlternationFacts mu nu h :=
  literalJuilletLevelAlternation
    (finiteCouplingMarginalsHaveEqualMass gamma)
    hOrder hRegular

end ConcaveOTLimit
