import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real))
    gamma.property.1

private theorem measurePreservingSnd
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (Real × Real)) (nu : Measure Real) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real))
    gamma.property.2

private theorem oppositeMonotoneArchesCannotCrossCutDirect
    {x y x' y' t : Real}
    (hBackward : y ≤ t ∧ t < x)
    (hForward : x' < t ∧ t < y')
    (hNoCross : ArchesDoNotCross (x, y) (x', y'))
    (hNoConnect : ArchesDoNotConnect (x, y) (x', y'))
    (hNoConnectRev : ArchesDoNotConnect (x', y') (x, y))
    (hOrientation : NestedArchesHaveSameOrientation (x, y) (x', y'))
    (hOrientationRev :
      NestedArchesHaveSameOrientation (x', y') (x, y)) :
    False := by
  have hyx : y < x := hBackward.1.trans_lt hBackward.2
  have hx'y' : x' < y' := hForward.1.trans hForward.2
  have hLengths :
      0 < min |y - x| |y' - x'| := by
    apply lt_min
    · exact abs_pos.mpr (sub_ne_zero.mpr hyx.ne)
    · exact abs_pos.mpr (sub_ne_zero.mpr hx'y'.ne')
  have hNotYX' : y ≠ x' := hNoConnect hLengths
  have hNotY'X : y' ≠ x :=
    hNoConnectRev (by simpa [min_comm] using hLengths)
  have htBackward : t ∈ uIcc x y :=
    mem_uIcc_of_ge hBackward.1 hBackward.2.le
  have htForward : t ∈ uIcc x' y' :=
    mem_uIcc_of_le hForward.1.le hForward.2.le
  have hMin : t < min x y' := lt_min hBackward.2 hForward.2
  let s : Real := (t + min x y') / 2
  have hts : t < s := by
    dsimp [s]
    linarith
  have hsMin : s < min x y' := by
    dsimp [s]
    linarith
  have hsBackward : s ∈ uIcc x y :=
    mem_uIcc_of_ge (hBackward.1.trans hts.le)
      (hsMin.trans_le (min_le_left _ _)).le
  have hsForward : s ∈ uIcc x' y' :=
    mem_uIcc_of_le (hForward.1.le.trans hts.le)
      (hsMin.trans_le (min_le_right _ _)).le
  rcases hNoCross with
    hDisjoint | hSingleton | hBackwardSubset | hForwardSubset
  · exact Set.disjoint_left.1 hDisjoint htBackward htForward
  · obtain ⟨z, hz⟩ := hSingleton
    have htEq : t = z := by
      have : t ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨htBackward, htForward⟩
      simpa using this
    have hsEq : s = z := by
      have : s ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨hsBackward, hsForward⟩
      simpa using this
    linarith
  · have hyMem : y ∈ uIcc x' y' :=
      hBackwardSubset right_mem_uIcc
    have hxMem : x ∈ uIcc x' y' :=
      hBackwardSubset left_mem_uIcc
    rw [uIcc_of_le hx'y'.le] at hyMem hxMem
    have hx'y : x' < y :=
      lt_of_le_of_ne hyMem.1 (Ne.symm hNotYX')
    have hxy' : x < y' :=
      lt_of_le_of_ne hxMem.2 (Ne.symm hNotY'X)
    have hStrictSubset : uIcc x y ⊆ uIoo x' y' := by
      intro z hz
      rw [uIcc_comm, uIcc_of_le hyx.le] at hz
      rw [uIoo_of_le hx'y'.le]
      exact ⟨hx'y.trans_le hz.1, hz.2.trans_lt hxy'⟩
    have hProduct := hOrientationRev hStrictSubset
    have hForwardDisplacement : 0 < y' - x' :=
      sub_pos.mpr hx'y'
    have hBackwardDisplacement : y - x < 0 :=
      sub_neg.mpr hyx
    nlinarith
  · have hx'Mem : x' ∈ uIcc x y :=
      hForwardSubset left_mem_uIcc
    have hy'Mem : y' ∈ uIcc x y :=
      hForwardSubset right_mem_uIcc
    rw [uIcc_comm, uIcc_of_le hyx.le] at hx'Mem hy'Mem
    have hyx' : y < x' :=
      lt_of_le_of_ne hx'Mem.1 hNotYX'
    have hy'x : y' < x :=
      lt_of_le_of_ne hy'Mem.2 hNotY'X
    have hStrictSubset : uIcc x' y' ⊆ uIoo x y := by
      intro z hz
      rw [uIcc_of_le hx'y'.le] at hz
      rw [uIoo_comm, uIoo_of_le hyx.le]
      exact ⟨hyx'.trans_le hz.1, hz.2.trans_lt hy'x⟩
    have hProduct := hOrientation hStrictSubset
    have hForwardDisplacement : 0 < y' - x' :=
      sub_pos.mpr hx'y'
    have hBackwardDisplacement : y - x < 0 :=
      sub_neg.mpr hyx
    nlinarith

/-- Direct, assumption-free version of forwardness for a Juillet
monotone-arch plan.  This proof uses only a rational cut argument, the two
marginals, source atomlessness, and stochastic order. -/
theorem isForwardPlanOfJuilletExcursionPlanDirect
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    IsForwardPlan gamma := by
  rcases hExcursion with
    ⟨_hCoupling, support, _hSupportMeasurable, hFull, hMonotone⟩
  by_contra hNotForward
  change ¬(∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≤ z.2)
    at hNotForward
  let backward : Set (Real × Real) := {z | z.2 < z.1}
  let backwardAt : Rat → Set (Real × Real) :=
    fun q => {z | z.2 ≤ (q : Real) ∧ (q : Real) < z.1}
  have hBackwardSubset :
      backward ⊆ ⋃ q : Rat, backwardAt q := by
    intro z hz
    change z.2 < z.1 at hz
    obtain ⟨q, hzq, hqz⟩ := exists_rat_btwn hz
    apply mem_iUnion.mpr
    exact ⟨q, hzq.le, hqz⟩
  have hBackwardMeasureNe :
      (gamma.plan : Measure (Real × Real)) backward ≠ 0 := by
    intro hZero
    apply hNotForward
    apply ae_iff.mpr
    simpa only [backward, not_le, setOf_mem_eq] using hZero
  have hUnionMeasureNe :
      (gamma.plan : Measure (Real × Real))
          (⋃ q : Rat, backwardAt q) ≠ 0 := by
    intro hZero
    exact hBackwardMeasureNe
      (measure_mono_null hBackwardSubset hZero)
  obtain ⟨q, hBackwardAtPos⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null hUnionMeasureNe
  let cut : Real := q
  let sourceLeft : Set (Real × Real) := {z | z.1 ≤ cut}
  let targetLeft : Set (Real × Real) := {z | z.2 ≤ cut}
  let forwardAt : Set (Real × Real) :=
    {z | z.1 ≤ cut ∧ cut < z.2}
  have hSourceLeftMeasurable : MeasurableSet sourceLeft :=
    measurableSet_le measurable_fst measurable_const
  have hTargetLeftMeasurable : MeasurableSet targetLeft :=
    measurableSet_le measurable_snd measurable_const
  have hForwardDiff : sourceLeft \ targetLeft = forwardAt := by
    ext z
    simp only [sourceLeft, targetLeft, forwardAt, mem_diff,
      mem_setOf_eq, not_le]
  have hBackwardDiff : targetLeft \ sourceLeft = backwardAt q := by
    ext z
    simp only [targetLeft, sourceLeft, backwardAt, cut, mem_diff,
      mem_setOf_eq, not_le]
  have hSourceMeasure :
      (gamma.plan : Measure (Real × Real)) sourceLeft =
        (mu : Measure Real) (Iic cut) := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceLeft =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) (Iic cut) := by
        rw [Measure.map_apply measurable_fst measurableSet_Iic]
        rfl
      _ = (mu : Measure Real) (Iic cut) := by
        rw [(measurePreservingFst gamma).map_eq]
  have hTargetMeasure :
      (gamma.plan : Measure (Real × Real)) targetLeft =
        (nu : Measure Real) (Iic cut) := by
    calc
      (gamma.plan : Measure (Real × Real)) targetLeft =
          Measure.map Prod.snd
            (gamma.plan : Measure (Real × Real)) (Iic cut) := by
        rw [Measure.map_apply measurable_snd measurableSet_Iic]
        rfl
      _ = (nu : Measure Real) (Iic cut) := by
        rw [(measurePreservingSnd gamma).map_eq]
  have hPlanOrder :
      (gamma.plan : Measure (Real × Real)) targetLeft ≤
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [hTargetMeasure, hSourceMeasure]
    exact hOrder cut
  have hSourceDecomp :
      (gamma.plan : Measure (Real × Real)) forwardAt +
          (gamma.plan : Measure (Real × Real))
            (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [← hForwardDiff]
    exact measure_diff_add_inter sourceLeft hTargetLeftMeasurable
  have hTargetDecomp :
      (gamma.plan : Measure (Real × Real)) (backwardAt q) +
          (gamma.plan : Measure (Real × Real))
            (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
    rw [← hBackwardDiff]
    simpa only [inter_comm] using
      (measure_diff_add_inter
        (μ := (gamma.plan : Measure (Real × Real)))
        targetLeft hSourceLeftMeasurable)
  have hBackwardLeForward :
      (gamma.plan : Measure (Real × Real)) (backwardAt q) ≤
        (gamma.plan : Measure (Real × Real)) forwardAt := by
    apply ENNReal.le_of_add_le_add_left
      (measure_ne_top
        (gamma.plan : Measure (Real × Real))
        (sourceLeft ∩ targetLeft))
    calc
      (gamma.plan : Measure (Real × Real)) (sourceLeft ∩ targetLeft) +
          (gamma.plan : Measure (Real × Real)) (backwardAt q) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
          rw [add_comm, hTargetDecomp]
      _ ≤ (gamma.plan : Measure (Real × Real)) sourceLeft :=
        hPlanOrder
      _ = (gamma.plan : Measure (Real × Real))
            (sourceLeft ∩ targetLeft) +
          (gamma.plan : Measure (Real × Real)) forwardAt := by
          rw [← hSourceDecomp, add_comm]
  have hForwardAtPos :
      0 < (gamma.plan : Measure (Real × Real)) forwardAt :=
    hBackwardAtPos.trans_le hBackwardLeForward
  let sourceAt : Set (Real × Real) := {z | z.1 = cut}
  have hSourceAtZero :
      (gamma.plan : Measure (Real × Real)) sourceAt = 0 := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceAt =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) {cut} := by
        rw [Measure.map_apply measurable_fst
          (measurableSet_singleton cut)]
        rfl
      _ = (mu : Measure Real) {cut} := by
        rw [(measurePreservingFst gamma).map_eq]
      _ = 0 := hAtomless cut
  have hStrictForwardAtPos :
      0 < (gamma.plan : Measure (Real × Real))
        (forwardAt \ sourceAt) := by
    rw [measure_diff_null hSourceAtZero]
    exact hForwardAtPos
  obtain ⟨backwardPoint, hBackwardPoint, hBackwardSupport⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      hBackwardAtPos.ne'
      (ae_restrict_of_ae hFull)
  obtain ⟨forwardPoint, hForwardPoint, hForwardSupport⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      hStrictForwardAtPos.ne'
      (ae_restrict_of_ae hFull)
  have hForwardSourceNe : forwardPoint.1 ≠ cut := by
    simpa only [sourceAt, mem_setOf_eq] using hForwardPoint.2
  have hForwardStrict : forwardPoint.1 < cut :=
    lt_of_le_of_ne hForwardPoint.1.1 hForwardSourceNe
  have hConditions :=
    hMonotone backwardPoint hBackwardSupport
      forwardPoint hForwardSupport
  have hConditionsRev :=
    hMonotone forwardPoint hForwardSupport
      backwardPoint hBackwardSupport
  exact oppositeMonotoneArchesCannotCrossCutDirect
    ⟨hBackwardPoint.1, hBackwardPoint.2⟩
    ⟨hForwardStrict, hForwardPoint.1.2⟩
    hConditions.1 hConditions.2.1 hConditionsRev.2.1
    hConditions.2.2 hConditionsRev.2.2

/-- The source points at which a set of arches has more than one target. -/
def monotoneArchBranchingSources (S : Set (Real × Real)) : Set Real :=
  {x | ∃ y y', (x, y) ∈ S ∧ (x, y') ∈ S ∧ y ≠ y'}

private def monotoneArchBranchingCode
    (S : Set (Real × Real)) (a b : Rat) : Set Real :=
  {x | ∃ y y',
    (x, y) ∈ S ∧ (x, y') ∈ S ∧
      x < (a : Real) ∧ (a : Real) < y ∧
      y < (b : Real) ∧ (b : Real) < y'}

private theorem interleavingArches_not_doNotCross
    {x x' y y' : Real}
    (hxx' : x < x') (hx'y : x' < y) (hyy' : y < y') :
    ¬ ArchesDoNotCross (x, y) (x', y') := by
  intro hNoCross
  have hx'First : x' ∈ uIcc x y :=
    mem_uIcc_of_le hxx'.le hx'y.le
  have hx'Second : x' ∈ uIcc x' y' :=
    left_mem_uIcc
  have hyFirst : y ∈ uIcc x y :=
    right_mem_uIcc
  have hySecond : y ∈ uIcc x' y' :=
    mem_uIcc_of_le hx'y.le hyy'.le
  rcases hNoCross with
    hDisjoint | hSingleton | hLeftSubset | hRightSubset
  · exact Set.disjoint_left.mp hDisjoint hx'First hx'Second
  · obtain ⟨z, hz⟩ := hSingleton
    have hx'z : x' = z := by
      have : x' ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨hx'First, hx'Second⟩
      simpa only [mem_singleton_iff] using this
    have hyz : y = z := by
      have : y ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨hyFirst, hySecond⟩
      simpa only [mem_singleton_iff] using this
    exact hx'y.ne (hx'z.trans hyz.symm)
  · have hxSecond :=
      hLeftSubset (left_mem_uIcc : x ∈ uIcc x y)
    rw [uIcc_of_le (hx'y.trans hyy').le] at hxSecond
    exact (not_le_of_gt hxx') hxSecond.1
  · have hy'First :=
      hRightSubset (right_mem_uIcc : y' ∈ uIcc x' y')
    rw [uIcc_of_le (hxx'.trans hx'y).le] at hy'First
    exact (not_le_of_gt hyy') hy'First.2

/-- In a strictly forward monotone-arch set, only countably many source
points can have more than one target. -/
theorem monotoneArchBranchingSources_countable
    (S : Set (Real × Real))
    (hStrict : ∀ {x y : Real}, (x, y) ∈ S → x < y)
    (hMonotone : IsMonotoneArchSet S) :
    (monotoneArchBranchingSources S).Countable := by
  have hCodeSubsingleton (a b : Rat) :
      (monotoneArchBranchingCode S a b).Subsingleton := by
    intro x hx x' hx'
    rcases hx with
      ⟨y, y', hxy, hxy', hxa, hay, hyb, hby'⟩
    rcases hx' with
      ⟨z, z', hxz, hxz', hx'a, haz, hzb, hbz'⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxx' | hx'x
    · exact interleavingArches_not_doNotCross
        hxx' (hx'a.trans hay) (hyb.trans hbz')
        (hMonotone (x, y) hxy (x', z') hxz').1
    · exact interleavingArches_not_doNotCross
        hx'x (hxa.trans haz) (hzb.trans hby')
        (hMonotone (x', z) hxz (x, y') hxy').1
  have hCodesCountable :
      (⋃ a : Rat, ⋃ b : Rat, monotoneArchBranchingCode S a b).Countable :=
    Set.countable_iUnion fun a =>
      Set.countable_iUnion fun b =>
        (hCodeSubsingleton a b).countable
  apply hCodesCountable.mono
  intro x hx
  rcases hx with ⟨y, y', hxy, hxy', hne⟩
  rcases lt_or_gt_of_ne hne with hyy' | hy'y
  · obtain ⟨a, hxa, hay⟩ :=
      exists_rat_btwn (hStrict hxy)
    obtain ⟨b, hyb, hby'⟩ :=
      exists_rat_btwn hyy'
    exact mem_iUnion_of_mem a <|
      mem_iUnion_of_mem b ⟨y, y', hxy, hxy', hxa, hay, hyb, hby'⟩
  · obtain ⟨a, hxa, hay'⟩ :=
      exists_rat_btwn (hStrict hxy')
    obtain ⟨b, hy'b, hby⟩ :=
      exists_rat_btwn hy'y
    exact mem_iUnion_of_mem a <|
      mem_iUnion_of_mem b ⟨y', y, hxy', hxy, hxa, hay', hy'b, hby⟩

/-- Removing the countably many branching source fibers from a measurable
strictly forward monotone-arch support leaves a measurable, full-mass support
on which the first projection is injective. -/
theorem existsFullMassFstInjOnSubsetOfStrictMonotoneArchSupport
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (S : Set (Real × Real))
    (hSMeasurable : MeasurableSet S)
    (hFull : IsSupported gamma S)
    (hStrict : ∀ {x y : Real}, (x, y) ∈ S → x < y)
    (hMonotone : IsMonotoneArchSet S) :
    ∃ G : Set (Real × Real),
      MeasurableSet G ∧
      IsSupported gamma G ∧
      G ⊆ S ∧
      Set.InjOn Prod.fst G := by
  let B : Set Real := monotoneArchBranchingSources S
  let G : Set (Real × Real) := S ∩ Prod.fst ⁻¹' Bᶜ
  have hBCountable : B.Countable :=
    monotoneArchBranchingSources_countable S hStrict hMonotone
  have hBMeasurable : MeasurableSet B :=
    hBCountable.measurableSet
  letI : NoAtoms (mu : Measure Real) := ⟨hAtomless⟩
  have hAvoid :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ∉ B :=
    (measurePreservingFst gamma).quasiMeasurePreserving.ae
      (hBCountable.ae_notMem (mu : Measure Real))
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · exact hSMeasurable.inter
      (hBMeasurable.compl.preimage measurable_fst)
  · filter_upwards [hFull, hAvoid] with z hzS hzB
    exact ⟨hzS, hzB⟩
  · exact inter_subset_left
  · intro p hp q hq hfst
    apply Prod.ext hfst
    by_contra hsnd
    have hqS : (p.1, q.2) ∈ S := by
      rw [hfst]
      exact hq.1
    have hpBranching : p.1 ∈ B :=
      ⟨p.2, q.2, hp.1, hqS, hsnd⟩
    exact hp.2 hpBranching

/-- Every Juillet monotone-arch plan under the paper's marginal assumptions
has a measurable full-mass, strictly forward, monotone support on which the
first projection is injective. -/
theorem existsFullMassFstInjOnSupportOfJuilletExcursionPlan
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    ∃ G : Set (Real × Real),
      MeasurableSet G ∧
      IsSupported gamma G ∧
      (∀ {x y : Real}, (x, y) ∈ G → x < y) ∧
      IsMonotoneArchSet G ∧
      Set.InjOn Prod.fst G := by
  have hForward : IsForwardPlan gamma :=
    isForwardPlanOfJuilletExcursionPlanDirect
      hAtomless hOrder hExcursion
  have hOffDiagonal :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ z.2 :=
    finiteCouplingAvoidsDiagonalOfMutuallySingular gamma hSingular
  have hStrict :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 < z.2 := by
    filter_upwards [hForward, hOffDiagonal] with z hzForward hzNe
    exact lt_of_le_of_ne hzForward hzNe
  rcases hExcursion with
    ⟨_hCoupling, support, hSupportMeasurable, hSupportFull,
      hSupportMonotone⟩
  let S : Set (Real × Real) :=
    support ∩ {z : Real × Real | z.1 < z.2}
  have hSMeasurable : MeasurableSet S :=
    hSupportMeasurable.inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hSFull : IsSupported gamma S := by
    filter_upwards [hSupportFull, hStrict] with z hzSupport hzStrict
    exact ⟨hzSupport, hzStrict⟩
  have hSStrict :
      ∀ {x y : Real}, (x, y) ∈ S → x < y :=
    fun {_ _} hxy => hxy.2
  have hSMonotone : IsMonotoneArchSet S :=
    fun p hp q hq => hSupportMonotone p hp.1 q hq.1
  obtain ⟨G, hGMeasurable, hGFull, hGS, hGInjective⟩ :=
    existsFullMassFstInjOnSubsetOfStrictMonotoneArchSupport
      gamma hAtomless S hSMeasurable hSFull hSStrict hSMonotone
  exact
    ⟨G, hGMeasurable, hGFull,
      fun {_ _} hxy => hSStrict (hGS hxy),
      fun p hp q hq => hSMonotone p (hGS hp) q (hGS hq),
      hGInjective⟩

/-- Paper Theorem 5, graphness part: under mutual singularity, atomlessness
of the source, and stochastic order, every plan satisfying Juillet's
monotone-arch condition is induced by a measurable map. -/
theorem juilletExcursionPlanIsGraph
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    ∃ T : Real → Real, IsGraphPlan gamma T := by
  obtain ⟨G, _hGMeasurable, hGFull, _hGStrict, _hGMonotone,
      hGInjective⟩ :=
    existsFullMassFstInjOnSupportOfJuilletExcursionPlan
      gamma hSingular hAtomless hOrder hExcursion
  exact existsGraphPlanOfSupportedFstInjOn
    gamma G hGInjective hGFull

end ConcaveOTLimit
