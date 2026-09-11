import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Support
import Theorems.Thm_ConcaveOTLimit_strictCrossedForwardOfDistanceTieOnCarrier

open MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- A strict failure of the secondary target-swap inequality at two
carrier-separated topological-support points persists with a uniform positive
gap on disjoint positive-mass open blocks. -/
theorem existsPositiveDisjointSwapBlocks
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    {A : Set Real}
    {p q : Real × Real}
    (hProfile : AdmissibleStrictlyConcaveProfile profile)
    (hpSupport :
      p ∈ Measure.support
        (gamma.plan : Measure (Real × Real)))
    (hqSupport :
      q ∈ Measure.support
        (gamma.plan : Measure (Real × Real)))
    (hpCarrier : p ∈ A ×ˢ Aᶜ)
    (hqCarrier : q ∈ A ×ˢ Aᶜ)
    (hpForward : p.1 < p.2)
    (hqForward : q.1 < q.2)
    (hTie :
      dist p.1 p.2 + dist q.1 q.2 =
        dist p.1 q.2 + dist q.1 p.2)
    (hFailure :
      profile (dist p.1 q.2) + profile (dist q.1 p.2) <
        profile (dist p.1 p.2) + profile (dist q.1 q.2)) :
    exists U V : Set (Real × Real), exists delta : Real,
      IsOpen U /\
      MeasurableSet U /\
      p ∈ U /\
      IsOpen V /\
      MeasurableSet V /\
      q ∈ V /\
      Disjoint U V /\
      0 < (gamma.plan.restrict U).mass /\
      0 < (gamma.plan.restrict V).mass /\
      0 < delta /\
      forall r, r ∈ U -> forall s, s ∈ V ->
        r.1 < s.2 /\
        s.1 < r.2 /\
        delta <=
          profile (dist r.1 r.2) + profile (dist s.1 s.2) -
            (profile (dist r.1 s.2) +
              profile (dist s.1 r.2)) := by
  have hCrossed : p.1 < q.2 ∧ q.1 < p.2 :=
    strictCrossedForwardOfDistanceTieOnCarrier
      hpCarrier.1 hpCarrier.2 hqCarrier.1 hqCarrier.2
      hpForward hqForward hTie
  have hpDistance : 0 < dist p.1 p.2 :=
    dist_pos.mpr (ne_of_lt hpForward)
  have hqDistance : 0 < dist q.1 q.2 :=
    dist_pos.mpr (ne_of_lt hqForward)
  have hpqDistance : 0 < dist p.1 q.2 :=
    dist_pos.mpr (ne_of_lt hCrossed.1)
  have hqpDistance : 0 < dist q.1 p.2 :=
    dist_pos.mpr (ne_of_lt hCrossed.2)
  have hProfileContinuousAt :
      forall {d : Real}, 0 < d -> ContinuousAt profile d := by
    intro d hd
    have hdInterior : d ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici, mem_Ioi] using hd
    exact
      (hProfile.1.concaveOn.continuousOn_interior
        d hdInterior).continuousAt
        (isOpen_interior.mem_nhds hdInterior)
  let gap : ((Real × Real) × (Real × Real)) -> Real :=
    fun z =>
      profile (dist z.1.1 z.1.2) +
          profile (dist z.2.1 z.2.2) -
        (profile (dist z.1.1 z.2.2) +
          profile (dist z.2.1 z.1.2))
  have hpTerm :
      ContinuousAt
        (fun z : (Real × Real) × (Real × Real) =>
          profile (dist z.1.1 z.1.2)) (p, q) :=
    (hProfileContinuousAt hpDistance).comp_of_eq
      (show
        ContinuousAt
          (fun z : (Real × Real) × (Real × Real) =>
            dist z.1.1 z.1.2) (p, q) by
        fun_prop)
      rfl
  have hqTerm :
      ContinuousAt
        (fun z : (Real × Real) × (Real × Real) =>
          profile (dist z.2.1 z.2.2)) (p, q) :=
    (hProfileContinuousAt hqDistance).comp_of_eq
      (show
        ContinuousAt
          (fun z : (Real × Real) × (Real × Real) =>
            dist z.2.1 z.2.2) (p, q) by
        fun_prop)
      rfl
  have hpqTerm :
      ContinuousAt
        (fun z : (Real × Real) × (Real × Real) =>
          profile (dist z.1.1 z.2.2)) (p, q) :=
    (hProfileContinuousAt hpqDistance).comp_of_eq
      (show
        ContinuousAt
          (fun z : (Real × Real) × (Real × Real) =>
            dist z.1.1 z.2.2) (p, q) by
        fun_prop)
      rfl
  have hqpTerm :
      ContinuousAt
        (fun z : (Real × Real) × (Real × Real) =>
          profile (dist z.2.1 z.1.2)) (p, q) :=
    (hProfileContinuousAt hqpDistance).comp_of_eq
      (show
        ContinuousAt
          (fun z : (Real × Real) × (Real × Real) =>
            dist z.2.1 z.1.2) (p, q) by
        fun_prop)
      rfl
  have hGapContinuous : ContinuousAt gap (p, q) := by
    dsimp only [gap]
    exact (hpTerm.add hqTerm).sub (hpqTerm.add hqpTerm)
  have hGapPositive : 0 < gap (p, q) := by
    dsimp only [gap]
    exact sub_pos.mpr hFailure
  let delta : Real := gap (p, q) / 2
  have hDeltaPositive : 0 < delta := by
    dsimp only [delta]
    exact half_pos hGapPositive
  have hDeltaLt : delta < gap (p, q) := by
    dsimp only [delta]
    exact half_lt_self hGapPositive
  have hFirstCrossedEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        z.1.1 < z.2.2 := by
    have hOpen :
        IsOpen
          {z : (Real × Real) × (Real × Real) |
            z.1.1 < z.2.2} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    exact hOpen.mem_nhds hCrossed.1
  have hSecondCrossedEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        z.2.1 < z.1.2 := by
    have hOpen :
        IsOpen
          {z : (Real × Real) × (Real × Real) |
            z.2.1 < z.1.2} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    exact hOpen.mem_nhds hCrossed.2
  have hGapEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        delta < gap z :=
    hGapContinuous (Ioi_mem_nhds hDeltaLt)
  have hGoodEventually :
      ∀ᶠ z : (Real × Real) × (Real × Real) in 𝓝 (p, q),
        z.1.1 < z.2.2 /\
          z.2.1 < z.1.2 /\
          delta <= gap z := by
    filter_upwards
      [hFirstCrossedEventually, hSecondCrossedEventually,
        hGapEventually] with z hzFirst hzSecond hzGap
    exact ⟨hzFirst, hzSecond, hzGap.le⟩
  obtain
      ⟨U0, V0, hU0Open, hpU0, hV0Open, hqV0, hU0V0Good⟩ :=
    mem_nhds_prod_iff'.mp hGoodEventually
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact (lt_irrefl _ hFailure)
  obtain
      ⟨Up, Vq, hUpOpen, hVqOpen, hpUp, hqVq, hSeparated⟩ :=
    t2_separation hpq
  let U : Set (Real × Real) := U0 ∩ Up
  let V : Set (Real × Real) := V0 ∩ Vq
  have hUOpen : IsOpen U := hU0Open.inter hUpOpen
  have hVOpen : IsOpen V := hV0Open.inter hVqOpen
  have hpU : p ∈ U := ⟨hpU0, hpUp⟩
  have hqV : q ∈ V := ⟨hqV0, hqVq⟩
  have hUVDisjoint : Disjoint U V :=
    hSeparated.mono inter_subset_right inter_subset_right
  have hUMeasurePositive :
      0 <
        (gamma.plan : Measure (Real × Real)) U :=
    (Measure.mem_support_iff_forall p).mp hpSupport U
      (hUOpen.mem_nhds hpU)
  have hVMeasurePositive :
      0 <
        (gamma.plan : Measure (Real × Real)) V :=
    (Measure.mem_support_iff_forall q).mp hqSupport V
      (hVOpen.mem_nhds hqV)
  have hUPlanPositive : 0 < gamma.plan U := by
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (gamma.plan : Measure (Real × Real)) U = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null gamma.plan U).mp hZero
    exact hUMeasurePositive.ne' hMeasureZero
  have hVPlanPositive : 0 < gamma.plan V := by
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (gamma.plan : Measure (Real × Real)) V = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null gamma.plan V).mp hZero
    exact hVMeasurePositive.ne' hMeasureZero
  have hURestrictPositive :
      0 < (gamma.plan.restrict U).mass := by
    simpa only [FiniteMeasure.restrict_mass] using hUPlanPositive
  have hVRestrictPositive :
      0 < (gamma.plan.restrict V).mass := by
    simpa only [FiniteMeasure.restrict_mass] using hVPlanPositive
  refine
    ⟨U, V, delta, hUOpen, hUOpen.measurableSet, hpU,
      hVOpen, hVOpen.measurableSet, hqV, hUVDisjoint,
      hURestrictPositive, hVRestrictPositive, hDeltaPositive, ?_⟩
  intro r hr s hs
  have hrs : (r, s) ∈ U0 ×ˢ V0 := ⟨hr.1, hs.1⟩
  exact hU0V0Good hrs

end ConcaveOTLimit
