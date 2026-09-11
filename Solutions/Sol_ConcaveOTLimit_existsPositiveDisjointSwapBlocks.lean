import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Support
import Theorems.Thm_ConcaveOTLimit_strictCrossedForwardOfDistanceTieOnCarrier

open MeasureTheory Set Topology

open ConcaveOTLimit

theorem solution
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
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact (lt_irrefl _ hFailure)
  have hProfileContinuousOn :
      ContinuousOn profile (Ioi (0 : Real)) :=
    (hProfile.1.concaveOn.subset Ioi_subset_Ici_self
      (convex_Ioi (0 : Real))).continuousOn isOpen_Ioi
  have hComposeProfile :
      forall (f :
        ((Real × Real) × (Real × Real)) -> Real),
        ContinuousAt f (p, q) ->
        0 < f (p, q) ->
        ContinuousAt (fun z => profile (f z)) (p, q) := by
    intro f hf hPositive
    exact
      (hProfileContinuousOn.continuousAt
        (isOpen_Ioi.mem_nhds hPositive)).comp' hf
  have hpDistance : 0 < dist p.1 p.2 :=
    dist_pos.mpr (ne_of_lt hpForward)
  have hqDistance : 0 < dist q.1 q.2 :=
    dist_pos.mpr (ne_of_lt hqForward)
  have hpqDistance : 0 < dist p.1 q.2 :=
    dist_pos.mpr (ne_of_lt hCrossed.1)
  have hqpDistance : 0 < dist q.1 p.2 :=
    dist_pos.mpr (ne_of_lt hCrossed.2)
  let gap : (Real × Real) -> (Real × Real) -> Real :=
    fun r s =>
      profile (dist r.1 r.2) + profile (dist s.1 s.2) -
        (profile (dist r.1 s.2) + profile (dist s.1 r.2))
  have hGapContinuous :
      ContinuousAt
        (fun z : (Real × Real) × (Real × Real) =>
          gap z.1 z.2) (p, q) := by
    dsimp only [gap]
    exact
      ((hComposeProfile
          (fun z : (Real × Real) × (Real × Real) =>
            dist z.1.1 z.1.2)
          (by fun_prop) hpDistance).add
        (hComposeProfile
          (fun z : (Real × Real) × (Real × Real) =>
            dist z.2.1 z.2.2)
          (by fun_prop) hqDistance)).sub
        ((hComposeProfile
            (fun z : (Real × Real) × (Real × Real) =>
              dist z.1.1 z.2.2)
            (by fun_prop) hpqDistance).add
          (hComposeProfile
            (fun z : (Real × Real) × (Real × Real) =>
              dist z.2.1 z.1.2)
            (by fun_prop) hqpDistance))
  have hGapPositive : 0 < gap p q := by
    dsimp only [gap]
    exact sub_pos.mpr hFailure
  let delta : Real := gap p q / 2
  have hDeltaPositive : 0 < delta := by
    dsimp only [delta]
    exact half_pos hGapPositive
  have hDeltaLt : delta < gap p q := by
    dsimp only [delta]
    exact half_lt_self hGapPositive
  have hFirstCrossedNhd :
      {z : (Real × Real) × (Real × Real) |
        z.1.1 < z.2.2} ∈ 𝓝 (p, q) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) (by fun_prop)
    · exact hCrossed.1
  have hSecondCrossedNhd :
      {z : (Real × Real) × (Real × Real) |
        z.2.1 < z.1.2} ∈ 𝓝 (p, q) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) (by fun_prop)
    · exact hCrossed.2
  have hGapNhd :
      {z : (Real × Real) × (Real × Real) |
        delta <= gap z.1 z.2} ∈ 𝓝 (p, q) := by
    filter_upwards
      [hGapContinuous (Ioi_mem_nhds hDeltaLt)] with z hz
    exact hz.le
  let good : Set ((Real × Real) × (Real × Real)) :=
    {z |
      z.1.1 < z.2.2 /\
        z.2.1 < z.1.2 /\
        delta <= gap z.1 z.2}
  have hGoodNhd : good ∈ 𝓝 (p, q) := by
    dsimp only [good]
    filter_upwards
      [hFirstCrossedNhd, hSecondCrossedNhd, hGapNhd] with
      z hzFirst hzSecond hzGap
    exact ⟨hzFirst, hzSecond, hzGap⟩
  obtain
      ⟨Up, Vq, hUpOpen, hVqOpen, hpUp, hqVq, hSeparated⟩ :=
    t2_separation hpq
  have hSeparatedProductNhd :
      Up ×ˢ Vq ∈ 𝓝 (p, q) :=
    prod_mem_nhds (hUpOpen.mem_nhds hpUp)
      (hVqOpen.mem_nhds hqVq)
  have hCombinedNhd :
      good ∩ (Up ×ˢ Vq) ∈ 𝓝 (p, q) :=
    Filter.inter_mem hGoodNhd hSeparatedProductNhd
  obtain
      ⟨U, V, hUOpen, hpU, hVOpen, hqV, hUVCombined⟩ :=
    mem_nhds_prod_iff'.mp hCombinedNhd
  have hUSubset : U ⊆ Up := by
    intro r hr
    have hrq : (r, q) ∈ U ×ˢ V := ⟨hr, hqV⟩
    exact (hUVCombined hrq).2.1
  have hVSubset : V ⊆ Vq := by
    intro s hs
    have hps : (p, s) ∈ U ×ˢ V := ⟨hpU, hs⟩
    exact (hUVCombined hps).2.2
  have hUVDisjoint : Disjoint U V :=
    hSeparated.mono hUSubset hVSubset
  have restrictMassPositive
      (x : Real × Real)
      (hxSupport :
        x ∈ Measure.support
          (gamma.plan : Measure (Real × Real)))
      (W : Set (Real × Real))
      (hWOpen : IsOpen W) (hxW : x ∈ W) :
      0 < (gamma.plan.restrict W).mass := by
    have hMeasurePositive :
        0 < (gamma.plan : Measure (Real × Real)) W :=
      (Measure.mem_support_iff_forall x).mp hxSupport W
        (hWOpen.mem_nhds hxW)
    rw [FiniteMeasure.restrict_mass]
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (gamma.plan : Measure (Real × Real)) W = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null gamma.plan W).mp hZero
    exact hMeasurePositive.ne' hMeasureZero
  refine
    ⟨U, V, delta, hUOpen, hUOpen.measurableSet, hpU,
      hVOpen, hVOpen.measurableSet, hqV, hUVDisjoint,
      restrictMassPositive p hpSupport U hUOpen hpU,
      restrictMassPositive q hqSupport V hVOpen hqV,
      hDeltaPositive, ?_⟩
  intro r hr s hs
  have hrs : (r, s) ∈ U ×ˢ V := ⟨hr, hs⟩
  have hGood := (hUVCombined hrs).1
  simpa only [gap] using hGood
