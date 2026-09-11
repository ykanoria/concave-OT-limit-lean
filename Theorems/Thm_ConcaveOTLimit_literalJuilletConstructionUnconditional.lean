import Theorems.Thm_ConcaveOTLimit_existsForwardCouplingOfStochasticOrder
import Theorems.Thm_ConcaveOTLimit_existsJuilletExcursionPlan
import Theorems.Thm_ConcaveOTLimit_existsStrictMonotoneArchSupportOfJuilletExcursionPlan
import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer
import Theorems.Thm_ConcaveOTLimit_literalJuilletPairingConstruction
import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrixAtomless
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Constructions.UnitInterval

open Function MeasureTheory Set

namespace ConcaveOTLimit

noncomputable section

private theorem finiteMeasure_mass_map_of_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : FiniteMeasure X) {f : X -> Y} (hf : Measurable f) :
    (mu.map f).mass = mu.mass := by
  unfold FiniteMeasure.mass
  rw [FiniteMeasure.map_apply mu hf MeasurableSet.univ]
  simp

private noncomputable def mapFiniteCouplingLocal
    {X Y X' Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace X'] [MeasurableSpace Y']
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (f : X -> X') (g : Y -> Y')
    (hf : Measurable f) (hg : Measurable g) :
    FiniteCoupling (mu.map f) (nu.map g) := by
  refine ⟨gamma.plan.map (Prod.map f g), ?_, ?_⟩
  · apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.fst
          (Measure.map (Prod.map f g)
            (gamma.plan : Measure (X × Y))) =
        Measure.map f (mu : Measure X)
    rw [Measure.map_map measurable_fst (hf.prodMap hg)]
    change
      Measure.map (f ∘ Prod.fst)
          (gamma.plan : Measure (X × Y)) =
        Measure.map f (mu : Measure X)
    rw [← Measure.map_map hf measurable_fst]
    have hFirst :
        Measure.map Prod.fst
            (gamma.plan : Measure (X × Y)) =
          (mu : Measure X) := by
      simpa [firstMarginal, FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure X => (eta : Measure X))
        gamma.property.1
    rw [hFirst]
  · apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.snd
          (Measure.map (Prod.map f g)
            (gamma.plan : Measure (X × Y))) =
        Measure.map g (nu : Measure Y)
    rw [Measure.map_map measurable_snd (hf.prodMap hg)]
    change
      Measure.map (g ∘ Prod.snd)
          (gamma.plan : Measure (X × Y)) =
        Measure.map g (nu : Measure Y)
    rw [← Measure.map_map hg measurable_snd]
    have hSecond :
        Measure.map Prod.snd
            (gamma.plan : Measure (X × Y)) =
          (nu : Measure Y) := by
      simpa [secondMarginal, FiniteCoupling.plan] using congrArg
        (fun eta : FiniteMeasure Y => (eta : Measure Y))
        gamma.property.2
    rw [hSecond]

private theorem stochasticallyDominatesOfForwardLocal
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gamma) :
    StochasticallyDominates nu mu := by
  intro r
  change
    (nu : Measure Real) (Iic r) ≤
      (mu : Measure Real) (Iic r)
  have hFirst :
      Measure.map Prod.fst
          (gamma.plan : Measure (Real × Real)) =
        (mu : Measure Real) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Real => (eta : Measure Real))
      gamma.property.1
  have hSecond :
      Measure.map Prod.snd
          (gamma.plan : Measure (Real × Real)) =
        (nu : Measure Real) := by
    simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Real => (eta : Measure Real))
      gamma.property.2
  rw [← hSecond, ← hFirst,
    Measure.map_apply measurable_snd measurableSet_Iic,
    Measure.map_apply measurable_fst measurableSet_Iic]
  apply measure_mono_ae
  filter_upwards [hForward] with z hz
  exact fun hzr => hz.trans hzr

private theorem isAtomlessFinite_map_of_measurableEmbedding
    {mu : FiniteMeasure Real} {f : Real -> Real}
    (hAtomless : IsAtomlessFinite mu)
    (hf : MeasurableEmbedding f) :
    IsAtomlessFinite (mu.map f) := by
  intro y
  change Measure.map f (mu : Measure Real) {y} = 0
  rw [Measure.map_apply hf.measurable (measurableSet_singleton y)]
  by_cases hy : y ∈ range f
  · obtain ⟨x, rfl⟩ := hy
    have hPreimage : f ⁻¹' ({f x} : Set Real) = {x} := by
      ext z
      simp only [mem_preimage, mem_singleton_iff]
      exact hf.injective.eq_iff
    rw [hPreimage]
    exact hAtomless x
  · have hPreimage : f ⁻¹' ({y} : Set Real) = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hxy
      exact hy ⟨x, hxy⟩
    rw [hPreimage, measure_empty]

private theorem finiteMutuallySingular_map_of_measurableEmbedding
    {mu nu : FiniteMeasure Real} {f : Real -> Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hf : MeasurableEmbedding f) :
    FiniteMutuallySingular (mu.map f) (nu.map f) := by
  obtain ⟨A, hA, hMu, hNu⟩ := hSingular
  refine ⟨f '' A, hf.measurableSet_image' hA, ?_, ?_⟩
  · change Measure.map f (mu : Measure Real) (f '' A)ᶜ = 0
    rw [Measure.map_apply hf.measurable
      (hf.measurableSet_image' hA).compl, preimage_compl,
      hf.injective.preimage_image, hMu]
  · change Measure.map f (nu : Measure Real) (f '' A) = 0
    rw [Measure.map_apply hf.measurable
      (hf.measurableSet_image' hA), hf.injective.preimage_image, hNu]

private theorem sigmoid_mem_uIcc_iff (a b z : Real) :
    Real.sigmoid z ∈ uIcc (Real.sigmoid a) (Real.sigmoid b) ↔
      z ∈ uIcc a b := by
  simp only [mem_uIcc, Real.sigmoid_le_iff]

private theorem archesDoNotCross_of_sigmoid
    (p q : Real × Real)
    (hCross :
      ArchesDoNotCross
        (Real.sigmoid p.1, Real.sigmoid p.2)
        (Real.sigmoid q.1, Real.sigmoid q.2)) :
    ArchesDoNotCross p q := by
  rcases hCross with hDisjoint | hSingleton | hSubset | hSubset
  · left
    rw [Set.disjoint_left]
    intro z hp hq
    exact Set.disjoint_left.mp hDisjoint
      ((sigmoid_mem_uIcc_iff p.1 p.2 z).2 hp)
      ((sigmoid_mem_uIcc_iff q.1 q.2 z).2 hq)
  · obtain ⟨t, ht⟩ := hSingleton
    by_cases hNonempty : (uIcc p.1 p.2 ∩ uIcc q.1 q.2).Nonempty
    · obtain ⟨z, hp, hq⟩ := hNonempty
      right
      left
      refine ⟨z, ?_⟩
      ext w
      constructor
      · intro hw
        have hfw :
            Real.sigmoid w ∈
              uIcc (Real.sigmoid p.1) (Real.sigmoid p.2) ∩
                uIcc (Real.sigmoid q.1) (Real.sigmoid q.2) :=
          ⟨(sigmoid_mem_uIcc_iff p.1 p.2 w).2 hw.1,
            (sigmoid_mem_uIcc_iff q.1 q.2 w).2 hw.2⟩
        have hfz :
            Real.sigmoid z ∈
              uIcc (Real.sigmoid p.1) (Real.sigmoid p.2) ∩
                uIcc (Real.sigmoid q.1) (Real.sigmoid q.2) :=
          ⟨(sigmoid_mem_uIcc_iff p.1 p.2 z).2 hp,
            (sigmoid_mem_uIcc_iff q.1 q.2 z).2 hq⟩
        rw [ht] at hfw hfz
        have hEq : Real.sigmoid w = Real.sigmoid z := by
          simpa only [mem_singleton_iff] using hfw.trans hfz.symm
        exact (Real.sigmoid_injective hEq : w = z)
      · intro hw
        have hwz : w = z := by simpa only [mem_singleton_iff] using hw
        simpa only [hwz] using And.intro hp hq
    · left
      rw [Set.disjoint_left]
      intro z hp hq
      exact hNonempty ⟨z, hp, hq⟩
  · right
    right
    left
    intro z hz
    apply (sigmoid_mem_uIcc_iff q.1 q.2 z).1
    exact hSubset ((sigmoid_mem_uIcc_iff p.1 p.2 z).2 hz)
  · right
    right
    right
    intro z hz
    apply (sigmoid_mem_uIcc_iff p.1 p.2 z).1
    exact hSubset ((sigmoid_mem_uIcc_iff q.1 q.2 z).2 hz)

private theorem archesDoNotConnect_of_sigmoid
    (p q : Real × Real)
    (hConnect :
      ArchesDoNotConnect
        (Real.sigmoid p.1, Real.sigmoid p.2)
        (Real.sigmoid q.1, Real.sigmoid q.2)) :
    ArchesDoNotConnect p q := by
  intro hLength
  have hLength' := lt_min_iff.mp hLength
  have hpNe : p.2 ≠ p.1 := by
    intro hp
    rw [hp, sub_self, abs_zero] at hLength'
    exact (lt_irrefl 0 hLength'.1).elim
  have hqNe : q.2 ≠ q.1 := by
    intro hq
    rw [hq, sub_self, abs_zero] at hLength'
    exact (lt_irrefl 0 hLength'.2).elim
  have hMappedLength :
      0 <
        min
          |Real.sigmoid p.2 - Real.sigmoid p.1|
          |Real.sigmoid q.2 - Real.sigmoid q.1| := by
    rw [lt_min_iff]
    constructor
    · exact abs_pos.mpr
        (sub_ne_zero.mpr (Real.sigmoid_injective.ne hpNe))
    · exact abs_pos.mpr
        (sub_ne_zero.mpr (Real.sigmoid_injective.ne hqNe))
  have hMappedNe :
      Real.sigmoid p.2 ≠ Real.sigmoid q.1 :=
    hConnect hMappedLength
  intro hpq
  exact hMappedNe (congrArg Real.sigmoid hpq)

private theorem zeroLiteralAndJuilletExcursionPlan :
    ∃ gamma : FiniteMeasure (Real × Real),
      IsLiteralJuilletExcursionPlan 0 0 gamma ∧
        IsJuilletExcursionPlan 0 0 gamma := by
  have hAtomless : IsAtomlessFinite (0 : FiniteMeasure Real) := by
    intro x
    simp
  let data : JuilletCompletedGraphPairingData 0 0 := {
    source := fun _ _ => 0
    target := fun _ _ => 0
    active := fun _ => ∅
    source_measurable := fun _ => measurable_const
    target_measurable := fun _ => measurable_const
    active_measurable := fun _ => MeasurableSet.empty
    active_positive := by simp
    regular_positive_levels :=
      isJuilletRegularPositiveLevel_ae 0 0 hAtomless
    paired_ae := by simp
    entrances_exhaustive_unique_ae := by
      filter_upwards with h
      intro x hh hx
      have hGraph := hx.1
      change h ∈
        uIcc (signedCumulativeLeft 0 0 x)
          (signedCumulative 0 0 x) at hGraph
      have hZero : h = 0 := by
        simpa [signedCumulativeLeft, signedCumulative] using hGraph
      exact (ne_of_gt hh hZero).elim
    exits_exhaustive_unique_ae := by
      filter_upwards with h
      intro y hh hy
      have hGraph := hy.1
      change h ∈
        uIcc (signedCumulativeLeft 0 0 y)
          (signedCumulative 0 0 y) at hGraph
      have hZero : h = 0 := by
        simpa [signedCumulativeLeft, signedCumulative] using hGraph
      exact (ne_of_gt hh hZero).elim
    finite_active_ae := by simp
  }
  have hCoupling :
      IsFiniteCoupling
        (0 : FiniteMeasure Real) 0
        (0 : FiniteMeasure (Real × Real)) := by
    constructor
    · apply FiniteMeasure.toMeasure_injective
      change Measure.map Prod.fst (0 : Measure (Real × Real)) =
        (0 : Measure Real)
      exact Measure.map_zero Prod.fst
    · apply FiniteMeasure.toMeasure_injective
      change Measure.map Prod.snd (0 : Measure (Real × Real)) =
        (0 : Measure Real)
      exact Measure.map_zero Prod.snd
  refine ⟨0, ⟨hCoupling, data, ?_⟩, hCoupling, ∅,
    MeasurableSet.empty, by simp, ?_⟩
  · simp [literalJuilletExcursionMeasure, data]
  · simp [IsMonotoneArchSet]

/-- The literal completed-graph Juillet construction requires neither
positive common mass nor first moments. -/
theorem literalJuilletConstructionPremise_unconditional :
    LiteralJuilletConstructionPremise := by
  intro mu nu hMass hAtomless hSingular hOrder
  by_cases hMassZero : mu.mass = 0
  · have hMu : mu = 0 :=
      (FiniteMeasure.mass_zero_iff mu).mp hMassZero
    have hNuMassZero : nu.mass = 0 := hMass.symm.trans hMassZero
    have hNu : nu = 0 :=
      (FiniteMeasure.mass_zero_iff nu).mp hNuMassZero
    subst mu
    subst nu
    exact zeroLiteralAndJuilletExcursionPlan
  · have hPositive : 0 < mu.mass := pos_of_ne_zero hMassZero
    have hSigmoidEmbedding : MeasurableEmbedding Real.sigmoid := by
      simpa only [Function.comp_apply, unitInterval.sigmoid] using
        (unitInterval.measurableEmbedding_coe.comp
          measurableEmbedding_sigmoid)
    have hSigmoidMeasurable : Measurable Real.sigmoid :=
      hSigmoidEmbedding.measurable
    let muB : FiniteMeasure Real := mu.map Real.sigmoid
    let nuB : FiniteMeasure Real := nu.map Real.sigmoid
    have hMuBMass : muB.mass = mu.mass := by
      exact finiteMeasure_mass_map_of_measurable mu hSigmoidMeasurable
    have hNuBMass : nuB.mass = nu.mass := by
      exact finiteMeasure_mass_map_of_measurable nu hSigmoidMeasurable
    have hMassB : muB.mass = nuB.mass := by
      rw [hMuBMass, hNuBMass]
      exact hMass
    have hPositiveB : 0 < muB.mass := by
      rw [hMuBMass]
      exact hPositive
    have hFirstMoment (eta : FiniteMeasure Real) :
        Integrable (fun x : Real => |Real.sigmoid x|)
          (eta : Measure Real) := by
      refine (integrable_const 1).mono'
        (continuous_abs.comp continuous_sigmoid).aestronglyMeasurable ?_
      filter_upwards with x
      simpa only [Real.norm_eq_abs, abs_abs, abs_one] using
        (abs_le.mpr
          ⟨by linarith [Real.sigmoid_pos x],
            Real.sigmoid_le_one x⟩)
    have hFirstMuB :
        Integrable (fun x : Real => |x|) (muB : Measure Real) := by
      change
        Integrable (fun x : Real => |x|)
          (Measure.map Real.sigmoid (mu : Measure Real))
      apply hSigmoidEmbedding.integrable_map_iff.mpr
      simpa only [Function.comp_apply] using hFirstMoment mu
    have hFirstNuB :
        Integrable (fun x : Real => |x|) (nuB : Measure Real) := by
      change
        Integrable (fun x : Real => |x|)
          (Measure.map Real.sigmoid (nu : Measure Real))
      apply hSigmoidEmbedding.integrable_map_iff.mpr
      simpa only [Function.comp_apply] using hFirstMoment nu
    have hAtomlessB : IsAtomlessFinite muB :=
      isAtomlessFinite_map_of_measurableEmbedding
        hAtomless hSigmoidEmbedding
    have hSingularB : FiniteMutuallySingular muB nuB :=
      finiteMutuallySingular_map_of_measurableEmbedding
        hSingular hSigmoidEmbedding
    obtain ⟨gammaForward, hForward⟩ :=
      existsForwardCouplingOfStochasticOrder hMass hOrder
    let gammaForwardB : FiniteCoupling muB nuB :=
      mapFiniteCouplingLocal gammaForward Real.sigmoid Real.sigmoid
        hSigmoidMeasurable hSigmoidMeasurable
    have hForwardB : IsForwardPlan gammaForwardB := by
      change
        ∀ᵐ z ∂Measure.map
            (Prod.map Real.sigmoid Real.sigmoid)
            (gammaForward.plan : Measure (Real × Real)),
          z.1 <= z.2
      apply (ae_map_iff
        (hSigmoidMeasurable.prodMap hSigmoidMeasurable).aemeasurable
        (measurableSet_le measurable_fst measurable_snd)).2
      exact hForward.mono fun z hz =>
        Real.sigmoid_monotone hz
    have hOrderB : StochasticallyDominates nuB muB :=
      stochasticallyDominatesOfForwardLocal
        gammaForwardB hForwardB
    obtain ⟨gammaB, _hGammaBForward, hGammaBExcursion⟩ :=
      existsJuilletExcursionPlan
        muB nuB hMassB hPositiveB hFirstMuB hFirstNuB
          hSingularB hAtomlessB hOrderB
    obtain ⟨SB, hSBMeasurable, hSBFull, hSBStrict, hSBMonotone⟩ :=
      existsStrictMonotoneArchSupportOfJuilletExcursionPlan
        hSingularB hAtomlessB hOrderB hGammaBExcursion
    let inv : Real -> Real := hSigmoidEmbedding.invFun
    have hInvMeasurable : Measurable inv :=
      hSigmoidEmbedding.measurable_invFun
    have hPullMu : muB.map inv = mu := by
      apply FiniteMeasure.toMeasure_injective
      change
        Measure.map inv
            (Measure.map Real.sigmoid (mu : Measure Real)) =
          (mu : Measure Real)
      rw [Measure.map_map hInvMeasurable hSigmoidMeasurable,
        hSigmoidEmbedding.leftInverse_invFun.id, Measure.map_id]
    have hPullNu : nuB.map inv = nu := by
      apply FiniteMeasure.toMeasure_injective
      change
        Measure.map inv
            (Measure.map Real.sigmoid (nu : Measure Real)) =
          (nu : Measure Real)
      rw [Measure.map_map hInvMeasurable hSigmoidMeasurable,
        hSigmoidEmbedding.leftInverse_invFun.id, Measure.map_id]
    let gammaPull : FiniteCoupling (muB.map inv) (nuB.map inv) :=
      mapFiniteCouplingLocal gammaB inv inv hInvMeasurable hInvMeasurable
    let gamma : FiniteCoupling mu nu :=
      ⟨gammaPull.plan,
        gammaPull.property.1.trans hPullMu,
        gammaPull.property.2.trans hPullNu⟩
    let S : Set (Real × Real) :=
      Prod.map Real.sigmoid Real.sigmoid ⁻¹' SB
    have hSMeasurable : MeasurableSet S :=
      hSBMeasurable.preimage
        (hSigmoidMeasurable.prodMap hSigmoidMeasurable)
    have hRangeMuB :
        ∀ᵐ x ∂(muB : Measure Real), x ∈ range Real.sigmoid := by
      change
        ∀ᵐ x ∂Measure.map Real.sigmoid (mu : Measure Real),
          x ∈ range Real.sigmoid
      exact ae_map_mem_range Real.sigmoid
        hSigmoidEmbedding.measurableSet_range (mu : Measure Real)
    have hRangeNuB :
        ∀ᵐ x ∂(nuB : Measure Real), x ∈ range Real.sigmoid := by
      change
        ∀ᵐ x ∂Measure.map Real.sigmoid (nu : Measure Real),
          x ∈ range Real.sigmoid
      exact ae_map_mem_range Real.sigmoid
        hSigmoidEmbedding.measurableSet_range (nu : Measure Real)
    have hRangePlan :=
      finiteCouplingMarginalAeTransfer gammaB hRangeMuB hRangeNuB
    have hPullFull :
        ∀ᵐ z ∂(gammaPull.plan : Measure (Real × Real)), z ∈ S := by
      change
        ∀ᵐ z ∂Measure.map (Prod.map inv inv)
            (gammaB.plan : Measure (Real × Real)),
          z ∈ S
      apply (ae_map_iff
        (hInvMeasurable.prodMap hInvMeasurable).aemeasurable
        hSMeasurable).2
      filter_upwards [hSBFull, hRangePlan.1, hRangePlan.2] with
          z hz hzFirst hzSecond
      obtain ⟨x, hx⟩ := hzFirst
      obtain ⟨y, hy⟩ := hzSecond
      have hFirst :
          Real.sigmoid (inv z.1) = z.1 := by
        rw [← hx]
        exact congrArg Real.sigmoid
          (hSigmoidEmbedding.leftInverse_invFun x)
      have hSecond :
          Real.sigmoid (inv z.2) = z.2 := by
        rw [← hy]
        exact congrArg Real.sigmoid
          (hSigmoidEmbedding.leftInverse_invFun y)
      change
        (Real.sigmoid (inv z.1), Real.sigmoid (inv z.2)) ∈ SB
      rwa [hFirst, hSecond]
    have hSFull : IsSupported gamma S := by
      simpa only [gamma, FiniteCoupling.plan] using hPullFull
    have hSMonotone : IsMonotoneArchSet S := by
      intro p hp q hq
      change
        (Real.sigmoid p.1, Real.sigmoid p.2) ∈ SB at hp
      change
        (Real.sigmoid q.1, Real.sigmoid q.2) ∈ SB at hq
      have hMapped :=
        hSBMonotone
          (Real.sigmoid p.1, Real.sigmoid p.2) hp
          (Real.sigmoid q.1, Real.sigmoid q.2) hq
      have hpStrict : p.1 < p.2 :=
        Real.sigmoid_lt_iff.mp (hSBStrict hp)
      have hqStrict : q.1 < q.2 :=
        Real.sigmoid_lt_iff.mp (hSBStrict hq)
      refine ⟨archesDoNotCross_of_sigmoid p q hMapped.1,
        archesDoNotConnect_of_sigmoid p q hMapped.2.1, ?_⟩
      intro _hNested
      exact mul_nonneg
        (sub_nonneg.mpr hpStrict.le)
        (sub_nonneg.mpr hqStrict.le)
    have hGammaExcursion :
        IsJuilletExcursionPlan mu nu gamma.plan :=
      ⟨gamma.property, S, hSMeasurable, hSFull, hSMonotone⟩
    have hIndicatrix :
        PositiveCrossingIndicatrixIdentity mu nu :=
      positiveCrossingIndicatrixIdentity_of_atomless_mutuallySingular
        hAtomless hSingular
    have hGammaLiteral :
        IsLiteralJuilletExcursionPlan mu nu gamma.plan :=
      isLiteralJuilletExcursionPlan_of_juilletExcursionPlan
        mu nu gamma hGammaExcursion hSingular hAtomless hOrder
          (measurablePositiveCrossingDecomposition mu nu) hIndicatrix
    exact ⟨gamma.plan, hGammaLiteral, hGammaExcursion⟩

end

end ConcaveOTLimit
