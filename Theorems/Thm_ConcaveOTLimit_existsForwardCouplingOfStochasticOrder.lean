import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.CDF

open Filter Function MeasureTheory ProbabilityTheory Set Topology unitInterval
open scoped ENNReal NNReal Topology unitInterval

noncomputable section

namespace ConcaveOTLimit

private def unitQuantile (kappa : Measure I) (t : I) : I :=
  sSup {x | kappa.real (Icc 0 x) < t}

private theorem unitQuantile_measurable_map
    (kappa : Measure I) [IsProbabilityMeasure kappa] :
    Measurable (unitQuantile kappa) /\
      volume.map (unitQuantile kappa) = kappa := by
  let f : I -> I := fun t => sSup {x | kappa.real (Icc 0 x) < t}
  have hMeasurable : Measurable f := by
    refine measurable_of_Ioi fun a => ?_
    have hMonotone : Monotone (fun x : I => kappa.real (Icc 0 x)) :=
      fun x y hxy => measureReal_mono (by gcongr)
    have hPreimage :
        {t : I | a < f t} =
          iUnion fun q : Rat =>
            iUnion fun hqI : (q : Real) ∈ Icc 0 1 =>
              iUnion fun _hq : a < (q : Real) =>
                {t : I | kappa.real (Icc 0 ⟨q, hqI⟩) < t} := by
      ext t
      simp_all only [lt_sSup_iff, mem_setOf_eq, Subtype.exists, mem_Icc, Rat.cast_nonneg,
        mem_iUnion, exists_prop, exists_and_left, f]
      constructor
      · rintro ⟨y, hyI, hy, (hay : a.1 < y)⟩
        obtain ⟨q, haq, hqy⟩ := exists_rat_btwn hay
        refine ⟨q, haq, ⟨?_, hqy.le.trans hyI.2⟩,
          lt_of_lt_of_le' hy (hMonotone hqy.le)⟩
        simp [← Rat.cast_nonneg (K := Real), a.2.1.trans haq.le]
      · rintro ⟨q, haq, hqI, hqt⟩
        refine ⟨q, ⟨by simpa using hqI.1, hqI.2⟩, hqt, ?_⟩
        simpa using haq
    change MeasurableSet {t : I | a < f t}
    rw [hPreimage]
    refine MeasurableSet.iUnion fun q =>
      MeasurableSet.iUnion fun hqI =>
        MeasurableSet.iUnion fun _hq => ?_
    exact measurableSet_lt measurable_const measurable_subtype_coe
  refine ⟨by simpa [unitQuantile, f] using hMeasurable, ?_⟩
  change volume.map f = kappa
  refine (volume.map f).ext_of_Iic kappa fun x => ?_
  have hIic : Iic x = Icc 0 x := by
    ext y
    simp
  have hkappaI : kappa.real (Icc 0 x) ∈ Icc (0 : Real) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [volume.map_apply hMeasurable measurableSet_Iic, preimage, mem_Iic, hIic,
    ← ofReal_measureReal (measure_ne_top kappa _),
    ← unitInterval.volume_Iic ⟨_, hkappaI⟩]
  congr with xi
  constructor
  · intro hfx
    change xi <= kappa.real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, xi.2.2]
    let g : I -> Real := fun y => kappa.real (Icc 0 y)
    letI : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      exact ⟨1, lt_of_le_of_ne x.2.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g)
      continuousWithinAt_const ?_ ?_
    · let h := cdf (kappa.map Subtype.val)
      have hContinuous :=
        continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real kappa]
      exact hContinuous.comp
        (Continuous.continuousWithinAt (by fun_prop))
        (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra hle
      simp only [not_le] at hle
      simp only [sSup_le_iff, f] at hfx
      exact (not_lt_of_ge (hfx y hle)) hy
  · intro (hxi : xi <= kappa.real (Icc 0 x))
    simp only [sSup_le_iff, f]
    intro c hc
    by_contra! hcx
    have hnot :
        ¬(kappa.real (Icc 0 x) <= kappa.real (Icc 0 c)) :=
      not_le.mpr (lt_of_le_of_lt' hxi hc)
    refine hnot ?_
    gcongr
    simp

private theorem unitQuantile_mono
    {kappa lambda : Measure I}
    (hCDF : forall x, lambda.real (Icc 0 x) <= kappa.real (Icc 0 x)) :
    forall t, unitQuantile kappa t <= unitQuantile lambda t := by
  intro t
  apply sSup_le_sSup
  intro x hx
  exact (hCDF x).trans_lt hx

private theorem existsOrderedProbabilityMaps
    (mu nu : ProbabilityMeasure Real)
    (hOrder : forall x, (nu : Measure Real) (Iic x) <=
      (mu : Measure Real) (Iic x)) :
    exists (f g : I -> Real),
      Measurable f /\ Measurable g /\
      volume.map f = (mu : Measure Real) /\
      volume.map g = (nu : Measure Real) /\
      ∀ᵐ t ∂volume, f t <= g t := by
  let sigmoidEmbedding : MeasurableEmbedding unitInterval.sigmoid :=
    measurableEmbedding_sigmoid
  let muI : Measure I := (mu : Measure Real).map unitInterval.sigmoid
  let nuI : Measure I := (nu : Measure Real).map unitInterval.sigmoid
  letI : IsProbabilityMeasure muI :=
    Measure.isProbabilityMeasure_map sigmoidEmbedding.measurable.aemeasurable
  letI : IsProbabilityMeasure nuI :=
    Measure.isProbabilityMeasure_map sigmoidEmbedding.measurable.aemeasurable
  have hCDFI : forall x, nuI.real (Icc 0 x) <= muI.real (Icc 0 x) := by
    intro x
    apply ENNReal.toReal_mono (measure_ne_top muI (Icc 0 x))
    change
      ((nu : Measure Real).map unitInterval.sigmoid) (Icc 0 x) <=
        ((mu : Measure Real).map unitInterval.sigmoid) (Icc 0 x)
    rw [Measure.map_apply sigmoidEmbedding.measurable measurableSet_Icc,
      Measure.map_apply sigmoidEmbedding.measurable measurableSet_Icc]
    rcases eq_or_ne x 0 with rfl | hx0
    · have hPreimage :
          unitInterval.sigmoid ⁻¹' Icc 0 (0 : I) = (∅ : Set Real) := by
        ext y
        simp only [mem_preimage, mem_Icc, mem_empty_iff_false]
        constructor
        · rintro ⟨_, hy⟩
          exact (not_lt_of_ge hy (unitInterval.sigmoid_pos y)).elim
        · exact False.elim
      rw [hPreimage]
      simp
    rcases eq_or_ne x 1 with rfl | hx1
    · have hPreimage :
          unitInterval.sigmoid ⁻¹' Icc 0 (1 : I) = (univ : Set Real) := by
        ext y
        simp only [mem_preimage, mem_Icc, mem_univ, iff_true]
        exact ⟨(unitInterval.sigmoid_pos y).le,
          (unitInterval.sigmoid_lt_one y).le⟩
      rw [hPreimage]
      simp
    have hxInterior : x ∈ Ioo (0 : I) 1 :=
      ⟨lt_of_le_of_ne x.2.1 (Ne.symm hx0),
        lt_of_le_of_ne x.2.2 hx1⟩
    rw [← unitInterval.range_sigmoid] at hxInterior
    obtain ⟨r, rfl⟩ := hxInterior
    have hPreimage :
        unitInterval.sigmoid ⁻¹' Icc 0 (unitInterval.sigmoid r) = Iic r := by
      ext y
      simp [unitInterval.sigmoid_le_iff]
    simpa [hPreimage] using hOrder r
  have hMuQuantile := unitQuantile_measurable_map muI
  have hNuQuantile := unitQuantile_measurable_map nuI
  let qMu := unitQuantile muI
  let qNu := unitQuantile nuI
  have hqMuMeasurable : Measurable qMu := by
    simpa [qMu] using hMuQuantile.1
  have hqNuMeasurable : Measurable qNu := by
    simpa [qNu] using hNuQuantile.1
  have hqMuMap : volume.map qMu = muI := by
    simpa [qMu] using hMuQuantile.2
  have hqNuMap : volume.map qNu = nuI := by
    simpa [qNu] using hNuQuantile.2
  have hqOrder : forall t, qMu t <= qNu t := by
    simpa [qMu, qNu] using unitQuantile_mono hCDFI
  let f : I -> Real := sigmoidEmbedding.invFun ∘ qMu
  let g : I -> Real := sigmoidEmbedding.invFun ∘ qNu
  have hfMeasurable : Measurable f :=
    sigmoidEmbedding.measurable_invFun.comp hqMuMeasurable
  have hgMeasurable : Measurable g :=
    sigmoidEmbedding.measurable_invFun.comp hqNuMeasurable
  have hfMap : volume.map f = (mu : Measure Real) := by
    calc
      volume.map f =
          (volume.map qMu).map sigmoidEmbedding.invFun := by
        rw [Measure.map_map sigmoidEmbedding.measurable_invFun hqMuMeasurable]
      _ = muI.map sigmoidEmbedding.invFun := by rw [hqMuMap]
      _ = ((mu : Measure Real).map unitInterval.sigmoid).map
          sigmoidEmbedding.invFun := by rfl
      _ = (mu : Measure Real).map
          (sigmoidEmbedding.invFun ∘ unitInterval.sigmoid) :=
        Measure.map_map sigmoidEmbedding.measurable_invFun
          sigmoidEmbedding.measurable
      _ = (mu : Measure Real).map id := by
        rw [sigmoidEmbedding.leftInverse_invFun.id]
      _ = (mu : Measure Real) := Measure.map_id
  have hgMap : volume.map g = (nu : Measure Real) := by
    calc
      volume.map g =
          (volume.map qNu).map sigmoidEmbedding.invFun := by
        rw [Measure.map_map sigmoidEmbedding.measurable_invFun hqNuMeasurable]
      _ = nuI.map sigmoidEmbedding.invFun := by rw [hqNuMap]
      _ = ((nu : Measure Real).map unitInterval.sigmoid).map
          sigmoidEmbedding.invFun := by rfl
      _ = (nu : Measure Real).map
          (sigmoidEmbedding.invFun ∘ unitInterval.sigmoid) :=
        Measure.map_map sigmoidEmbedding.measurable_invFun
          sigmoidEmbedding.measurable
      _ = (nu : Measure Real).map id := by
        rw [sigmoidEmbedding.leftInverse_invFun.id]
      _ = (nu : Measure Real) := Measure.map_id
  have hqMuRange :
      ∀ᵐ t ∂volume, qMu t ∈ range unitInterval.sigmoid := by
    apply (ae_map_iff (μ := volume) hqMuMeasurable.aemeasurable
      sigmoidEmbedding.measurableSet_range).mp
    rw [hqMuMap]
    exact ae_map_mem_range unitInterval.sigmoid
      sigmoidEmbedding.measurableSet_range (mu : Measure Real)
  have hqNuRange :
      ∀ᵐ t ∂volume, qNu t ∈ range unitInterval.sigmoid := by
    apply (ae_map_iff (μ := volume) hqNuMeasurable.aemeasurable
      sigmoidEmbedding.measurableSet_range).mp
    rw [hqNuMap]
    exact ae_map_mem_range unitInterval.sigmoid
      sigmoidEmbedding.measurableSet_range (nu : Measure Real)
  refine ⟨f, g, hfMeasurable, hgMeasurable, hfMap, hgMap, ?_⟩
  filter_upwards [hqMuRange, hqNuRange] with t htMu htNu
  obtain ⟨x, hx⟩ := htMu
  obtain ⟨y, hy⟩ := htNu
  have hxy : x <= y := unitInterval.sigmoid_le_iff.mp <| by
    simpa [hx, hy] using hqOrder t
  change sigmoidEmbedding.invFun (qMu t) <=
    sigmoidEmbedding.invFun (qNu t)
  rw [← hx, ← hy, sigmoidEmbedding.leftInverse_invFun,
    sigmoidEmbedding.leftInverse_invFun]
  exact hxy

/-- Equal finite mass and first-order stochastic dominance produce a
coupling supported on the forward half-plane. This includes the zero-mass
case. -/
theorem existsForwardCouplingOfStochasticOrder
    {mu nu : FiniteMeasure Real}
    (hMass : mu.mass = nu.mass)
    (hOrder : StochasticallyDominates nu mu) :
    exists gamma : FiniteCoupling mu nu, IsForwardPlan gamma := by
  by_cases hMuZero : mu.mass = 0
  · have hMu : mu = 0 := (FiniteMeasure.mass_zero_iff mu).mp hMuZero
    have hNuZero : nu.mass = 0 := hMass.symm.trans hMuZero
    have hNu : nu = 0 := (FiniteMeasure.mass_zero_iff nu).mp hNuZero
    subst mu
    subst nu
    let gamma : FiniteCoupling (0 : FiniteMeasure Real) 0 :=
      ⟨0, by
        constructor
        · apply FiniteMeasure.toMeasure_injective
          change Measure.map Prod.fst (0 : Measure (Real × Real)) =
            (0 : Measure Real)
          exact Measure.map_zero Prod.fst
        · apply FiniteMeasure.toMeasure_injective
          change Measure.map Prod.snd (0 : Measure (Real × Real)) =
            (0 : Measure Real)
          exact Measure.map_zero Prod.snd⟩
    refine ⟨gamma, ?_⟩
    simp [gamma, IsForwardPlan, FiniteCoupling.plan]
  have hMu : mu ≠ 0 := mu.mass_nonzero_iff.mp hMuZero
  have hNuMass : nu.mass ≠ 0 := by
    rw [← hMass]
    exact hMuZero
  have hNu : nu ≠ 0 := nu.mass_nonzero_iff.mp hNuMass
  have hNormalizedOrder :
      forall x, (nu.normalize : Measure Real) (Iic x) <=
        (mu.normalize : Measure Real) (Iic x) := by
    intro x
    rw [nu.toMeasure_normalize_eq_of_nonzero hNu,
      mu.toMeasure_normalize_eq_of_nonzero hMu]
    simp only [Measure.smul_apply]
    rw [hMass]
    exact mul_le_mul_right (hOrder x) _
  obtain ⟨f, g, hf, hg, hfMap, hgMap, hfg⟩ :=
    existsOrderedProbabilityMaps mu.normalize nu.normalize hNormalizedOrder
  let pairMap : I -> Real × Real := fun t => (f t, g t)
  have hPairMap : Measurable pairMap := hf.prodMk hg
  let rho : FiniteMeasure (Real × Real) :=
    ⟨volume.map pairMap, by infer_instance⟩
  have hRhoFirst : firstMarginal rho = mu.normalize.toFiniteMeasure := by
    apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.fst (volume.map pairMap) =
        (mu.normalize : Measure Real)
    calc
      Measure.map Prod.fst (volume.map pairMap) =
          volume.map (Prod.fst ∘ pairMap) :=
        Measure.map_map measurable_fst hPairMap
      _ = volume.map f := by rfl
      _ = (mu.normalize : Measure Real) := hfMap
  have hRhoSecond : secondMarginal rho = nu.normalize.toFiniteMeasure := by
    apply FiniteMeasure.toMeasure_injective
    change
      Measure.map Prod.snd (volume.map pairMap) =
        (nu.normalize : Measure Real)
    calc
      Measure.map Prod.snd (volume.map pairMap) =
          volume.map (Prod.snd ∘ pairMap) :=
        Measure.map_map measurable_snd hPairMap
      _ = volume.map g := by rfl
      _ = (nu.normalize : Measure Real) := hgMap
  let rawPlan : FiniteMeasure (Real × Real) := mu.mass • rho
  have hRawCoupling : IsFiniteCoupling mu nu rawPlan := by
    constructor
    · calc
        firstMarginal rawPlan = mu.mass • firstMarginal rho := by
          simp [rawPlan, firstMarginal]
        _ = mu.mass • mu.normalize.toFiniteMeasure := by rw [hRhoFirst]
        _ = mu := mu.self_eq_mass_smul_normalize.symm
    · calc
        secondMarginal rawPlan = mu.mass • secondMarginal rho := by
          simp [rawPlan, secondMarginal]
        _ = mu.mass • nu.normalize.toFiniteMeasure := by rw [hRhoSecond]
        _ = nu.mass • nu.normalize.toFiniteMeasure := by rw [hMass]
        _ = nu := nu.self_eq_mass_smul_normalize.symm
  have hRhoForward :
      ∀ᵐ z ∂(rho : Measure (Real × Real)), z.1 <= z.2 := by
    change ∀ᵐ z ∂(volume.map pairMap), z.1 <= z.2
    rw [ae_map_iff hPairMap.aemeasurable
      (measurableSet_le measurable_fst measurable_snd)]
    simpa [pairMap] using hfg
  let gamma : FiniteCoupling mu nu := ⟨rawPlan, hRawCoupling⟩
  refine ⟨gamma, ?_⟩
  change ∀ᵐ z ∂(rawPlan : Measure (Real × Real)), z.1 <= z.2
  simpa [rawPlan, FiniteMeasure.toMeasure_smul] using
    Measure.ae_smul_measure hRhoForward mu.mass

end ConcaveOTLimit
