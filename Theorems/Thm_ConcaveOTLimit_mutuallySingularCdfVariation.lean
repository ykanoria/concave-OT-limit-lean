import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrixMutuallySingular
import Mathlib.MeasureTheory.Measure.Stieltjes

open MeasureTheory Set

namespace ConcaveOTLimit

noncomputable section

private def cumulativeVariation
    (mu nu : FiniteMeasure Real) (x : Real) : Real :=
  variationOnFromTo (signedCumulative mu nu) univ 0 x

private def positiveVariationCumulative
    (mu nu : FiniteMeasure Real) : StieltjesFunction Real where
  toFun x :=
    (cumulativeVariation mu nu x + signedCumulative mu nu x) / 2
  mono' := by
    intro a b hab
    have hBV :=
      (signedCumulativeBoundedVariation mu nu).locallyBoundedVariationOn
    have hVariation :
        signedCumulative mu nu a - signedCumulative mu nu b ≤
          cumulativeVariation mu nu b -
            cumulativeVariation mu nu a := by
      calc
        signedCumulative mu nu a - signedCumulative mu nu b ≤
            |signedCumulative mu nu b - signedCumulative mu nu a| :=
          neg_le_abs _
        _ = dist (signedCumulative mu nu a)
              (signedCumulative mu nu b) := by
          rw [dist_comm, Real.dist_eq]
        _ ≤ variationOnFromTo (signedCumulative mu nu) univ a b := by
          rw [variationOnFromTo.eq_of_le _ _ hab, dist_edist]
          apply ENNReal.toReal_mono
            (hBV a b (mem_univ _) (mem_univ _))
          exact eVariationOn.edist_le _ ⟨mem_univ _, le_rfl, hab⟩
            ⟨mem_univ _, hab, le_rfl⟩
        _ = cumulativeVariation mu nu b -
              cumulativeVariation mu nu a := by
          rw [cumulativeVariation, cumulativeVariation,
            ← variationOnFromTo.add hBV (mem_univ (0 : Real))
              (mem_univ a) (mem_univ b)]
          ring
    dsimp only
    linarith
  right_continuous' x := by
    apply ContinuousWithinAt.div_const
    apply ContinuousWithinAt.add
    · exact
        (signedCumulativeBoundedVariation mu nu).continuousWithinAt_variationOnFromTo_Ici
          ((signedCumulativeRightContinuousAndLeftLim mu nu).1 x)
    · exact (signedCumulativeRightContinuousAndLeftLim mu nu).1 x

private def negativeVariationCumulative
    (mu nu : FiniteMeasure Real) : StieltjesFunction Real where
  toFun x :=
    (cumulativeVariation mu nu x - signedCumulative mu nu x) / 2
  mono' := by
    have hMono :
        MonotoneOn
          (variationOnFromTo (signedCumulative mu nu) univ 0 -
            signedCumulative mu nu) univ :=
      variationOnFromTo.sub_self_monotoneOn
        (signedCumulativeBoundedVariation mu nu).locallyBoundedVariationOn
        (mem_univ (0 : Real))
    intro a b hab
    exact div_le_div_of_nonneg_right
      (hMono (mem_univ a) (mem_univ b) hab) (by norm_num)
  right_continuous' x := by
    apply ContinuousWithinAt.div_const
    apply ContinuousWithinAt.sub
    · exact
        (signedCumulativeBoundedVariation mu nu).continuousWithinAt_variationOnFromTo_Ici
          ((signedCumulativeRightContinuousAndLeftLim mu nu).1 x)
    · exact (signedCumulativeRightContinuousAndLeftLim mu nu).1 x

private theorem variationCumulative_abs_le
    (mu nu : FiniteMeasure Real) (x : Real) :
    |cumulativeVariation mu nu x| ≤
      (eVariationOn (signedCumulative mu nu) univ).toReal := by
  exact variationOnFromTo.abs_le_eVariationOn
    (signedCumulativeBoundedVariation mu nu)

private theorem signedCumulative_abs_le
    (mu nu : FiniteMeasure Real) (x : Real) :
    |signedCumulative mu nu x| ≤
      (eVariationOn (signedCumulative mu nu) univ).toReal +
        |signedCumulative mu nu 0| := by
  have hDist :
      dist (signedCumulative mu nu x) (signedCumulative mu nu 0) ≤
        (eVariationOn (signedCumulative mu nu) univ).toReal := by
    rw [dist_edist]
    exact ENNReal.toReal_mono (signedCumulativeBoundedVariation mu nu)
      (eVariationOn.edist_le _ (mem_univ x) (mem_univ 0))
  calc
    |signedCumulative mu nu x| ≤
        |signedCumulative mu nu x - signedCumulative mu nu 0| +
          |signedCumulative mu nu 0| := by
      have := abs_add_le
        (signedCumulative mu nu x - signedCumulative mu nu 0)
        (signedCumulative mu nu 0)
      simpa only [sub_add_cancel] using this
    _ = dist (signedCumulative mu nu x)
          (signedCumulative mu nu 0) +
          |signedCumulative mu nu 0| := by
      rw [Real.dist_eq]
    _ ≤ _ := by
      gcongr

private theorem variationStieltjes_abs_le
    (mu nu : FiniteMeasure Real)
    (x : Real) :
    |positiveVariationCumulative mu nu x| ≤
        2 * (eVariationOn (signedCumulative mu nu) univ).toReal +
          |signedCumulative mu nu 0| ∧
      |negativeVariationCumulative mu nu x| ≤
        2 * (eVariationOn (signedCumulative mu nu) univ).toReal +
          |signedCumulative mu nu 0| := by
  have hV := variationCumulative_abs_le mu nu x
  have hF := signedCumulative_abs_le mu nu x
  have hC :
      0 ≤ (eVariationOn (signedCumulative mu nu) univ).toReal :=
    ENNReal.toReal_nonneg
  have hA : 0 ≤ |signedCumulative mu nu 0| := abs_nonneg _
  constructor
  · rw [positiveVariationCumulative, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |cumulativeVariation mu nu x + signedCumulative mu nu x| / 2 ≤
          (|cumulativeVariation mu nu x| +
            |signedCumulative mu nu x|) / 2 := by
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by linarith
  · rw [negativeVariationCumulative, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |cumulativeVariation mu nu x - signedCumulative mu nu x| / 2 ≤
          (|cumulativeVariation mu nu x| +
            |signedCumulative mu nu x|) / 2 := by
        gcongr
        exact abs_sub _ _
      _ ≤ _ := by linarith

private def positiveVariationMeasure
    (mu nu : FiniteMeasure Real) : Measure Real :=
  (positiveVariationCumulative mu nu).measure

private def negativeVariationMeasure
    (mu nu : FiniteMeasure Real) : Measure Real :=
  (negativeVariationCumulative mu nu).measure

private instance positiveVariationMeasure_finite
    (mu nu : FiniteMeasure Real) :
    IsFiniteMeasure (positiveVariationMeasure mu nu) := by
  exact StieltjesFunction.isFiniteMeasure_of_forall_abs_le _
    (fun x => (variationStieltjes_abs_le mu nu x).1)

private instance negativeVariationMeasure_finite
    (mu nu : FiniteMeasure Real) :
    IsFiniteMeasure (negativeVariationMeasure mu nu) := by
  exact StieltjesFunction.isFiniteMeasure_of_forall_abs_le _
    (fun x => (variationStieltjes_abs_le mu nu x).2)

private theorem signedCumulative_increment
    (mu nu : FiniteMeasure Real) {a b : Real} (hab : a ≤ b) :
    signedCumulative mu nu b - signedCumulative mu nu a =
      (mu : Measure Real).real (Ioc a b) -
        (nu : Measure Real).real (Ioc a b) := by
  calc
    signedCumulative mu nu b - signedCumulative mu nu a =
        (signedCumulativeBoundedVariation mu nu).vectorMeasure
          (Ioc a b) := by
      rw [(signedCumulativeBoundedVariation mu nu).vectorMeasure_Ioc hab,
        ((signedCumulativeRightContinuousAndLeftLim mu nu).1 b).rightLim_eq,
        ((signedCumulativeRightContinuousAndLeftLim mu nu).1 a).rightLim_eq]
    _ = juilletSignedMeasure mu nu (Ioc a b) := by
      rw [signedCumulativeVectorMeasure_eq_juilletSignedMeasure]
    _ = _ := by
      rw [juilletSignedMeasure,
        Measure.toSignedMeasure_sub_apply measurableSet_Ioc]

private theorem variationMeasure_balance
    (mu nu : FiniteMeasure Real) :
    positiveVariationMeasure mu nu + (nu : Measure Real) =
      negativeVariationMeasure mu nu + (mu : Measure Real) := by
  apply Measure.ext_of_Ioc
  intro a b hab
  apply measureReal_eq_measureReal_iff.mp
  rw [measureReal_add_apply, measureReal_add_apply,
    positiveVariationMeasure, negativeVariationMeasure,
    StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    Measure.real_def, Measure.real_def,
    ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · have hIncrement := signedCumulative_increment mu nu hab.le
    dsimp [positiveVariationCumulative, negativeVariationCumulative]
    linarith
  · exact sub_nonneg.mpr
      ((negativeVariationCumulative mu nu).mono hab.le)
  · exact sub_nonneg.mpr
      ((positiveVariationCumulative mu nu).mono hab.le)

private theorem mutuallySingular_le_of_balance
    {mu nu p q : Measure Real}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    [IsFiniteMeasure p] [IsFiniteMeasure q]
    (hSingular : mu ⟂ₘ nu)
    (hBalance : p + nu = q + mu) :
    mu ≤ p ∧ nu ≤ q := by
  rcases hSingular with ⟨A, hA, hMu, hNu⟩
  constructor
  · refine Measure.le_intro fun s hs _ => ?_
    calc
      mu s = mu (s ∩ Aᶜ) := by
        rw [← measure_diff_null (s := s) hMu, diff_eq]
      _ ≤ (q + mu) (s ∩ Aᶜ) := by
        simp only [Measure.add_apply]
        exact le_add_left le_rfl
      _ = (p + nu) (s ∩ Aᶜ) := by rw [hBalance]
      _ = p (s ∩ Aᶜ) := by
        rw [Measure.add_apply,
          measure_mono_null inter_subset_right hNu, add_zero]
      _ ≤ p s := measure_mono inter_subset_left
  · refine Measure.le_intro fun s hs _ => ?_
    calc
      nu s = nu (s ∩ A) := by
        rw [← measure_diff_null (s := s) hNu, diff_compl, inter_comm]
      _ ≤ (p + nu) (s ∩ A) := by
        simp only [Measure.add_apply]
        exact le_add_left le_rfl
      _ = (q + mu) (s ∩ A) := by rw [hBalance]
      _ = q (s ∩ A) := by
        rw [Measure.add_apply,
          measure_mono_null inter_subset_right hMu, add_zero]
      _ ≤ q s := measure_mono inter_subset_left

private theorem signedCumulative_eVariationOn_le_mass
    (mu nu : FiniteMeasure Real) {a b : Real} (hab : a ≤ b) :
    eVariationOn (signedCumulative mu nu) (Icc a b) ≤
      ((mu : Measure Real) + (nu : Measure Real)) (Ioc a b) := by
  apply iSup_le
  rintro ⟨n, u, hu, huMem⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (signedCumulative mu nu (u (i + 1)))
          (signedCumulative mu nu (u i))) ≤
        ∑ i ∈ Finset.range n,
          (((mu : Measure Real) + (nu : Measure Real))
            (Ioc (u i) (u (i + 1)))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [edist_dist, Real.dist_eq,
        signedCumulative_increment mu nu (hu (Nat.le_succ i)),
        ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      rw [Measure.add_apply, ENNReal.toReal_add
        (measure_ne_top (mu : Measure Real) _)
        (measure_ne_top (nu : Measure Real) _)]
      simp only [Measure.real_def]
      exact abs_sub_le _ _
    _ ≤ ((mu : Measure Real) + (nu : Measure Real)) (Ioc a b) := by
      have hSum :
          ∑ i ∈ Finset.range n,
              ((mu : Measure Real) + (nu : Measure Real))
                (Ioc (u i) (u (i + 1))) =
            ((mu : Measure Real) + (nu : Measure Real))
              (Ioc (u 0) (u n)) := by
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Finset.sum_range_succ, ih,
              ← measure_union (Ioc_disjoint_Ioc_of_le le_rfl)
                measurableSet_Ioc,
              Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n))
                (hu (Nat.le_succ n))]
      rw [hSum]
      exact measure_mono
        (Ioc_subset_Ioc (huMem 0).1 (huMem n).2)

/-- For mutually singular finite measures, the total interval mass is exactly
the variation of their signed cumulative path on the matching closed interval. -/
theorem mutuallySingular_cdf_mass_eq_eVariationOn_Icc
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    {a b : Real} (hab : a ≤ b) :
    ((mu : Measure Real) + (nu : Measure Real)) (Ioc a b) =
      eVariationOn (signedCumulative mu nu) (Icc a b) := by
  apply le_antisymm
  · have hMeasureSingular :
        (mu : Measure Real) ⟂ₘ (nu : Measure Real) := by
      rcases hSingular with ⟨A, hA, hMu, hNu⟩
      exact ⟨Aᶜ, hA.compl, hMu, by simpa only [compl_compl] using hNu⟩
    have hLe :=
      mutuallySingular_le_of_balance hMeasureSingular
        (variationMeasure_balance mu nu)
    calc
      ((mu : Measure Real) + (nu : Measure Real)) (Ioc a b) =
          (mu : Measure Real) (Ioc a b) +
            (nu : Measure Real) (Ioc a b) := by
        rw [Measure.add_apply]
      _ ≤ positiveVariationMeasure mu nu (Ioc a b) +
            negativeVariationMeasure mu nu (Ioc a b) :=
        add_le_add (hLe.1 (Ioc a b)) (hLe.2 (Ioc a b))
      _ = eVariationOn (signedCumulative mu nu) (Icc a b) := by
        rw [positiveVariationMeasure, negativeVariationMeasure,
          StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
          ← ENNReal.ofReal_add]
        · dsimp [positiveVariationCumulative,
            negativeVariationCumulative, cumulativeVariation]
          rw [show
              (variationOnFromTo (signedCumulative mu nu) univ 0 b +
                    signedCumulative mu nu b) /
                    2 -
                  (variationOnFromTo (signedCumulative mu nu) univ 0 a +
                    signedCumulative mu nu a) /
                    2 +
                ((variationOnFromTo (signedCumulative mu nu) univ 0 b -
                    signedCumulative mu nu b) /
                    2 -
                  (variationOnFromTo (signedCumulative mu nu) univ 0 a -
                    signedCumulative mu nu a) /
                    2) =
                variationOnFromTo (signedCumulative mu nu) univ 0 b -
                  variationOnFromTo (signedCumulative mu nu) univ 0 a by ring]
          rw [← variationOnFromTo.add
              (signedCumulativeBoundedVariation mu nu).locallyBoundedVariationOn
              (mem_univ (0 : Real)) (mem_univ a) (mem_univ b),
            variationOnFromTo.eq_of_le _ _ hab, univ_inter,
            add_sub_cancel_left, ENNReal.ofReal_toReal]
          exact (signedCumulativeBoundedVariation mu nu).mono Icc_subset_univ
        · exact sub_nonneg.mpr
            ((positiveVariationCumulative mu nu).mono hab)
        · exact sub_nonneg.mpr
            ((negativeVariationCumulative mu nu).mono hab)
  · exact signedCumulative_eVariationOn_le_mass mu nu hab

/-- The one-sided global estimate requested by the indicatrix-free audit. -/
theorem mutuallySingular_cdf_mass_le_eVariationOn
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu) :
    (mu : Measure Real) univ ≤
      eVariationOn (signedCumulative mu nu) univ := by
  let intervals : Nat → Set Real :=
    fun n => Ioc (-(n : Real)) (n : Real)
  have hMonotone : Monotone intervals := by
    intro m n hmn
    exact Ioc_subset_Ioc
      (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)
  have hUnion : (⋃ n, intervals n) = (univ : Set Real) := by
    ext x
    simp only [intervals, mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n : Nat, hn⟩ := exists_nat_gt |x|
    exact ⟨n, neg_lt_of_abs_lt hn,
      (lt_of_le_of_lt (le_abs_self x) hn).le⟩
  have hTendsto :
      Tendsto
        (fun n => ((mu : Measure Real) + (nu : Measure Real)) (intervals n))
        atTop
        (nhds (((mu : Measure Real) + (nu : Measure Real)) univ)) := by
    simpa only [Function.comp_apply, hUnion] using
      tendsto_measure_iUnion_atTop
        (μ := (mu : Measure Real) + (nu : Measure Real)) hMonotone
  have hIntervals (n : Nat) :
      ((mu : Measure Real) + (nu : Measure Real)) (intervals n) ≤
        eVariationOn (signedCumulative mu nu) univ := by
    rw [intervals,
      mutuallySingular_cdf_mass_eq_eVariationOn_Icc hSingular
        (neg_nonpos.mpr (Nat.cast_nonneg n))]
    exact eVariationOn.mono _ (subset_univ _)
  calc
    (mu : Measure Real) univ ≤
        ((mu : Measure Real) + (nu : Measure Real)) univ := by
      rw [Measure.add_apply]
      exact le_add_right le_rfl
    _ ≤ eVariationOn (signedCumulative mu nu) univ :=
      le_of_tendsto hTendsto (Eventually.of_forall hIntervals)

end

end ConcaveOTLimit
