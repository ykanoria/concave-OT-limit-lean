import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrix
import Theorems.Thm_ConcaveOTLimit_signedCumulativeBoundedVariation
import Theorems.Thm_ConcaveOTLimit_signedCumulativeRightContinuousAndLeftLim
import Theorems.Thm_ConcaveOTLimit_literalJuilletLevelAlternation
import Definitions.Def_JuilletMassClock
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

noncomputable section

private theorem signedMeasure_ext_Iic
    {sigma tau : SignedMeasure Real}
    (hIic : forall x : Real, sigma (Iic x) = tau (Iic x)) :
    sigma = tau := by
  let spanning : Nat -> Set Real := fun n => Iic (n : Real)
  have hSpanningMonotone : Monotone spanning := by
    intro m n hmn
    exact Iic_subset_Iic.mpr (Nat.cast_le.mpr hmn)
  have hSpanningUnion : (⋃ n, spanning n) = (univ : Set Real) := by
    ext x
    simp only [spanning, mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge x
  have hSigmaUniv : Tendsto (fun n => sigma (spanning n)) atTop (nhds (sigma univ)) := by
    simpa only [hSpanningUnion] using
      sigma.tendsto_vectorMeasure_iUnion_atTop_nat hSpanningMonotone
        (fun _ => measurableSet_Iic)
  have hTauUniv : Tendsto (fun n => tau (spanning n)) atTop (nhds (tau univ)) := by
    simpa only [hSpanningUnion] using
      tau.tendsto_vectorMeasure_iUnion_atTop_nat hSpanningMonotone
        (fun _ => measurableSet_Iic)
  have hUniv : sigma univ = tau univ := by
    apply tendsto_nhds_unique
      (show Tendsto (fun n => tau (spanning n)) atTop (nhds (sigma univ)) by
        simpa only [spanning, hIic] using hSigmaUniv)
    exact hTauUniv
  apply VectorMeasure.ext
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => sigma t = tau t)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic Real))
    isPiSystem_Iic ?_ ?_ ?_ ?_ s hs
  · simp
  · intro t ht
    obtain ⟨x, rfl⟩ := ht
    exact hIic x
  · intro t ht hEq
    rw [VectorMeasure.of_compl ht, VectorMeasure.of_compl ht, hUniv, hEq]
  · intro f hDisjoint hMeasurable hEq
    rw [sigma.of_disjoint_iUnion hMeasurable hDisjoint,
      tau.of_disjoint_iUnion hMeasurable hDisjoint]
    exact tsum_congr hEq

private theorem tendsto_signedCumulative_atBot'
    (mu nu : FiniteMeasure Real) :
    Tendsto (signedCumulative mu nu) atBot (nhds 0) := by
  have hMeasure (eta : FiniteMeasure Real) :
      Tendsto (fun x : Real => (eta : Measure Real) (Iic x))
        atBot (nhds 0) := by
    have h :=
      tendsto_measure_iInter_atBot
        (μ := (eta : Measure Real))
        (s := fun x : Real => Iic x)
        (fun _ => measurableSet_Iic.nullMeasurableSet)
        (fun _ _ hxy => Iic_subset_Iic.mpr hxy)
        ⟨0, measure_ne_top (eta : Measure Real) (Iic 0)⟩
    have hInter : (⋂ x : Real, Iic x) = (∅ : Set Real) := by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
      push Not
      exact ⟨x - 1, by linarith⟩
    simpa only [Function.comp_apply, hInter, measure_empty] using h
  have hReal (eta : FiniteMeasure Real) :
      Tendsto
        (fun x : Real => ((eta : Measure Real) (Iic x)).toReal)
        atBot (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hMeasure eta)
  simpa only [signedCumulative, sub_zero] using
    (hReal mu).sub (hReal nu)

private theorem signedCumulative_value_mem_graph'
    (mu nu : FiniteMeasure Real) (x : Real) :
    (x, signedCumulative mu nu x) ∈
      generalizedCumulativeGraph mu nu := by
  change
    signedCumulative mu nu x ∈
      uIcc (signedCumulativeLeft mu nu x)
        (signedCumulative mu nu x)
  exact right_mem_uIcc

private theorem exists_right_point_below
    (mu nu : FiniteMeasure Real) {a b h : Real}
    (hab : a < b)
    (ha : signedCumulative mu nu a < h) :
    ∃ x ∈ Ioo a b, signedCumulative mu nu x < h := by
  have hTendsto :
      Tendsto (signedCumulative mu nu)
        (nhdsWithin a (Ioi a))
        (nhds (signedCumulative mu nu a)) :=
    ((signedCumulativeRightContinuousAndLeftLim mu nu).1 a).tendsto.mono_left
      (nhdsWithin_mono a Ioi_subset_Ici_self)
  have hBelow :
      ∀ᶠ x in nhdsWithin a (Ioi a),
        signedCumulative mu nu x < h :=
    hTendsto.eventually_lt_const ha
  have hBeforeAt :
      ∀ᶠ x in nhds a, x < b :=
    Iio_mem_nhds hab
  have hBefore :
      ∀ᶠ x in nhdsWithin a (Ioi a), x < b :=
    hBeforeAt.filter_mono inf_le_left
  have hExists :
      ∀ᶠ x in nhdsWithin a (Ioi a),
        x ∈ Ioi a ∧ x < b ∧ signedCumulative mu nu x < h := by
    filter_upwards [hBelow, hBefore, self_mem_nhdsWithin] with
        x hxBelow hxb hax
    exact ⟨hax, hxb, hxBelow⟩
  rcases hExists.exists with ⟨x, hax, hxb, hxBelow⟩
  exact ⟨x, ⟨hax, hxb⟩, hxBelow⟩

private theorem exists_graph_hit_Ioc
    (mu nu : FiniteMeasure Real) {a b h : Real}
    (hab : a < b)
    (ha : signedCumulative mu nu a < h)
    (hb : h < signedCumulative mu nu b) :
    ∃ x ∈ Ioc a b,
      (x, h) ∈ generalizedCumulativeGraph mu nu := by
  by_contra hNone
  push Not at hNone
  obtain ⟨z, hz, hzBelow⟩ :=
    exists_right_point_below mu nu hab ha
  have hAvoid :
      ∀ x ∈ Ioc a b,
        (x, h) ∉ generalizedCumulativeGraph mu nu := by
    intro x hx hGraph
    exact hNone x hx hGraph
  have hSide :=
    signedCumulative_side_constant_on_preconnected
      mu nu h isPreconnected_Ioc hAvoid
      (show z ∈ Ioc a b from ⟨hz.1, hz.2.le⟩)
      (show b ∈ Ioc a b from ⟨hab, le_rfl⟩)
  exact (not_lt_of_ge hb.le) (hSide.mp hzBelow)

private theorem exists_positive_crossing_Ioc
    (mu nu : FiniteMeasure Real) {a b h : Real}
    (hab : a < b)
    (ha : signedCumulative mu nu a < h)
    (hb : h < signedCumulative mu nu b)
    (hFinite :
      {x : Real |
        (x, h) ∈ generalizedCumulativeGraph mu nu}.Finite)
    (hClassified :
      ∀ x : Real,
        (x, h) ∈ generalizedCumulativeGraph mu nu →
          IsGoodIncreasingCrossing mu nu x h ∨
            IsGoodDecreasingCrossing mu nu x h) :
    ∃ x ∈ Ioc a b,
      IsGoodIncreasingCrossing mu nu x h := by
  let hits : Set Real :=
    {x | x ∈ Ioc a b ∧
      (x, h) ∈ generalizedCumulativeGraph mu nu}
  have hHitsFinite : hits.Finite :=
    hFinite.subset fun x hx => hx.2
  have hHitsNonempty : hits.Nonempty := by
    obtain ⟨x, hx, hGraph⟩ :=
      exists_graph_hit_Ioc mu nu hab ha hb
    exact ⟨x, hx, hGraph⟩
  have hHitsFinsetNonempty :
      hHitsFinite.toFinset.Nonempty :=
    hHitsFinite.toFinset_nonempty.mpr hHitsNonempty
  let x := hHitsFinite.toFinset.min' hHitsFinsetNonempty
  have hxHits : x ∈ hits :=
    hHitsFinite.mem_toFinset.mp
      (Finset.min'_mem _ hHitsFinsetNonempty)
  have hxLeast : ∀ y ∈ hits, x ≤ y := by
    intro y hy
    exact Finset.min'_le _ y
      (hHitsFinite.mem_toFinset.mpr hy)
  rcases hClassified x hxHits.2 with hIncreasing | hDecreasing
  · exact ⟨x, hxHits.1, hIncreasing⟩
  · obtain ⟨_hxGraph, epsilon, hEpsilon, hLocal⟩ := hDecreasing
    have hLower : max a (x - epsilon) < x :=
      max_lt hxHits.1.1 (sub_lt_self x hEpsilon)
    obtain ⟨y, hyLower, hyx⟩ := exists_between hLower
    have hay : a < y :=
      (le_max_left a (x - epsilon)).trans_lt hyLower
    have hxyEpsilon : x - epsilon < y :=
      (le_max_right a (x - epsilon)).trans_lt hyLower
    have hyNear : y ∈ Ioo (x - epsilon) (x + epsilon) :=
      ⟨hxyEpsilon, hyx.trans (lt_add_of_pos_right x hEpsilon)⟩
    have hProduct :=
      hLocal hyNear hyx.ne
        (signedCumulative_value_mem_graph' mu nu y)
    have hyAbove : h < signedCumulative mu nu y := by
      rcases mul_neg_iff.mp hProduct with hSigns | hSigns
      · exact sub_pos.mp hSigns.1
      · exact
          ((not_lt_of_ge (sub_nonpos.mpr hyx.le)) hSigns.2).elim
    obtain ⟨z, hz, hzBelow⟩ :=
      exists_right_point_below mu nu hxHits.1.1 ha
    have hAvoid :
        ∀ q ∈ Ioo a x,
          (q, h) ∉ generalizedCumulativeGraph mu nu := by
      intro q hq hqGraph
      have hqHits : q ∈ hits :=
        ⟨⟨hq.1, hq.2.le.trans hxHits.1.2⟩, hqGraph⟩
      exact (not_lt_of_ge (hxLeast q hqHits)) hq.2
    have hSide :=
      signedCumulative_side_constant_on_preconnected
        mu nu h isPreconnected_Ioo hAvoid hz
        (show y ∈ Ioo a x from ⟨hay, hyx⟩)
    exact ((not_lt_of_ge hyAbove.le) (hSide.mp hzBelow)).elim

/-- Every positive cumulative increment across an interval is paid for by
the literal increasing-crossing occupation of that interval. This is the
one-sided local Banach-indicatrix estimate available from finite regular
levels without a general fiber-counting area theorem. -/
theorem positiveIncrement_le_positiveCrossingOccupation_Ioc
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu)
    {a b : Real} (hab : a < b) :
    ENNReal.ofReal
        (signedCumulative mu nu b - signedCumulative mu nu a) ≤
      ∫⁻ h,
        ((positiveCrossingFiber mu nu (Ioc a b) h).encard : ENNReal)
          ∂(volume : Measure Real) := by
  have hRegular :=
    generalizedCumulativeGraphFiniteAndRegularAe
      mu nu hAtomless
  have hPointwise :
      ∀ᵐ h ∂(volume : Measure Real),
        (Ioo (signedCumulative mu nu a)
            (signedCumulative mu nu b)).indicator
            (fun _ => (1 : ENNReal)) h ≤
          ((positiveCrossingFiber mu nu (Ioc a b) h).encard :
            ENNReal) := by
    filter_upwards [hRegular] with h hRegularLevel
    by_cases hh :
        h ∈ Ioo (signedCumulative mu nu a)
          (signedCumulative mu nu b)
    · rw [indicator_of_mem hh]
      obtain ⟨x, hx, hIncreasing⟩ :=
        exists_positive_crossing_Ioc mu nu hab
          hh.1 hh.2 hRegularLevel.1 hRegularLevel.2
      have hNonempty :
          (positiveCrossingFiber mu nu (Ioc a b) h).Nonempty :=
        ⟨x, hx, hIncreasing⟩
      exact_mod_cast
        (Set.one_le_encard_iff_nonempty.mpr hNonempty)
    · rw [Set.indicator_of_notMem hh]
      exact bot_le
  calc
    ENNReal.ofReal
          (signedCumulative mu nu b -
            signedCumulative mu nu a) =
        (volume : Measure Real)
          (Ioo (signedCumulative mu nu a)
            (signedCumulative mu nu b)) := by
      rw [Real.volume_Ioo]
    _ = ∫⁻ h,
        (Ioo (signedCumulative mu nu a)
            (signedCumulative mu nu b)).indicator
            (fun _ => (1 : ENNReal)) h
        ∂(volume : Measure Real) :=
      (lintegral_indicator_one measurableSet_Ioo).symm
    _ ≤ ∫⁻ h,
        ((positiveCrossingFiber mu nu (Ioc a b) h).encard :
          ENNReal)
        ∂(volume : Measure Real) :=
      lintegral_mono_ae hPointwise

/-- The Stieltjes vector measure canonically associated by Mathlib to the
bounded-variation signed cumulative function is exactly `mu - nu`. -/
theorem signedCumulativeVectorMeasure_eq_juilletSignedMeasure
    (mu nu : FiniteMeasure Real) :
    (signedCumulativeBoundedVariation mu nu).vectorMeasure =
      juilletSignedMeasure mu nu := by
  apply signedMeasure_ext_Iic
  intro x
  rw [(signedCumulativeBoundedVariation mu nu).vectorMeasure_Iic]
  have hRight :
      Function.rightLim (signedCumulative mu nu) x =
        signedCumulative mu nu x :=
    ((signedCumulativeRightContinuousAndLeftLim mu nu).1 x).rightLim_eq
  have hBot :
      Filter.limUnder atBot (signedCumulative mu nu) = 0 :=
    (tendsto_signedCumulative_atBot' mu nu).limUnder_eq
  rw [hRight, hBot, sub_zero, juilletSignedMeasure,
    Measure.toSignedMeasure_sub_apply measurableSet_Iic]
  rfl

/-- Consequently, the positive Jordan part of Mathlib's BV vector measure is
the positive-variation measure used by the crossing indicatrix statement. -/
theorem signedCumulativeVectorMeasure_positivePart
    (mu nu : FiniteMeasure Real) :
    (SignedMeasure.toJordanDecomposition
        (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart =
      juilletPositiveVariationMeasure mu nu := by
  rw [signedCumulativeVectorMeasure_eq_juilletSignedMeasure]
  rfl

/-- The requested crossing identity is exactly the positive-part coarea
formula for Mathlib's Stieltjes vector measure of the cumulative path. -/
theorem
    positiveCrossingIndicatrixIdentity_iff_signedCumulativeVectorMeasurePositivePart
    (mu nu : FiniteMeasure Real) :
    PositiveCrossingIndicatrixIdentity mu nu ↔
      ∀ s : Set Real, MeasurableSet s →
        (∫⁻ h,
            ((positiveCrossingFiber mu nu s h).encard : ENNReal)
          ∂(volume : Measure Real)) =
          (SignedMeasure.toJordanDecomposition
              (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart s := by
  simp only [PositiveCrossingIndicatrixIdentity,
    signedCumulativeVectorMeasure_positivePart]

/-- For mutually singular inputs, the positive Jordan part of the cumulative
BV vector measure is the source measure. -/
theorem signedCumulativeVectorMeasure_positivePart_eq_source
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu) :
    (SignedMeasure.toJordanDecomposition
        (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart =
      (mu : Measure Real) := by
  rw [signedCumulativeVectorMeasure_positivePart,
    juilletPositiveVariationMeasureEqSource hSingular]

/-- For mutually singular inputs, the negative Jordan part of the cumulative
BV vector measure is the target measure. -/
theorem signedCumulativeVectorMeasure_negativePart_eq_target
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu) :
    (SignedMeasure.toJordanDecomposition
        (signedCumulativeBoundedVariation mu nu).vectorMeasure).negPart =
      (nu : Measure Real) := by
  rw [signedCumulativeVectorMeasure_eq_juilletSignedMeasure]
  have hMutuallySingular :
      (mu : Measure Real) ⟂ₘ (nu : Measure Real) := by
    rcases hSingular with ⟨A, hA, hMu, hNu⟩
    exact ⟨Aᶜ, hA.compl, hMu, by simpa only [compl_compl] using hNu⟩
  let jordan : JordanDecomposition Real :=
    { posPart := (mu : Measure Real)
      negPart := (nu : Measure Real)
      mutuallySingular := hMutuallySingular }
  have hSigned :
      juilletSignedMeasure mu nu = jordan.toSignedMeasure := by
    rfl
  rw [SignedMeasure.toJordanDecomposition_eq hSigned]

/-- Thus the total variation measure of the cumulative path is the total
input mass measure. -/
theorem signedCumulativeVectorMeasure_totalVariation_eq_sum
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu) :
    SignedMeasure.totalVariation
        (signedCumulativeBoundedVariation mu nu).vectorMeasure =
      (mu : Measure Real) + (nu : Measure Real) := by
  rw [SignedMeasure.totalVariation,
    signedCumulativeVectorMeasure_positivePart_eq_source hSingular,
    signedCumulativeVectorMeasure_negativePart_eq_target hSingular]

/-- Under mutual singularity, the repository's mass clock is exactly the
cumulative total-variation clock of Mathlib's BV vector measure. -/
theorem cumulativeMassClock_eq_vectorMeasureTotalVariation_Iic_real
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu) (x : Real) :
    cumulativeMassClock mu nu x =
      (SignedMeasure.totalVariation
          (signedCumulativeBoundedVariation mu nu).vectorMeasure).real
        (Iic x) := by
  rw [cumulativeMassClock,
    signedCumulativeVectorMeasure_totalVariation_eq_sum hSingular,
    measureReal_add_apply]

/-- The mutually singular occupation formula is therefore equivalent to the
positive-part coarea formula for the cumulative BV vector measure. -/
theorem
    mutuallySingularPositiveCrossingOccupationFormula_iff_vectorMeasurePositivePart :
    MutuallySingularPositiveCrossingOccupationFormula ↔
      ∀ mu nu : FiniteMeasure Real,
        FiniteMutuallySingular mu nu →
          ∀ s : Set Real, MeasurableSet s →
            (∫⁻ h,
                ((positiveCrossingFiber mu nu s h).encard : ENNReal)
              ∂(volume : Measure Real)) =
              (SignedMeasure.toJordanDecomposition
                  (signedCumulativeBoundedVariation mu nu).vectorMeasure).posPart s := by
  constructor
  · intro hOccupation mu nu hSingular s hs
    rw [signedCumulativeVectorMeasure_positivePart_eq_source hSingular]
    exact hOccupation mu nu hSingular s hs
  · intro hOccupation mu nu hSingular s hs
    rw [← signedCumulativeVectorMeasure_positivePart_eq_source hSingular]
    exact hOccupation mu nu hSingular s hs

end

end ConcaveOTLimit
