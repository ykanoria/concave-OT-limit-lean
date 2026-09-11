import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

private theorem measurePreservingFst
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (E × E)) (mu : Measure E) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.1

private theorem measurePreservingSnd
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (E × E)) (nu : Measure E) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.2

private theorem integralCompMeasurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {m : Measure A} {n : Measure B} {f : A -> B}
    (hf : MeasurePreserving f m n) {g : B -> Real}
    (hg : AEStronglyMeasurable g n) :
    (∫ x, g (f x) ∂m) = ∫ y, g y ∂n := by
  calc
    (∫ x, g (f x) ∂m) = ∫ y, g y ∂Measure.map f m :=
      (integral_map hf.measurable.aemeasurable (hf.map_eq ▸ hg)).symm
    _ = ∫ y, g y ∂n := by rw [hf.map_eq]

private def clip (K r : Real) : Real :=
  max (-K) (min r K)

private theorem continuousClip (K : Real) : Continuous (clip K) := by
  exact continuous_const.max (continuous_id.min continuous_const)

private theorem absClipLe (K r : Real) (hK : 0 <= K) :
    |clip K r| <= K := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le_iff.mpr
    ⟨by linarith, min_le_right _ _⟩⟩

@[simp]
private theorem clipEqSelf {K r : Real} (hr : |r| <= K) :
    clip K r = r := by
  rw [abs_le] at hr
  simp [clip, hr.1, hr.2]

private theorem absSubClipLeIndicator (K r : Real) (hK : 0 <= K) :
    |r - clip K r| <= {s | K < |s|}.indicator abs r := by
  by_cases hr : |r| <= K
  · have hrNot : r ∉ {s : Real | K < |s|} := by
      simpa using not_lt_of_ge hr
    simp [clipEqSelf hr, hrNot]
  · have hrMem : r ∈ {s : Real | K < |s|} := by
      simpa using lt_of_not_ge hr
    rw [indicator_of_mem hrMem]
    by_cases hLow : r < -K
    · have hMin : min r K = r := min_eq_left (by linarith)
      have hClip : clip K r = -K :=
        max_eq_left (by simpa [hMin] using hLow.le)
      rw [hClip, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have hLow' : -K <= r := le_of_not_gt hLow
      by_cases hUpper : r <= K
      · exact (hr (abs_le.mpr ⟨hLow', hUpper⟩)).elim
      · have hUpper' : K < r := lt_of_not_ge hUpper
        have hMin : min r K = K := min_eq_right hUpper'.le
        have hClip : clip K r = K := by
          simp [clip, hMin, neg_le_self hK]
        rw [hClip, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        linarith

private theorem absIntegralSubIntegralClipLe
    {A : Type*} [MeasurableSpace A] {m : Measure A} [IsFiniteMeasure m]
    {f : A -> Real} (hf : Integrable f m) (hfMeasurable : Measurable f)
    (K : Real) (hK : 0 <= K) :
    |(∫ x, f x ∂m) - ∫ x, clip K (f x) ∂m| <=
      ∫ x in {x | K < |f x|}, |f x| ∂m := by
  have hClipMeasurable :
      AEStronglyMeasurable (fun x => clip K (f x)) m :=
    ((continuousClip K).measurable.comp hfMeasurable).aestronglyMeasurable
  have hClipIntegrable : Integrable (fun x => clip K (f x)) m := by
    refine (integrable_const K).mono' hClipMeasurable ?_
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      simpa only [Real.norm_eq_abs] using absClipLe K (f x) hK
  have hSubIntegrable : Integrable (fun x => f x - clip K (f x)) m :=
    hf.sub hClipIntegrable
  have hAbsIntegrable : Integrable (fun x => |f x|) m := hf.abs
  have hTailMeasurable : MeasurableSet {x | K < |f x|} :=
    (continuous_abs.measurable.comp hfMeasurable) measurableSet_Ioi
  calc
    |(∫ x, f x ∂m) - ∫ x, clip K (f x) ∂m| =
        |∫ x, (f x - clip K (f x)) ∂m| := by
      rw [integral_sub hf hClipIntegrable]
    _ <= ∫ x, |f x - clip K (f x)| ∂m :=
      abs_integral_le_integral_abs
    _ <= ∫ x, {y | K < |f y|}.indicator (fun y => |f y|) x ∂m := by
      exact integral_mono hSubIntegrable.abs
        (hAbsIntegrable.indicator hTailMeasurable)
        (fun x => absSubClipLeIndicator K (f x) hK)
    _ = ∫ x in {x | K < |f x|}, |f x| ∂m := by
      rw [integral_indicator hTailMeasurable]

private theorem tendstoIntegralOfUniformValueTails
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A]
    {measures : Nat -> FiniteMeasure A} {limitMeasure : FiniteMeasure A}
    {f : A -> Real}
    (hMeasures : Tendsto measures atTop (nhds limitMeasure))
    (hContinuous : Continuous f)
    (hIntegrable : ∀ n, Integrable f (measures n : Measure A))
    (hLimitIntegrable : Integrable f (limitMeasure : Measure A))
    (hTail : ∀ ⦃epsilon : Real⦄, 0 < epsilon ->
      ∃ K : Real, 0 <= K ∧
        (∀ n, (∫ x in {x | K < |f x|}, |f x|
          ∂(measures n : Measure A)) < epsilon) ∧
        (∫ x in {x | K < |f x|}, |f x|
          ∂(limitMeasure : Measure A)) < epsilon) :
    Tendsto (fun n => ∫ x, f x ∂(measures n : Measure A)) atTop
      (nhds (∫ x, f x ∂(limitMeasure : Measure A))) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hEpsilon
  obtain ⟨K, hK, hTailMeasures, hTailLimit⟩ :=
    hTail (by linarith : 0 < epsilon / 3)
  let clipped : BoundedContinuousFunction A Real :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => clip K (f x)) ((continuousClip K).comp hContinuous) K
      (fun x => by
        rw [Real.norm_eq_abs]
        exact absClipLe K (f x) hK)
  have hClipped :
      Tendsto (fun n => ∫ x, clipped x ∂(measures n : Measure A)) atTop
        (nhds (∫ x, clipped x ∂(limitMeasure : Measure A))) :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hMeasures) clipped
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp hClipped (epsilon / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hLeft :=
    absIntegralSubIntegralClipLe
      (hIntegrable n) hContinuous.measurable K hK
  have hRight :=
    absIntegralSubIntegralClipLe
      hLimitIntegrable hContinuous.measurable K hK
  have hMiddle :
      |(∫ x, clipped x ∂(measures n : Measure A)) -
        ∫ x, clipped x ∂(limitMeasure : Measure A)| < epsilon / 3 := by
    simpa [Real.dist_eq] using hN n hn
  change |(∫ x, f x ∂(measures n : Measure A)) -
    ∫ x, f x ∂(limitMeasure : Measure A)| < epsilon
  have hLeft' :
      |(∫ x, f x ∂(measures n : Measure A)) -
        ∫ x, clipped x ∂(measures n : Measure A)| < epsilon / 3 :=
    hLeft.trans_lt (hTailMeasures n)
  have hRight' :
      |(∫ x, clipped x ∂(limitMeasure : Measure A)) -
        ∫ x, f x ∂(limitMeasure : Measure A)| < epsilon / 3 := by
    rw [abs_sub_comm]
    exact hRight.trans_lt hTailLimit
  calc
    |(∫ x, f x ∂(measures n : Measure A)) -
        ∫ x, f x ∂(limitMeasure : Measure A)| <=
        |(∫ x, f x ∂(measures n : Measure A)) -
          ∫ x, clipped x ∂(measures n : Measure A)| +
        |(∫ x, clipped x ∂(measures n : Measure A)) -
          ∫ x, clipped x ∂(limitMeasure : Measure A)| +
        |(∫ x, clipped x ∂(limitMeasure : Measure A)) -
          ∫ x, f x ∂(limitMeasure : Measure A)| := by
      calc
        |(∫ x, f x ∂(measures n : Measure A)) -
            ∫ x, f x ∂(limitMeasure : Measure A)| <=
            |(∫ x, f x ∂(measures n : Measure A)) -
              ∫ x, clipped x ∂(measures n : Measure A)| +
            |(∫ x, clipped x ∂(measures n : Measure A)) -
              ∫ x, f x ∂(limitMeasure : Measure A)| :=
          abs_sub_le _ _ _
        _ <= |(∫ x, f x ∂(measures n : Measure A)) -
              ∫ x, clipped x ∂(measures n : Measure A)| +
            (|(∫ x, clipped x ∂(measures n : Measure A)) -
              ∫ x, clipped x ∂(limitMeasure : Measure A)| +
            |(∫ x, clipped x ∂(limitMeasure : Measure A)) -
              ∫ x, f x ∂(limitMeasure : Measure A)|) := by
          linarith [abs_sub_le
            (∫ x, clipped x ∂(measures n : Measure A))
            (∫ x, clipped x ∂(limitMeasure : Measure A))
            (∫ x, f x ∂(limitMeasure : Measure A))]
        _ = _ := by ring
    _ < epsilon := by linarith

private theorem uniformDistanceTail
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E)) :
    ∀ ⦃epsilon : Real⦄, 0 < epsilon ->
      ∃ K : Real, 0 <= K ∧ ∀ gamma : FiniteCoupling mu nu,
        (∫ z in {z | K < ‖‖z.1 - z.2‖‖}, ‖‖z.1 - z.2‖‖
          ∂(gamma.plan : Measure (E × E))) < epsilon := by
  intro epsilon hEpsilon
  let tailSet : Nat -> Set E := fun k => {x | (k : Real) < ‖x‖}
  have hTailMeasurable : ∀ k, MeasurableSet (tailSet k) := by
    intro k
    exact continuous_norm.measurable measurableSet_Ioi
  have hTailAntitone : Antitone tailSet := by
    intro i j hij x hx
    change (j : Real) < ‖x‖ at hx
    change (i : Real) < ‖x‖
    exact lt_of_le_of_lt (by exact_mod_cast hij) hx
  have hTailInter : ⋂ k, tailSet k = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxAll : ∀ k : Nat, (k : Real) < ‖x‖ := by
      intro k
      exact mem_iInter.mp hx k
    obtain ⟨k, hk⟩ : ∃ k : Nat, ‖x‖ < (k : Real) :=
      exists_nat_gt ‖x‖
    exact (not_lt_of_ge hk.le) (hxAll k)
  have hMuTail :
      Tendsto (fun k => ∫ x in tailSet k, ‖x‖ ∂(mu : Measure E))
        atTop (nhds 0) := by
    have h :=
      hTailAntitone.tendsto_setIntegral hTailMeasurable hMu.integrableOn
    rw [hTailInter] at h
    simpa using h
  have hNuTail :
      Tendsto (fun k => ∫ y in tailSet k, ‖y‖ ∂(nu : Measure E))
        atTop (nhds 0) := by
    have h :=
      hTailAntitone.tendsto_setIntegral hTailMeasurable hNu.integrableOn
    rw [hTailInter] at h
    simpa using h
  have hMuSmall :
      ∀ᶠ k in atTop,
        (∫ x in tailSet k, ‖x‖ ∂(mu : Measure E)) < epsilon / 4 :=
    hMuTail.eventually (Iio_mem_nhds (by linarith))
  have hNuSmall :
      ∀ᶠ k in atTop,
        (∫ y in tailSet k, ‖y‖ ∂(nu : Measure E)) < epsilon / 4 :=
    hNuTail.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨k, hkMu, hkNu⟩ :=
    Filter.Eventually.exists (hMuSmall.and hNuSmall)
  let K : Real := 2 * k
  refine ⟨K, by positivity, fun gamma => ?_⟩
  let D : E × E -> Real := fun z => ‖z.1 - z.2‖
  let A : Set (E × E) := {z | K < ‖D z‖}
  have hA : MeasurableSet A :=
    ((measurable_fst.sub measurable_snd).norm.norm) measurableSet_Ioi
  have hDistance : Integrable D (gamma.plan : Measure (E × E)) :=
    distanceIntegrableOfMarginalFirstMoments hMu hNu gamma
  have hFirst : Integrable
      (fun z : E × E =>
        (tailSet k).indicator (fun x : E => ‖x‖) z.1)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingFst gamma).integrable_comp_of_integrable
      (hMu.indicator (hTailMeasurable k))
  have hSecond : Integrable
      (fun z : E × E =>
        (tailSet k).indicator (fun y : E => ‖y‖) z.2)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingSnd gamma).integrable_comp_of_integrable
      (hNu.indicator (hTailMeasurable k))
  have hFirstIntegral :
      (∫ z, (tailSet k).indicator (fun x : E => ‖x‖) z.1
          ∂(gamma.plan : Measure (E × E))) =
        ∫ x in tailSet k, ‖x‖ ∂(mu : Measure E) := by
    calc
      _ = ∫ x, (tailSet k).indicator (fun x : E => ‖x‖) x
          ∂(mu : Measure E) :=
        integralCompMeasurePreserving (measurePreservingFst gamma)
          (hMu.indicator (hTailMeasurable k)).aestronglyMeasurable
      _ = _ := integral_indicator (hTailMeasurable k)
  have hSecondIntegral :
      (∫ z, (tailSet k).indicator (fun y : E => ‖y‖) z.2
          ∂(gamma.plan : Measure (E × E))) =
        ∫ y in tailSet k, ‖y‖ ∂(nu : Measure E) := by
    calc
      _ = ∫ y, (tailSet k).indicator (fun y : E => ‖y‖) y
          ∂(nu : Measure E) :=
        integralCompMeasurePreserving (measurePreservingSnd gamma)
          (hNu.indicator (hTailMeasurable k)).aestronglyMeasurable
      _ = _ := integral_indicator (hTailMeasurable k)
  have hPointwise : ∀ z : E × E,
      A.indicator (fun z => ‖D z‖) z <=
        2 * (tailSet k).indicator (fun x : E => ‖x‖) z.1 +
        2 * (tailSet k).indicator (fun y : E => ‖y‖) z.2 := by
    intro z
    by_cases hz : z ∈ A
    · have hz' : K < ‖D z‖ := hz
      rw [Real.norm_of_nonneg (by simp [D])] at hz'
      have hLarge : 2 * (k : Real) < D z := by
        simpa [K] using hz'
      by_cases hx : (k : Real) < ‖z.1‖
      · by_cases hy : (k : Real) < ‖z.2‖
        · simp [indicator_of_mem hz, tailSet, hx, hy, D,
            Real.norm_of_nonneg (norm_nonneg _)]
          nlinarith [norm_sub_le z.1 z.2, norm_nonneg z.1, norm_nonneg z.2]
        · have hyLe : ‖z.2‖ <= (k : Real) := le_of_not_gt hy
          have hSecondLeFirst : ‖z.2‖ <= ‖z.1‖ := by linarith
          simp [indicator_of_mem hz, tailSet, hx, hy, D,
            Real.norm_of_nonneg (norm_nonneg _)]
          linarith [norm_sub_le z.1 z.2]
      · have hxLe : ‖z.1‖ <= (k : Real) := le_of_not_gt hx
        have hy : (k : Real) < ‖z.2‖ := by
          by_contra hy
          have hyLe : ‖z.2‖ <= (k : Real) := le_of_not_gt hy
          linarith [norm_sub_le z.1 z.2]
        have hFirstLeSecond : ‖z.1‖ <= ‖z.2‖ := by linarith
        simp [indicator_of_mem hz, tailSet, hx, hy, D,
          Real.norm_of_nonneg (norm_nonneg _)]
        linarith [norm_sub_le z.1 z.2]
    · by_cases hx : z.1 ∈ tailSet k <;>
        by_cases hy : z.2 ∈ tailSet k <;>
        simp [Set.indicator_of_notMem hz, hx, hy, norm_nonneg] <;>
        positivity
  have hLeft :
      Integrable (A.indicator fun z => ‖D z‖)
        (gamma.plan : Measure (E × E)) := by
    exact hDistance.norm.indicator hA
  have hRight :
      Integrable
        (fun z : E × E =>
          2 * (tailSet k).indicator (fun x : E => ‖x‖) z.1 +
          2 * (tailSet k).indicator (fun y : E => ‖y‖) z.2)
        (gamma.plan : Measure (E × E)) :=
    (hFirst.const_mul 2).add (hSecond.const_mul 2)
  have hIntegralLe :
      (∫ z in A, ‖D z‖ ∂(gamma.plan : Measure (E × E))) <=
        2 * (∫ x in tailSet k, ‖x‖ ∂(mu : Measure E)) +
        2 * (∫ y in tailSet k, ‖y‖ ∂(nu : Measure E)) := by
    have hMono := integral_mono hLeft hRight hPointwise
    rw [integral_indicator hA, integral_add (hFirst.const_mul 2)
      (hSecond.const_mul 2), integral_const_mul, integral_const_mul,
      hFirstIntegral, hSecondIntegral] at hMono
    exact hMono
  have hTail :
      (∫ z in A, ‖D z‖ ∂(gamma.plan : Measure (E × E))) < epsilon := by
    linarith
  simpa [A, D] using hTail

/-- Fixed integrable marginals make the distance cost sequentially
continuous on their coupling space. -/
theorem distanceCostSequentiallyContinuousOfMarginalFirstMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E))
    {gammaSeq : Nat -> FiniteCoupling mu nu}
    {gamma : FiniteCoupling mu nu}
    (hGamma : Tendsto gammaSeq atTop (nhds gamma)) :
    Tendsto (fun n => distanceCost (gammaSeq n))
      atTop (nhds (distanceCost gamma)) := by
  have hPlans :
      Tendsto (fun n => (gammaSeq n).plan) atTop (nhds gamma.plan) := by
    exact (continuous_subtype_val.tendsto gamma).comp hGamma
  let D : E × E -> Real := fun z => ‖z.1 - z.2‖
  have hDistanceContinuous : Continuous D :=
    (continuous_fst.sub continuous_snd).norm
  have hTendsto :=
    tendstoIntegralOfUniformValueTails hPlans hDistanceContinuous
      (fun n =>
        distanceIntegrableOfMarginalFirstMoments hMu hNu (gammaSeq n))
      (distanceIntegrableOfMarginalFirstMoments hMu hNu gamma)
      (fun epsilon hEpsilon => by
        obtain ⟨K, hK, hTail⟩ :=
          uniformDistanceTail hMu hNu hEpsilon
        exact ⟨K, hK, fun n => hTail (gammaSeq n), hTail gamma⟩)
  simpa [distanceCost, profileCost, D] using hTendsto

end ConcaveOTLimit
