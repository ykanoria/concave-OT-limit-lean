import Theorems.Thm_ConcaveOTLimit_PsiNormSubBound
import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set Topology

open ConcaveOTLimit

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

private theorem psiNonnegative {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem leOneAddPsi {r : Real} (hr : 0 <= r) :
    r <= 1 + Psi r := by
  by_cases hrOne : r <= 1
  · linarith [psiNonnegative hr]
  · have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one (le_of_not_ge hrOne)
    have hLog :=
      Real.one_sub_inv_le_log_of_pos (show 0 < 1 + r by linarith)
    have hMul :
        r * (1 - (1 + r)⁻¹) <= r * Real.log (1 + r) :=
      mul_le_mul_of_nonneg_left hLog hr
    have hFraction : r / (1 + r) <= 1 :=
      (div_le_one (by linarith)).2 (by linarith)
    rw [mul_sub, mul_one] at hMul
    rw [div_eq_mul_inv] at hFraction
    unfold Psi
    linarith

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

private theorem distanceIntegrable
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    Integrable (fun z : E × E => ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  have hRecovery :=
    recoveryBoundIntegrableOfMarginalLogMoments hMu hNu gamma
  have hPsi : Integrable (fun z : E × E => Psi ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
    exact (hRecovery.sub (integrable_const 2)).congr
      (ae_of_all _ fun z => by simp)
  refine ((integrable_const 1).add hPsi).mono'
    ((measurable_fst.sub measurable_snd).norm).aestronglyMeasurable
    (ae_of_all _ ?_)
  intro z
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact leOneAddPsi (norm_nonneg _)

private theorem uniformDistanceTail
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E)) :
    ∀ ⦃epsilon : Real⦄, 0 < epsilon ->
      ∃ K : Real, 0 <= K ∧ ∀ gamma : FiniteCoupling mu nu,
        (∫ z in {z | K < ‖‖z.1 - z.2‖‖}, ‖‖z.1 - z.2‖‖
          ∂(gamma.plan : Measure (E × E))) < epsilon := by
  intro epsilon hEpsilon
  let C : Real :=
    4 * ((mu : Measure E).real univ +
      (∫ x, Psi ‖x‖ ∂(mu : Measure E)) +
      ∫ y, Psi ‖y‖ ∂(nu : Measure E))
  have hMuIntegral : 0 <= ∫ x, Psi ‖x‖ ∂(mu : Measure E) :=
    integral_nonneg fun x => psiNonnegative (norm_nonneg x)
  have hNuIntegral : 0 <= ∫ y, Psi ‖y‖ ∂(nu : Measure E) :=
    integral_nonneg fun y => psiNonnegative (norm_nonneg y)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  let L : Real := C / epsilon + 1
  have hL : 0 < L := by
    dsimp [L]
    positivity
  let K : Real := Real.exp L
  refine ⟨K, (Real.exp_pos L).le, fun gamma => ?_⟩
  let D : E × E -> Real := fun z => ‖z.1 - z.2‖
  let P : E × E -> Real := fun z => Psi (D z)
  let A : Set (E × E) := {z | K < ‖D z‖}
  have hD : Integrable D (gamma.plan : Measure (E × E)) :=
    distanceIntegrable hMu hNu gamma
  have hRecovery :=
    recoveryBoundIntegrableOfMarginalLogMoments hMu hNu gamma
  have hP : Integrable P (gamma.plan : Measure (E × E)) := by
    exact (hRecovery.sub (integrable_const 2)).congr
      (ae_of_all _ fun z => by simp [P, D])
  have hFirst : Integrable (fun z : E × E => Psi ‖z.1‖)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingFst gamma).integrable_comp_of_integrable hMu
  have hSecond : Integrable (fun z : E × E => Psi ‖z.2‖)
      (gamma.plan : Measure (E × E)) :=
    (measurePreservingSnd gamma).integrable_comp_of_integrable hNu
  have hDominating : Integrable
      (fun z : E × E => 4 * (1 + Psi ‖z.1‖ + Psi ‖z.2‖))
      (gamma.plan : Measure (E × E)) :=
    (((integrable_const 1).add hFirst).add hSecond).const_mul 4
  have hOneFirst : Integrable
      (fun z : E × E => 1 + Psi ‖z.1‖)
      (gamma.plan : Measure (E × E)) :=
    (integrable_const 1).add hFirst
  have hIntegralSum :
      (∫ z, 1 + Psi ‖z.1‖ + Psi ‖z.2‖
        ∂(gamma.plan : Measure (E × E))) =
      (∫ z, 1 + Psi ‖z.1‖ ∂(gamma.plan : Measure (E × E))) +
        ∫ z, Psi ‖z.2‖ ∂(gamma.plan : Measure (E × E)) := by
    simpa only using integral_add hOneFirst hSecond
  have hIntegralFirst :
      (∫ z, 1 + Psi ‖z.1‖ ∂(gamma.plan : Measure (E × E))) =
      (∫ _z : E × E, (1 : Real) ∂(gamma.plan : Measure (E × E))) +
        ∫ z, Psi ‖z.1‖ ∂(gamma.plan : Measure (E × E)) := by
    simpa only using integral_add (integrable_const 1) hFirst
  have hFirstIntegral :
      (∫ z, Psi ‖z.1‖ ∂(gamma.plan : Measure (E × E))) =
        ∫ x, Psi ‖x‖ ∂(mu : Measure E) :=
    integralCompMeasurePreserving (measurePreservingFst gamma)
      hMu.aestronglyMeasurable
  have hSecondIntegral :
      (∫ z, Psi ‖z.2‖ ∂(gamma.plan : Measure (E × E))) =
        ∫ y, Psi ‖y‖ ∂(nu : Measure E) :=
    integralCompMeasurePreserving (measurePreservingSnd gamma)
      hNu.aestronglyMeasurable
  have hMass :
      (gamma.plan : Measure (E × E)).real univ =
        (mu : Measure E).real univ := by
    rw [← (measurePreservingFst gamma).map_eq,
      map_measureReal_apply measurable_fst MeasurableSet.univ, preimage_univ]
  have hPBound : (∫ z, P z ∂(gamma.plan : Measure (E × E))) <= C := by
    calc
      (∫ z, P z ∂(gamma.plan : Measure (E × E))) <=
          ∫ z, 4 * (1 + Psi ‖z.1‖ + Psi ‖z.2‖)
            ∂(gamma.plan : Measure (E × E)) := by
        exact integral_mono hP hDominating fun z => PsiNormSubBound z.1 z.2
      _ = C := by
        rw [integral_const_mul, hIntegralSum, hIntegralFirst,
          integral_const, hFirstIntegral, hSecondIntegral]
        simp [hMass, C]
  have hA : MeasurableSet A :=
    ((measurable_fst.sub measurable_snd).norm.norm) measurableSet_Ioi
  have hPointwise : ∀ z ∈ A, L * D z <= P z := by
    intro z hz
    have hKD : Real.exp L < D z := by
      simpa [A, K, D, Real.norm_of_nonneg (norm_nonneg _)] using hz
    have hExp : Real.exp L < 1 + D z := by linarith
    have hLog : L <= Real.log (1 + D z) :=
      (Real.lt_log_iff_exp_lt (by positivity)).2 hExp |>.le
    have hMul :=
      mul_le_mul_of_nonneg_left hLog (norm_nonneg (z.1 - z.2))
    simpa [P, D, Psi, mul_comm] using hMul
  have hScaledTail :
      L * (∫ z in A, D z ∂(gamma.plan : Measure (E × E))) <= C := by
    calc
      L * (∫ z in A, D z ∂(gamma.plan : Measure (E × E))) =
          ∫ z in A, L * D z ∂(gamma.plan : Measure (E × E)) := by
        rw [integral_const_mul]
      _ <= ∫ z in A, P z ∂(gamma.plan : Measure (E × E)) :=
        setIntegral_mono_on (hD.const_mul L).integrableOn
          hP.integrableOn hA hPointwise
      _ <= ∫ z, P z ∂(gamma.plan : Measure (E × E)) := by
        have hMono := setIntegral_mono_set (s := A) (t := univ)
          hP.integrableOn
            (ae_of_all _ fun z => psiNonnegative (norm_nonneg (z.1 - z.2)))
            (ae_of_all _ (subset_univ A))
        simpa only [setIntegral_univ] using hMono
      _ <= C := hPBound
  have hTailNonnegative :
      0 <= ∫ z in A, D z ∂(gamma.plan : Measure (E × E)) :=
    integral_nonneg fun z => norm_nonneg (z.1 - z.2)
  have hTail :
      (∫ z in A, D z ∂(gamma.plan : Measure (E × E))) < epsilon := by
    by_contra hNot
    have hEpsilonLe :
        epsilon <= ∫ z in A, D z ∂(gamma.plan : Measure (E × E)) :=
      le_of_not_gt hNot
    have hScaledEpsilon :
        L * epsilon <= L * (∫ z in A, D z
          ∂(gamma.plan : Measure (E × E))) :=
      mul_le_mul_of_nonneg_left hEpsilonLe hL.le
    have hIdentity : L * epsilon = C + epsilon := by
      dsimp [L]
      field_simp
    linarith
  simpa [A, D] using hTail

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
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
      (fun n => distanceIntegrable hMu hNu (gammaSeq n))
      (distanceIntegrable hMu hNu gamma)
      (fun epsilon hEpsilon => by
        obtain ⟨K, hK, hTail⟩ :=
          uniformDistanceTail hMu hNu hEpsilon
        exact ⟨K, hK, fun n => hTail (gammaSeq n), hTail gamma⟩)
  simpa [distanceCost, profileCost, D] using hTendsto
