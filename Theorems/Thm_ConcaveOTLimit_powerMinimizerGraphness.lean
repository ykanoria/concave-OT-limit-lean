import Theorems.Thm_ConcaveOTLimit_distanceCyclicMonotoneSufficiency
import Theorems.Thm_ConcaveOTLimit_existsFiniteMeasureRemainderOfLe
import Theorems.Thm_ConcaveOTLimit_existsGraphPlanOfSupportedFstInjOn
import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMeasureSubsetOfAe
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular
import Theorems.Thm_ConcaveOTLimit_finiteMeasureReplacementPreservesMarginals
import Theorems.Thm_ConcaveOTLimit_radialRpowGradientInjective
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Snowflaking

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ConcaveOTLimit

private theorem graphness_firstMarginal_mass_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (firstMarginal rho).mass = rho.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass]
  exact FiniteMeasure.map_apply rho measurable_fst MeasurableSet.univ
    |>.trans (by simp)

private theorem graphness_secondMarginal_mass_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (secondMarginal rho).mass = rho.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass]
  exact FiniteMeasure.map_apply rho measurable_snd MeasurableSet.univ
    |>.trans (by simp)

private theorem graphness_firstMarginal_crossProduct
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho sigma : FiniteMeasure (X × Y)) :
    firstMarginal
        ((firstMarginal rho).prod (secondMarginal sigma)) =
      sigma.mass • firstMarginal rho := by
  unfold firstMarginal
  rw [FiniteMeasure.map_fst_prod]
  change
    (secondMarginal sigma).mass • rho.map Prod.fst =
      sigma.mass • rho.map Prod.fst
  rw [graphness_secondMarginal_mass_eq]

private theorem graphness_secondMarginal_crossProduct
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho sigma : FiniteMeasure (X × Y)) :
    secondMarginal
        ((firstMarginal rho).prod (secondMarginal sigma)) =
      rho.mass • secondMarginal sigma := by
  unfold secondMarginal
  rw [FiniteMeasure.map_snd_prod]
  change
    (firstMarginal rho).mass • sigma.map Prod.snd =
      rho.mass • sigma.map Prod.snd
  rw [graphness_firstMarginal_mass_eq]

private theorem graphness_firstMarginal_fintypeSum
    {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (rho : I -> FiniteMeasure (X × Y)) :
    firstMarginal (∑ i, rho i) =
      ∑ i, firstMarginal (rho i) := by
  classical
  change
    (FiniteMeasure.mapHom (Ω := X × Y) (Ω' := X) measurable_fst)
        (∑ i, rho i) =
      ∑ i,
        (FiniteMeasure.mapHom (Ω := X × Y) (Ω' := X) measurable_fst)
          (rho i)
  simpa using
    (map_sum
      (FiniteMeasure.mapHom (Ω := X × Y) (Ω' := X) measurable_fst)
      rho Finset.univ)

private theorem graphness_secondMarginal_fintypeSum
    {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (rho : I -> FiniteMeasure (X × Y)) :
    secondMarginal (∑ i, rho i) =
      ∑ i, secondMarginal (rho i) := by
  classical
  change
    (FiniteMeasure.mapHom (Ω := X × Y) (Ω' := Y) measurable_snd)
        (∑ i, rho i) =
      ∑ i,
        (FiniteMeasure.mapHom (Ω := X × Y) (Ω' := Y) measurable_snd)
          (rho i)
  simpa using
    (map_sum
      (FiniteMeasure.mapHom (Ω := X × Y) (Ω' := Y) measurable_snd)
      rho Finset.univ)

private theorem graphness_normalizedFiniteMeasure_mass
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) :
    rho.normalize.toFiniteMeasure.mass = 1 :=
  ProbabilityMeasure.mass_toFiniteMeasure rho.normalize

private theorem graphness_normalizedRestriction_mem_ae
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) (s : Set Omega)
    (hs : MeasurableSet s) (hRho : rho.restrict s ≠ 0) :
    ∀ᵐ z ∂((rho.restrict s).normalize.toFiniteMeasure :
        Measure Omega), z ∈ s := by
  rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero _ hRho,
    FiniteMeasure.toMeasure_smul]
  exact Measure.ae_smul_measure (ae_restrict_mem hs) _

private theorem graphness_crossProduct_mem_pulledBalls
    {E F : Type*} [MeasurableSpace E] [PseudoMetricSpace F]
    (q : E -> F)
    (rho sigma : FiniteMeasure (E × E))
    (x y : E) (r : Real)
    (hRho :
      ∀ᵐ z ∂(rho : Measure (E × E)),
        q z.1 ∈ Metric.ball (q x) r)
    (hSigma :
      ∀ᵐ z ∂(sigma : Measure (E × E)),
        q z.2 ∈ Metric.ball (q y) r)
    (hBallMeasurable :
      ∀ a : E, MeasurableSet (q ⁻¹' Metric.ball (q a) r)) :
    ∀ᵐ z ∂(((firstMarginal rho).prod
        (secondMarginal sigma) : FiniteMeasure (E × E)) :
      Measure (E × E)),
      q z.1 ∈ Metric.ball (q x) r ∧
        q z.2 ∈ Metric.ball (q y) r := by
  have hFirst :
      ∀ᵐ a ∂(firstMarginal rho : Measure E),
        q a ∈ Metric.ball (q x) r := by
    rw [firstMarginal, FiniteMeasure.toMeasure_map]
    exact
      (ae_map_iff measurable_fst.aemeasurable
        (hBallMeasurable x)).2 hRho
  have hSecond :
      ∀ᵐ b ∂(secondMarginal sigma : Measure E),
        q b ∈ Metric.ball (q y) r := by
    rw [secondMarginal, FiniteMeasure.toMeasure_map]
    exact
      (ae_map_iff measurable_snd.aemeasurable
        (hBallMeasurable y)).2 hSigma
  rw [FiniteMeasure.toMeasure_prod]
  apply
    (Measure.ae_prod_iff_ae_ae
      ((hBallMeasurable x).prod (hBallMeasurable y))).2
  filter_upwards [hFirst] with a ha
  filter_upwards [hSecond] with b hb
  exact ⟨ha, hb⟩

private theorem graphness_integralPulledDistance_mem_prod_ball_bounds
    {E F : Type*} [MeasurableSpace E] [PseudoMetricSpace F]
    (q : E -> F)
    (rho : FiniteMeasure (E × E)) (x y : E) (r : Real)
    (hMass : rho.mass = 1)
    (hSupported :
      ∀ᵐ z ∂(rho : Measure (E × E)),
        q z.1 ∈ Metric.ball (q x) r ∧
          q z.2 ∈ Metric.ball (q y) r)
    (hIntegrable :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (rho : Measure (E × E))) :
    dist (q x) (q y) - 2 * r <=
        ∫ z, dist (q z.1) (q z.2)
          ∂(rho : Measure (E × E)) ∧
      (∫ z, dist (q z.1) (q z.2)
          ∂(rho : Measure (E × E))) <=
        dist (q x) (q y) + 2 * r := by
  have hConstantIntegral (a : Real) :
      (∫ _z : E × E, a ∂(rho : Measure (E × E))) = a := by
    rw [integral_const]
    simp only [FiniteMeasure.measureReal_eq_coe_coeFn, smul_eq_mul]
    change (rho.mass : Real) * a = a
    rw [hMass]
    simp
  have hLower :
      (fun _z : E × E => dist (q x) (q y) - 2 * r) ≤ᵐ[
          (rho : Measure (E × E))]
        (fun z => dist (q z.1) (q z.2)) := by
    filter_upwards [hSupported] with z hz
    have hxBall : dist (q z.1) (q x) < r :=
      Metric.mem_ball.mp hz.1
    have hy : dist (q z.2) (q y) < r :=
      Metric.mem_ball.mp hz.2
    have hx : dist (q x) (q z.1) < r := by
      simpa [dist_comm] using hxBall
    have hTriangle :
        dist (q x) (q y) <=
          dist (q x) (q z.1) +
            dist (q z.1) (q z.2) +
              dist (q z.2) (q y) := by
      calc
        dist (q x) (q y) <=
            dist (q x) (q z.1) + dist (q z.1) (q y) :=
          dist_triangle _ _ _
        _ <= dist (q x) (q z.1) +
            (dist (q z.1) (q z.2) + dist (q z.2) (q y)) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    linarith
  have hUpper :
      (fun z : E × E => dist (q z.1) (q z.2)) ≤ᵐ[
          (rho : Measure (E × E))]
        (fun _z => dist (q x) (q y) + 2 * r) := by
    filter_upwards [hSupported] with z hz
    have hx : dist (q z.1) (q x) < r :=
      Metric.mem_ball.mp hz.1
    have hyBall : dist (q z.2) (q y) < r :=
      Metric.mem_ball.mp hz.2
    have hy : dist (q y) (q z.2) < r := by
      simpa [dist_comm] using hyBall
    have hTriangle :
        dist (q z.1) (q z.2) <=
          dist (q z.1) (q x) +
            dist (q x) (q y) +
              dist (q y) (q z.2) := by
      calc
        dist (q z.1) (q z.2) <=
            dist (q z.1) (q x) + dist (q x) (q z.2) :=
          dist_triangle _ _ _
        _ <= dist (q z.1) (q x) +
            (dist (q x) (q y) + dist (q y) (q z.2)) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    linarith
  constructor
  · calc
      dist (q x) (q y) - 2 * r =
          ∫ _z : E × E, dist (q x) (q y) - 2 * r
            ∂(rho : Measure (E × E)) :=
        (hConstantIntegral _).symm
      _ <= ∫ z, dist (q z.1) (q z.2)
          ∂(rho : Measure (E × E)) :=
        integral_mono_ae (integrable_const _) hIntegrable hLower
  · calc
      (∫ z, dist (q z.1) (q z.2)
          ∂(rho : Measure (E × E))) <=
          ∫ _z : E × E, dist (q x) (q y) + 2 * r
            ∂(rho : Measure (E × E)) :=
        integral_mono_ae hIntegrable (integrable_const _) hUpper
      _ = dist (q x) (q y) + 2 * r := hConstantIntegral _

private theorem graphness_integrablePulledDistance_of_mem_prod_ball
    {E F : Type*} [MeasurableSpace E] [PseudoMetricSpace F]
    (q : E -> F)
    (hMeasurable :
      Measurable (fun z : E × E => dist (q z.1) (q z.2)))
    (rho : FiniteMeasure (E × E))
    (x y : E) (r : Real)
    (hSupported :
      ∀ᵐ z ∂(rho : Measure (E × E)),
        q z.1 ∈ Metric.ball (q x) r ∧
          q z.2 ∈ Metric.ball (q y) r) :
    Integrable (fun z : E × E => dist (q z.1) (q z.2))
      (rho : Measure (E × E)) := by
  apply Integrable.of_bound hMeasurable.aestronglyMeasurable
    (dist (q x) (q y) + 2 * |r|)
  filter_upwards [hSupported] with z hz
  have hx : dist (q z.1) (q x) < r :=
    Metric.mem_ball.mp hz.1
  have hyBall : dist (q z.2) (q y) < r :=
    Metric.mem_ball.mp hz.2
  have hy : dist (q y) (q z.2) < r := by
    simpa [dist_comm] using hyBall
  have hTriangle :
      dist (q z.1) (q z.2) <=
        dist (q z.1) (q x) +
          dist (q x) (q y) +
            dist (q y) (q z.2) := by
    calc
      dist (q z.1) (q z.2) <=
          dist (q z.1) (q x) + dist (q x) (q z.2) :=
        dist_triangle _ _ _
      _ <= dist (q z.1) (q x) +
          (dist (q x) (q y) + dist (q y) (q z.2)) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  have hr : r <= |r| := le_abs_self r
  linarith

/-- Local finite rerouting for a cost pulled back from a metric proves that
the topological support of every integrable minimizer is cyclically
monotone for that cost. -/
private theorem pulledMetric_minimizerSupportCyclic
    {E F : Type*}
    [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [OpensMeasurableSpace (E × E)]
    [PseudoMetricSpace F]
    (q : E -> F) (hq : Continuous q)
    (hCostMeasurable :
      Measurable (fun z : E × E => dist (q z.1) (q z.2)))
    {mu nu : FiniteMeasure E}
    (gamma : FiniteCoupling mu nu)
    (hGammaIntegrable :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (gamma.plan : Measure (E × E)))
    (hMinimal :
      ∀ eta : FiniteCoupling mu nu,
        (∫ z, dist (q z.1) (q z.2)
            ∂(gamma.plan : Measure (E × E))) <=
          ∫ z, dist (q z.1) (q z.2)
            ∂(eta.plan : Measure (E × E))) :
    ∀ {I : Type*} [Fintype I] (x y : I -> E),
      (∀ i, (x i, y i) ∈
        Measure.support (gamma.plan : Measure (E × E))) ->
      ∀ sigma : Equiv.Perm I,
        (∑ i, dist (q (x i)) (q (y i))) <=
          ∑ i, dist (q (x i)) (q (y (sigma i))) := by
  classical
  intro I _ x y hSupport sigma
  by_contra hCycle
  have hStrict :
      (∑ i, dist (q (x i)) (q (y (sigma i)))) <
        ∑ i, dist (q (x i)) (q (y i)) :=
    lt_of_not_ge hCycle
  have hNonempty : Nonempty I := by
    by_contra hEmpty
    letI : IsEmpty I := not_nonempty_iff.mp hEmpty
    simpa using hStrict
  letI : Nonempty I := hNonempty
  letI : Nonempty E := ⟨x (Classical.choice hNonempty)⟩
  let gap : Real :=
    (∑ i, dist (q (x i)) (q (y i))) -
      ∑ i, dist (q (x i)) (q (y (sigma i)))
  have hGapPos : 0 < gap := sub_pos.mpr hStrict
  have hCardPos : 0 < (Fintype.card I : Real) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hNonempty)
  let r : Real := gap / (8 * (Fintype.card I : Real))
  have hRPos : 0 < r :=
    div_pos hGapPos (mul_pos (by norm_num) hCardPos)
  have hError :
      4 * (Fintype.card I : Real) * r < gap := by
    have hDenom :
        8 * (Fintype.card I : Real) ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) hCardPos)
    have hEq :
        8 * (Fintype.card I : Real) * r = gap := by
      dsimp only [r]
      field_simp
    nlinarith
  let U : I -> Set (E × E) :=
    fun i =>
      (q ⁻¹' Metric.ball (q (x i)) r) ×ˢ
        (q ⁻¹' Metric.ball (q (y i)) r)
  have hUOpen (i : I) : IsOpen (U i) :=
    (Metric.isOpen_ball.preimage hq).prod
      (Metric.isOpen_ball.preimage hq)
  have hUMeasurable (i : I) : MeasurableSet (U i) :=
    (hUOpen i).measurableSet
  have hCenter (i : I) : (x i, y i) ∈ U i :=
    ⟨Metric.mem_ball_self hRPos, Metric.mem_ball_self hRPos⟩
  have hBlockMeasurePositive (i : I) :
      0 < (gamma.plan : Measure (E × E)) (U i) := by
    exact
      (Measure.mem_support_iff_forall (x i, y i)).mp (hSupport i)
        (U i) ((hUOpen i).mem_nhds (hCenter i))
  have hBlockPositive (i : I) : 0 < gamma.plan (U i) := by
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (gamma.plan : Measure (E × E)) (U i) = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null gamma.plan (U i)).mp hZero
    exact (ne_of_gt (hBlockMeasurePositive i)) hMeasureZero
  let raw : I -> FiniteMeasure (E × E) :=
    fun i => gamma.plan.restrict (U i)
  have hRawPositive (i : I) : 0 < (raw i).mass := by
    simpa only [raw, FiniteMeasure.restrict_mass] using hBlockPositive i
  have hRawNe (i : I) : raw i ≠ 0 :=
    (FiniteMeasure.mass_nonzero_iff (raw i)).mp
      (ne_of_gt (hRawPositive i))
  let rho : I -> FiniteMeasure (E × E) :=
    fun i => (raw i).normalize.toFiniteMeasure
  have hRhoMass (i : I) : (rho i).mass = 1 :=
    graphness_normalizedFiniteMeasure_mass (raw i)
  have hRhoEq (i : I) :
      rho i = (raw i).mass⁻¹ • raw i :=
    FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero
      (raw i) (hRawNe i)
  have hRhoSupported (i : I) :
      ∀ᵐ z ∂(rho i : Measure (E × E)),
        q z.1 ∈ Metric.ball (q (x i)) r ∧
          q z.2 ∈ Metric.ball (q (y i)) r := by
    simpa only [rho, raw, U] using
      graphness_normalizedRestriction_mem_ae gamma.plan (U i)
        (hUMeasurable i) (by simpa only [raw] using hRawNe i)
  let weight : NNReal := ∑ i, (raw i).mass⁻¹
  have hWeightPos : 0 < weight := by
    dsimp only [weight]
    exact
      Finset.sum_pos
        (fun i _ => inv_pos.mpr (hRawPositive i))
        Finset.univ_nonempty
  let c : NNReal := weight⁻¹
  have hCPos : 0 < c := inv_pos.mpr hWeightPos
  have hCWeight : c * weight = 1 := by
    dsimp only [c]
    exact inv_mul_cancel₀ (ne_of_gt hWeightPos)
  have hRhoLe (i : I) :
      (rho i : Measure (E × E)) <=
        (raw i).mass⁻¹ • (gamma.plan : Measure (E × E)) := by
    have hRawLe :
        (raw i : Measure (E × E)) <=
          (gamma.plan : Measure (E × E)) := by
      dsimp only [raw]
      exact Measure.restrict_le_self
    rw [hRhoEq i, FiniteMeasure.toMeasure_smul]
    intro s
    simp only [Measure.coe_nnreal_smul_apply]
    exact mul_le_mul_left' (hRawLe s) _
  have hRhoSumLe :
      ((∑ i, rho i : FiniteMeasure (E × E)) :
          Measure (E × E)) <=
        weight • (gamma.plan : Measure (E × E)) := by
    rw [FiniteMeasure.toMeasure_sum]
    calc
      (∑ i, (rho i : Measure (E × E))) <=
          ∑ i, (raw i).mass⁻¹ •
            (gamma.plan : Measure (E × E)) :=
        Finset.sum_le_sum fun i _ => hRhoLe i
      _ = weight • (gamma.plan : Measure (E × E)) := by
        rw [← Finset.sum_smul]
  let tau : I -> FiniteMeasure (E × E) :=
    fun i =>
      (firstMarginal (rho i)).prod
        (secondMarginal (rho (sigma i)))
  have hTauMass (i : I) : (tau i).mass = 1 := by
    dsimp only [tau]
    simp only [FiniteMeasure.mass_prod,
      graphness_firstMarginal_mass_eq,
      graphness_secondMarginal_mass_eq, hRhoMass, one_mul]
  have hPulledBallMeasurable (a : E) :
      MeasurableSet (q ⁻¹' Metric.ball (q a) r) :=
    (Metric.isOpen_ball.preimage hq).measurableSet
  have hTauSupported (i : I) :
      ∀ᵐ z ∂(tau i : Measure (E × E)),
        q z.1 ∈ Metric.ball (q (x i)) r ∧
          q z.2 ∈ Metric.ball (q (y (sigma i))) r := by
    dsimp only [tau]
    apply graphness_crossProduct_mem_pulledBalls q
    · exact (hRhoSupported i).mono fun z hz => hz.1
    · exact
        (hRhoSupported (sigma i)).mono fun z hz => hz.2
    · exact hPulledBallMeasurable
  let removed : FiniteMeasure (E × E) :=
    c • ∑ i, rho i
  let added : FiniteMeasure (E × E) :=
    c • ∑ i, tau i
  have hRemovedLe :
      (removed : Measure (E × E)) <=
        (gamma.plan : Measure (E × E)) := by
    dsimp only [removed]
    rw [FiniteMeasure.toMeasure_smul]
    intro s
    have hs := hRhoSumLe s
    simp only [Measure.coe_nnreal_smul_apply] at hs ⊢
    have hCWeightENN :
        (c : ENNReal) * (weight : ENNReal) = 1 := by
      exact_mod_cast hCWeight
    calc
      (c : ENNReal) *
          ((∑ i, rho i : FiniteMeasure (E × E)) :
            Measure (E × E)) s <=
          (c : ENNReal) *
            ((weight : ENNReal) *
              (gamma.plan : Measure (E × E)) s) :=
        mul_le_mul_left' hs _
      _ = (gamma.plan : Measure (E × E)) s := by
        rw [← mul_assoc, hCWeightENN, one_mul]
  have hFirstBase :
      firstMarginal (∑ i, tau i) =
        firstMarginal (∑ i, rho i) := by
    rw [graphness_firstMarginal_fintypeSum,
      graphness_firstMarginal_fintypeSum]
    apply Fintype.sum_congr
    intro i
    dsimp only [tau]
    rw [graphness_firstMarginal_crossProduct, hRhoMass]
    simp
  have hSecondBase :
      secondMarginal (∑ i, tau i) =
        secondMarginal (∑ i, rho i) := by
    rw [graphness_secondMarginal_fintypeSum,
      graphness_secondMarginal_fintypeSum]
    calc
      (∑ i, secondMarginal (tau i)) =
          ∑ i, secondMarginal (rho (sigma i)) := by
        apply Fintype.sum_congr
        intro i
        dsimp only [tau]
        rw [graphness_secondMarginal_crossProduct, hRhoMass]
        simp
      _ = ∑ i, secondMarginal (rho i) :=
        Equiv.sum_comp sigma fun i => secondMarginal (rho i)
  have hFirst :
      firstMarginal added = firstMarginal removed := by
    dsimp only [added, removed]
    simpa only [firstMarginal, FiniteMeasure.map_smul] using
      congrArg (fun eta : FiniteMeasure E => c • eta) hFirstBase
  have hSecond :
      secondMarginal added = secondMarginal removed := by
    dsimp only [added, removed]
    simpa only [secondMarginal, FiniteMeasure.map_smul] using
      congrArg (fun eta : FiniteMeasure E => c • eta) hSecondBase
  obtain
      ⟨remainder, _hRemainderSub, hRemainderLe, hDecomposition⟩ :=
    existsFiniteMeasureRemainderOfLe gamma.plan removed hRemovedLe
  have hMarginals :=
    finiteMeasureReplacementPreservesMarginals
      remainder removed added gamma.plan hDecomposition hFirst hSecond
  let eta : FiniteCoupling mu nu :=
    ⟨remainder + added,
      hMarginals.1.trans gamma.property.1,
      hMarginals.2.trans gamma.property.2⟩
  have hRhoIntegrable (i : I) :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (rho i : Measure (E × E)) :=
    graphness_integrablePulledDistance_of_mem_prod_ball
      q hCostMeasurable (rho i) (x i) (y i) r (hRhoSupported i)
  have hTauIntegrable (i : I) :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (tau i : Measure (E × E)) :=
    graphness_integrablePulledDistance_of_mem_prod_ball
      q hCostMeasurable (tau i) (x i) (y (sigma i)) r
        (hTauSupported i)
  have hRhoBounds (i : I) :
      dist (q (x i)) (q (y i)) - 2 * r <=
          ∫ z, dist (q z.1) (q z.2)
            ∂(rho i : Measure (E × E)) ∧
        (∫ z, dist (q z.1) (q z.2)
            ∂(rho i : Measure (E × E))) <=
          dist (q (x i)) (q (y i)) + 2 * r :=
    graphness_integralPulledDistance_mem_prod_ball_bounds
      q (rho i) (x i) (y i) r (hRhoMass i)
        (hRhoSupported i) (hRhoIntegrable i)
  have hTauBounds (i : I) :
      dist (q (x i)) (q (y (sigma i))) - 2 * r <=
          ∫ z, dist (q z.1) (q z.2)
            ∂(tau i : Measure (E × E)) ∧
        (∫ z, dist (q z.1) (q z.2)
            ∂(tau i : Measure (E × E))) <=
          dist (q (x i)) (q (y (sigma i))) + 2 * r :=
    graphness_integralPulledDistance_mem_prod_ball_bounds
      q (tau i) (x i) (y (sigma i)) r (hTauMass i)
        (hTauSupported i) (hTauIntegrable i)
  have hBaseCheaper :
      (∑ i, ∫ z, dist (q z.1) (q z.2)
          ∂(tau i : Measure (E × E))) <
        ∑ i, ∫ z, dist (q z.1) (q z.2)
          ∂(rho i : Measure (E × E)) := by
    calc
      (∑ i, ∫ z, dist (q z.1) (q z.2)
          ∂(tau i : Measure (E × E))) <=
          ∑ i, (dist (q (x i)) (q (y (sigma i))) + 2 * r) :=
        Finset.sum_le_sum fun i _ => (hTauBounds i).2
      _ < ∑ i, (dist (q (x i)) (q (y i)) - 2 * r) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp only [gap] at hError
        linarith
      _ <= ∑ i, ∫ z, dist (q z.1) (q z.2)
          ∂(rho i : Measure (E × E)) :=
        Finset.sum_le_sum fun i _ => (hRhoBounds i).1
  have hTauSumIntegrable :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        ((∑ i, tau i : FiniteMeasure (E × E)) :
          Measure (E × E)) := by
    rw [FiniteMeasure.toMeasure_sum]
    apply integrable_finsetSum_measure.2
    intro i _hi
    exact hTauIntegrable i
  have hAddedIntegrable :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (added : Measure (E × E)) := by
    dsimp only [added]
    rw [FiniteMeasure.toMeasure_smul]
    exact hTauSumIntegrable.smul_measure_nnreal
  have hRemovedIntegrable :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (removed : Measure (E × E)) :=
    hGammaIntegrable.mono_measure hRemovedLe
  have hRemainderIntegrable :
      Integrable (fun z : E × E => dist (q z.1) (q z.2))
        (remainder : Measure (E × E)) :=
    hGammaIntegrable.mono_measure hRemainderLe
  have hTauSumIntegral :
      (∫ z, dist (q z.1) (q z.2)
          ∂((∑ i, tau i : FiniteMeasure (E × E)) :
            Measure (E × E))) =
        ∑ i, ∫ z, dist (q z.1) (q z.2)
          ∂(tau i : Measure (E × E)) := by
    rw [FiniteMeasure.toMeasure_sum]
    exact integral_finsetSum_measure fun i _hi => hTauIntegrable i
  have hRhoSumIntegral :
      (∫ z, dist (q z.1) (q z.2)
          ∂((∑ i, rho i : FiniteMeasure (E × E)) :
            Measure (E × E))) =
        ∑ i, ∫ z, dist (q z.1) (q z.2)
          ∂(rho i : Measure (E × E)) := by
    rw [FiniteMeasure.toMeasure_sum]
    exact integral_finsetSum_measure fun i _hi => hRhoIntegrable i
  have hScaledCheaper :
      (∫ z, dist (q z.1) (q z.2)
          ∂(added : Measure (E × E))) <
        ∫ z, dist (q z.1) (q z.2)
          ∂(removed : Measure (E × E)) := by
    dsimp only [added, removed]
    rw [FiniteMeasure.toMeasure_smul,
      FiniteMeasure.toMeasure_smul,
      integral_smul_nnreal_measure,
      integral_smul_nnreal_measure,
      hTauSumIntegral, hRhoSumIntegral]
    simpa only [NNReal.smul_def] using
      mul_lt_mul_of_pos_left hBaseCheaper
        (by exact_mod_cast hCPos : (0 : Real) < c)
  have hEtaCheaper :
      (∫ z, dist (q z.1) (q z.2)
          ∂(eta.plan : Measure (E × E))) <
        ∫ z, dist (q z.1) (q z.2)
          ∂(gamma.plan : Measure (E × E)) := by
    change
      (∫ z, dist (q z.1) (q z.2)
          ∂((remainder + added : FiniteMeasure (E × E)) :
            Measure (E × E))) <
        ∫ z, dist (q z.1) (q z.2)
          ∂(gamma.plan : Measure (E × E))
    rw [← hDecomposition, FiniteMeasure.toMeasure_add,
      FiniteMeasure.toMeasure_add,
      integral_add_measure hRemainderIntegrable hAddedIntegrable,
      integral_add_measure hRemainderIntegrable hRemovedIntegrable]
    simpa [add_comm] using
      add_lt_add_right hScaledCheaper
        (∫ z, dist (q z.1) (q z.2)
          ∂(remainder : Measure (E × E)))
  exact (not_lt_of_ge (hMinimal eta)) hEtaCheaper

/-- A power-cost minimizer has a topological support that is cyclically
monotone after the Euclidean metric is snowflaked by its power exponent. -/
theorem powerMinimizerSupport_snowflakeCyclic
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain)
    (gamma : FiniteCoupling mu nu)
    (hGamma : IsProfileMinimizer (powerProfile epsilon) gamma) :
    let p : Real := 1 - epsilon
    let hp0 : 0 < p := by
      dsimp only [p]
      linarith [hEpsilon.2]
    let hp1 : p <= 1 := by
      dsimp only [p]
      linarith [hEpsilon.1]
    let S := Metric.Snowflaking (Euclidean n) p hp0 hp1
    IsDistanceCyclicallyMonotone
      {z : S × S |
        (z.1.ofSnowflaking, z.2.ofSnowflaking) ∈
          Measure.support
            (gamma.plan :
              Measure (Euclidean n × Euclidean n))} := by
  dsimp only
  let p : Real := 1 - epsilon
  have hp0 : 0 < p := by
    dsimp only [p]
    linarith [hEpsilon.2]
  have hp1 : p <= 1 := by
    dsimp only [p]
    linarith [hEpsilon.1]
  let S := Metric.Snowflaking (Euclidean n) p hp0 hp1
  let q : Euclidean n -> S :=
    Metric.Snowflaking.toSnowflaking
  have hq : Continuous q :=
    Metric.Snowflaking.continuous_toSnowflaking
  have hCostEq (z : Euclidean n × Euclidean n) :
      dist (q z.1) (q z.2) =
        powerProfile epsilon ‖z.1 - z.2‖ := by
    simp [q, S, p, powerProfile, dist_eq_norm]
  have hCostMeasurable :
      Measurable
        (fun z : Euclidean n × Euclidean n =>
          dist (q z.1) (q z.2)) :=
    ((hq.comp continuous_fst).dist
      (hq.comp continuous_snd)).measurable
  have hGammaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          dist (q z.1) (q z.2))
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)) := by
    simpa only [hCostEq] using
      powerProfileCostIntegrableOfMarginalLogMoments
        hPower.sourceLogMoment hPower.targetLogMoment gamma hEpsilon
  have hMinimal :
      ∀ eta : FiniteCoupling mu nu,
        (∫ z, dist (q z.1) (q z.2)
            ∂(gamma.plan :
              Measure (Euclidean n × Euclidean n))) <=
          ∫ z, dist (q z.1) (q z.2)
            ∂(eta.plan :
              Measure (Euclidean n × Euclidean n)) := by
    intro eta
    simpa only [hCostEq, profileCost] using
      hGamma.2 eta (mem_univ eta)
  intro I _ x y hxy sigma
  have hOriginalSupport (i : I) :
      ((x i).ofSnowflaking, (y i).ofSnowflaking) ∈
        Measure.support
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)) :=
    hxy i
  have hCycle :=
    pulledMetric_minimizerSupportCyclic
      q hq hCostMeasurable gamma hGammaIntegrable hMinimal
      (I := I)
      (fun i => (x i).ofSnowflaking)
      (fun i => (y i).ofSnowflaking)
      hOriginalSupport sigma
  simpa only [q, S,
    Metric.Snowflaking.toSnowflaking_ofSnowflaking] using hCycle

/-- The snowflake cyclic support of a power minimizer is contained in the
contact set of a global snowflake-Lipschitz potential. -/
private theorem exists_powerContactPotential
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain)
    (gamma : FiniteCoupling mu nu)
    (hGamma : IsProfileMinimizer (powerProfile epsilon) gamma) :
    let p : Real := 1 - epsilon
    ∃ u : Euclidean n -> Real,
      (∀ x y, dist (u x) (u y) <= dist x y ^ p) ∧
      ∀ z ∈ Measure.support
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)),
        dist z.1 z.2 ^ p = u z.1 - u z.2 := by
  dsimp only
  let p : Real := 1 - epsilon
  have hp0 : 0 < p := by
    dsimp only [p]
    linarith [hEpsilon.2]
  have hp1 : p <= 1 := by
    dsimp only [p]
    linarith [hEpsilon.1]
  let S := Metric.Snowflaking (Euclidean n) p hp0 hp1
  let q : Euclidean n -> S :=
    Metric.Snowflaking.toSnowflaking
  let GammaS : Set (S × S) :=
    {z |
      (z.1.ofSnowflaking, z.2.ofSnowflaking) ∈
        Measure.support
          (gamma.plan :
            Measure (Euclidean n × Euclidean n))}
  have hCyclic : IsDistanceCyclicallyMonotone GammaS := by
    intro I _ x y hxy sigma
    exact
      (powerMinimizerSupport_snowflakeCyclic
        n mu nu hPower hEpsilon gamma hGamma)
        x y hxy sigma
  obtain ⟨v, hvLipschitz, hvContact⟩ :=
    existsDistanceContactPotential_of_isDistanceCyclicallyMonotone
      (q 0) GammaS hCyclic
  let u : Euclidean n -> Real := fun x => v (q x)
  refine ⟨u, ?_, ?_⟩
  · intro x y
    have hDist := hvLipschitz.dist_le_mul (q x) (q y)
    simpa only [u, q, S, NNReal.coe_one, one_mul,
      Metric.Snowflaking.dist_toSnowflaking_toSnowflaking] using hDist
  · intro z hz
    have hLifted : (q z.1, q z.2) ∈ GammaS := by
      simpa only [GammaS, q, S,
        Metric.Snowflaking.ofSnowflaking_toSnowflaking] using hz
    have hContact := hvContact hLifted
    simpa only [distanceContactSet, mem_setOf_eq, u, q, S,
      Metric.Snowflaking.dist_toSnowflaking_toSnowflaking] using hContact

private theorem dist_rpow_sub_dist_rpow_le_of_separated
    {E : Type*} [PseudoMetricSpace E]
    {p r : Real} (hp0 : 0 < p) (hp1 : p <= 1) (hr : 0 < r)
    {a x x' y : E}
    (hx : x ∈ Metric.closedBall a r)
    (hx' : x' ∈ Metric.closedBall a r)
    (hy : y ∉ Metric.ball a (2 * r)) :
    |dist x y ^ p - dist x' y ^ p| <=
      r ^ (p - 1) * dist x x' := by
  have hxy : r <= dist x y := by
    have hNot : ¬dist a y < 2 * r := by
      simpa only [Metric.mem_ball, dist_comm] using hy
    have hay : 2 * r <= dist a y := le_of_not_gt hNot
    have hax : dist a x <= r := by
      simpa only [Metric.mem_closedBall, dist_comm] using hx
    linarith [dist_triangle a x y]
  have hx'y : r <= dist x' y := by
    have hNot : ¬dist a y < 2 * r := by
      simpa only [Metric.mem_ball, dist_comm] using hy
    have hay : 2 * r <= dist a y := le_of_not_gt hNot
    have hax' : dist a x' <= r := by
      simpa only [Metric.mem_closedBall, dist_comm] using hx'
    linarith [dist_triangle a x' y]
  have hpSub : p - 1 <= 0 := sub_nonpos.mpr hp1
  have hDerivative
      (t : Real) (ht : t ∈ Ici r) :
      ‖deriv (fun s : Real => s ^ p) t‖ <= r ^ (p - 1) := by
    have htPos : 0 < t := hr.trans_le ht
    rw [Real.deriv_rpow_const]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hp0.le (Real.rpow_nonneg htPos.le _))]
    calc
      p * t ^ (p - 1) <= 1 * t ^ (p - 1) := by
        exact
          mul_le_mul_of_nonneg_right hp1
            (Real.rpow_nonneg htPos.le _)
      _ <= 1 * r ^ (p - 1) := by
        simpa only [one_mul] using
          Real.rpow_le_rpow_of_nonpos hr ht hpSub
      _ = r ^ (p - 1) := one_mul _
  have hMean :=
    (convex_Ici r).norm_image_sub_le_of_norm_deriv_le
      (f := fun t : Real => t ^ p)
      (fun t ht =>
        (Real.hasDerivAt_rpow_const
          (Or.inl (ne_of_gt (hr.trans_le ht)))).differentiableAt)
      hDerivative hxy hx'y
  calc
    |dist x y ^ p - dist x' y ^ p| =
        ‖dist x' y ^ p - dist x y ^ p‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
    _ <= r ^ (p - 1) * ‖dist x' y - dist x y‖ := hMean
    _ <= r ^ (p - 1) * dist x x' := by
      gcongr
      simpa only [Real.norm_eq_abs, abs_sub_comm] using
        abs_dist_sub_le x x' y

private def powerContactEnvelope
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) (p : Real) (target : Set E) (x : E) : Real :=
  sInf ((fun y : E => u y + dist x y ^ p) '' target)

private theorem powerContactEnvelope_bddBelow
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) {p : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    {target : Set E} (hTarget : target.Nonempty) (x : E) :
    BddBelow ((fun y : E => u y + dist x y ^ p) '' target) := by
  refine ⟨u x, ?_⟩
  rintro _ ⟨y, _hy, rfl⟩
  have hDifference :
      u x - u y <= dist x y ^ p := by
    calc
      u x - u y <= |u x - u y| := le_abs_self _
      _ = dist (u x) (u y) := by rw [Real.dist_eq]
      _ <= dist x y ^ p := hu x y
  linarith

private theorem powerContactEnvelope_eq_of_contact
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) {p : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    {target : Set E} {x y : E} (hy : y ∈ target)
    (hContact : dist x y ^ p = u x - u y) :
    powerContactEnvelope u p target x = u x := by
  have hTarget : target.Nonempty := ⟨y, hy⟩
  apply le_antisymm
  · unfold powerContactEnvelope
    have hBdd :=
      powerContactEnvelope_bddBelow u hu hTarget x
    have hMember :
        u y + dist x y ^ p ∈
          (fun z : E => u z + dist x z ^ p) '' target :=
      ⟨y, hy, rfl⟩
    calc
      sInf ((fun z : E => u z + dist x z ^ p) '' target) <=
          u y + dist x y ^ p := csInf_le hBdd hMember
      _ = u x := by linarith
  · unfold powerContactEnvelope
    apply le_csInf (hTarget.image _)
    rintro _ ⟨z, _hz, rfl⟩
    have hDifference :
        u x - u z <= dist x z ^ p := by
      calc
        u x - u z <= |u x - u z| := le_abs_self _
        _ = dist (u x) (u z) := by rw [Real.dist_eq]
        _ <= dist x z ^ p := hu x z
    linarith

private theorem powerContactEnvelope_lipschitzOn_closedBall
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) {p r : Real}
    (hp0 : 0 < p) (hp1 : p <= 1) (hr : 0 < r)
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    (a : E) :
    let K : NNReal :=
      ⟨r ^ (p - 1), Real.rpow_nonneg hr.le _⟩
    LipschitzOnWith K
      (powerContactEnvelope u p (Metric.ball a (2 * r))ᶜ)
      (Metric.closedBall a r) := by
  dsimp only
  let target : Set E := (Metric.ball a (2 * r))ᶜ
  let K : NNReal :=
    ⟨r ^ (p - 1), Real.rpow_nonneg hr.le _⟩
  change LipschitzOnWith K
    (powerContactEnvelope u p target) (Metric.closedBall a r)
  by_cases hTarget : target.Nonempty
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx x' hx'
    have hBdd (z : E) :
        BddBelow
          ((fun y : E => u y + dist z y ^ p) '' target) :=
      powerContactEnvelope_bddBelow u hu hTarget z
    have hCost (y : E) (hy : y ∈ target) :
        |dist x y ^ p - dist x' y ^ p| <=
          r ^ (p - 1) * dist x x' := by
      apply
        dist_rpow_sub_dist_rpow_le_of_separated
          hp0 hp1 hr hx hx'
      exact hy
    have hForward :
        powerContactEnvelope u p target x <=
          powerContactEnvelope u p target x' +
            r ^ (p - 1) * dist x x' := by
      have hLower :
          powerContactEnvelope u p target x -
                r ^ (p - 1) * dist x x' <=
            powerContactEnvelope u p target x' := by
        unfold powerContactEnvelope
        apply le_csInf (hTarget.image _)
        rintro _ ⟨y, hy, rfl⟩
        have hInfLe :
            sInf ((fun z : E => u z + dist x z ^ p) '' target) <=
              u y + dist x y ^ p :=
          csInf_le (hBdd x) ⟨y, hy, rfl⟩
        have hPowerLe :
            dist x y ^ p <=
              dist x' y ^ p + r ^ (p - 1) * dist x x' :=
          by
            linarith only [(abs_le.mp (hCost y hy)).2]
        linarith
      linarith
    have hBackward :
        powerContactEnvelope u p target x' <=
          powerContactEnvelope u p target x +
            r ^ (p - 1) * dist x x' := by
      have hLower :
          powerContactEnvelope u p target x' -
                r ^ (p - 1) * dist x x' <=
            powerContactEnvelope u p target x := by
        unfold powerContactEnvelope
        apply le_csInf (hTarget.image _)
        rintro _ ⟨y, hy, rfl⟩
        have hInfLe :
            sInf ((fun z : E => u z + dist x' z ^ p) '' target) <=
              u y + dist x' y ^ p :=
          csInf_le (hBdd x') ⟨y, hy, rfl⟩
        have hPowerLe :
            dist x' y ^ p <=
              dist x y ^ p + r ^ (p - 1) * dist x x' := by
          have hAbs := hCost y hy
          rw [abs_sub_comm] at hAbs
          linarith only [(abs_le.mp hAbs).2]
        linarith
      linarith
    change
      |powerContactEnvelope u p target x -
          powerContactEnvelope u p target x'| <=
        r ^ (p - 1) * dist x x'
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hTargetEmpty : target = ∅ := not_nonempty_iff_eq_empty.mp hTarget
    rw [hTargetEmpty]
    have hZero :
        powerContactEnvelope u p (∅ : Set E) = fun _ => 0 := by
      funext z
      simp [powerContactEnvelope]
    rw [hZero]
    exact
      (LipschitzWith.const' (α := E) (0 : Real)
        (K := K)).lipschitzOnWith

private theorem powerContactEnvelope_le_cost
    {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) {p : Real}
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p)
    {target : Set E} {y : E} (hy : y ∈ target) (x : E) :
    powerContactEnvelope u p target x <= u y + dist x y ^ p := by
  unfold powerContactEnvelope
  exact
    csInf_le
      (powerContactEnvelope_bddBelow u hu ⟨y, hy⟩ x)
      ⟨y, hy, rfl⟩

private theorem powerContact_target_unique_ae
    (n : Nat) (u : Euclidean n -> Real) {p : Real}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : ∀ x y, dist (u x) (u y) <= dist x y ^ p) :
    ∀ᵐ x ∂(volume : Measure (Euclidean n)),
      ∀ y y',
        x ≠ y ->
        x ≠ y' ->
        dist x y ^ p = u x - u y ->
        dist x y' ^ p = u x - u y' ->
        y = y' := by
  let E := Euclidean n
  obtain ⟨D, hDCount, hDDense⟩ :
      ∃ D : Set E, D.Countable ∧ Dense D :=
    TopologicalSpace.exists_countable_dense E
  letI : Countable D := hDCount
  let radius : Nat -> Real :=
    fun k => 1 / (k + 1 : Real)
  have hRadius (k : Nat) : 0 < radius k := by
    dsimp only [radius]
    positivity
  let lipConstant : Nat -> NNReal :=
    fun k =>
      ⟨radius k ^ (p - 1),
        Real.rpow_nonneg (hRadius k).le _⟩
  have hEnvelopeLipschitz (a : D) (k : Nat) :
      LipschitzOnWith (lipConstant k)
        (powerContactEnvelope u p
          (Metric.ball (a : E) (2 * radius k))ᶜ)
        (Metric.closedBall (a : E) (radius k)) := by
    simpa only [lipConstant] using
      powerContactEnvelope_lipschitzOn_closedBall
        u hp0 hp1.le (hRadius k) hu (a : E)
  let extension : D -> Nat -> E -> Real :=
    fun a k =>
      Classical.choose (hEnvelopeLipschitz a k).extend_real
  have hExtensionLipschitz (a : D) (k : Nat) :
      LipschitzWith (lipConstant k) (extension a k) :=
    (Classical.choose_spec
      (hEnvelopeLipschitz a k).extend_real).1
  have hExtensionEq (a : D) (k : Nat) :
      EqOn
        (powerContactEnvelope u p
          (Metric.ball (a : E) (2 * radius k))ᶜ)
        (extension a k)
        (Metric.closedBall (a : E) (radius k)) :=
    (Classical.choose_spec
      (hEnvelopeLipschitz a k).extend_real).2
  have hDifferentiable :
      ∀ᵐ x ∂(volume : Measure E),
        ∀ a : D, ∀ k : Nat,
          DifferentiableAt Real (extension a k) x := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro k
    exact (hExtensionLipschitz a k).ae_differentiableAt
  filter_upwards [hDifferentiable] with x hx
  intro y y' hxy hxy' hContact hContact'
  let delta : Real := min (dist x y) (dist x y')
  have hDelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (dist_pos.mpr hxy) (dist_pos.mpr hxy')
  obtain ⟨k, hk⟩ :=
    exists_nat_one_div_lt (show 0 < delta / 4 by positivity)
  let r : Real := radius k
  have hr : 0 < r := hRadius k
  have hrDelta : r < delta / 4 := by
    simpa only [r, radius] using hk
  obtain ⟨a, haD, hxa⟩ :=
    hDDense.exists_dist_lt x hr
  let aD : D := ⟨a, haD⟩
  have hxBall : x ∈ Metric.ball (aD : E) r := by
    simpa only [Metric.mem_ball, aD] using hxa
  have hxClosed : x ∈ Metric.closedBall (aD : E) r :=
    Metric.ball_subset_closedBall hxBall
  have hyTarget :
      y ∈ (Metric.ball (aD : E) (2 * r))ᶜ := by
    intro hyBall
    have hay : dist (aD : E) y < 2 * r := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hyBall
    have hdeltaY : delta <= dist x y := min_le_left _ _
    have hxyUpper :
        dist x y < 3 * r := by
      calc
        dist x y <= dist x (aD : E) + dist (aD : E) y :=
          dist_triangle _ _ _
        _ < r + 2 * r := add_lt_add hxa hay
        _ = 3 * r := by ring
    linarith
  have hyTarget' :
      y' ∈ (Metric.ball (aD : E) (2 * r))ᶜ := by
    intro hyBall
    have hay : dist (aD : E) y' < 2 * r := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hyBall
    have hdeltaY : delta <= dist x y' := min_le_right _ _
    have hxyUpper :
        dist x y' < 3 * r := by
      calc
        dist x y' <= dist x (aD : E) + dist (aD : E) y' :=
          dist_triangle _ _ _
        _ < r + 2 * r := add_lt_add hxa hay
        _ = 3 * r := by ring
    linarith
  have hClosedNhds :
      Metric.closedBall (aD : E) r ∈ nhds x :=
    Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds hxBall)
      Metric.ball_subset_closedBall
  have hExtensionEventually :
      extension aD k =ᶠ[nhds x]
        powerContactEnvelope u p
          (Metric.ball (aD : E) (2 * r))ᶜ := by
    filter_upwards [hClosedNhds] with z hz
    have hEq := hExtensionEq aD k hz
    simpa only [r] using hEq.symm
  let target : Set E :=
    (Metric.ball (aD : E) (2 * r))ᶜ
  let envelope : E -> Real :=
    powerContactEnvelope u p target
  have hEnvelopeDifferentiable :
      DifferentiableAt Real envelope x := by
    exact hExtensionEventually.differentiableAt_iff.mp (hx aD k)
  apply
    powerUpperTouches_target_unique_of_differentiableAt
      (v := envelope) (c := u y) (c' := u y')
      hp0 hp1 hEnvelopeDifferentiable hxy hxy'
  · intro z
    simpa only [envelope, target, add_comm] using
      powerContactEnvelope_le_cost u hu hyTarget z
  · have hEnvelopeContact :=
      powerContactEnvelope_eq_of_contact u hu hyTarget hContact
    dsimp only [envelope, target]
    linarith
  · intro z
    simpa only [envelope, target, add_comm] using
      powerContactEnvelope_le_cost u hu hyTarget' z
  · have hEnvelopeContact :=
      powerContactEnvelope_eq_of_contact u hu hyTarget' hContact'
    dsimp only [envelope, target]
    linarith

/-- Every minimizer of an admissible power profile is induced by a
measurable transport map. -/
theorem powerProfileMinimizer_isGraphPlan
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain)
    (gamma : FiniteCoupling mu nu)
    (hGamma : IsProfileMinimizer (powerProfile epsilon) gamma) :
    ∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T := by
  let p : Real := 1 - epsilon
  have hp0 : 0 < p := by
    dsimp only [p]
    linarith [hEpsilon.2]
  have hp1 : p < 1 := by
    dsimp only [p]
    linarith [hEpsilon.1]
  obtain ⟨u, hu, hContact⟩ :=
    exists_powerContactPotential
      n mu nu hPower hEpsilon gamma hGamma
  let Gamma : Set (Euclidean n × Euclidean n) :=
    Measure.support
        (gamma.plan :
          Measure (Euclidean n × Euclidean n)) \
      {z | z.1 = z.2}
  have hSupported : IsSupported gamma Gamma := by
    filter_upwards
      [Measure.support_mem_ae,
        finiteCouplingAvoidsDiagonalOfMutuallySingular
          gamma hPower.mutuallySingular] with z hzSupport hzNe
    exact ⟨hzSupport, hzNe⟩
  have hUniqueVolume :
      ∀ᵐ x ∂(volume : Measure (Euclidean n)),
        ∀ y y',
          (x, y) ∈ Gamma ->
          (x, y') ∈ Gamma ->
          y = y' := by
    filter_upwards
      [powerContact_target_unique_ae
        n u hp0 hp1 hu] with x hx
    intro y y' hy hy'
    apply hx y y'
    · exact hy.2
    · exact hy'.2
    · exact hContact (x, y) hy.1
    · exact hContact (x, y') hy'.1
  have hUniqueSource :
      ∀ᵐ x ∂(mu : Measure (Euclidean n)),
        ∀ y y',
          (x, y) ∈ Gamma ->
          (x, y') ∈ Gamma ->
          y = y' :=
    hPower.sourceAbsolutelyContinuous.ae_le hUniqueVolume
  exact
    existsGraphPlanOfSupportedSourceAeUniqueFiber_polish
      gamma Gamma hSupported hUniqueSource

/-- The exact graphness premise used by the power optimizer-family producer. -/
theorem powerProfile_all_minimizers_graph
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    ∀ epsilon, epsilon ∈ epsilonDomain ->
      ∀ gamma : FiniteCoupling mu nu,
        IsProfileMinimizer (powerProfile epsilon) gamma ->
          ∃ T : Euclidean n -> Euclidean n,
            IsGraphPlan gamma T := by
  intro epsilon hEpsilon gamma hGamma
  exact
    powerProfileMinimizer_isGraphPlan
      n mu nu hPower hEpsilon gamma hGamma

/-- Under the paper's power-marginal hypotheses, exact graph-induced power
optimizers can be chosen simultaneously for all profile parameters. -/
theorem nonempty_powerOptimizerFamily
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    Nonempty (OptimizerFamily mu nu powerProfile) := by
  exact
    nonempty_powerOptimizerFamily_of_graph_minimizers
      n mu nu hPower
      (powerProfile_all_minimizers_graph n mu nu hPower)

end ConcaveOTLimit
