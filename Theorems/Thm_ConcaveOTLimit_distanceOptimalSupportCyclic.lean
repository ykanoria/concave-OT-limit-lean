import Theorems.Thm_ConcaveOTLimit_distanceContactCharacterization
import Theorems.Thm_ConcaveOTLimit_profileCostReroutingLtOfAddedLtRemoved
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ConcaveOTLimit

private theorem firstMarginal_mass_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (firstMarginal rho).mass = rho.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass]
  exact FiniteMeasure.map_apply rho measurable_fst MeasurableSet.univ
    |>.trans (by simp)

private theorem secondMarginal_mass_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure (X × Y)) :
    (secondMarginal rho).mass = rho.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass]
  exact FiniteMeasure.map_apply rho measurable_snd MeasurableSet.univ
    |>.trans (by simp)

private theorem firstMarginal_crossProduct
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
  rw [secondMarginal_mass_eq]

private theorem secondMarginal_crossProduct
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
  rw [firstMarginal_mass_eq]

private theorem firstMarginal_fintypeSum
    {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (rho : I -> FiniteMeasure (X × Y)) :
    firstMarginal (∑ i, rho i) = ∑ i, firstMarginal (rho i) := by
  apply FiniteMeasure.toMeasure_injective
  simp only [firstMarginal, FiniteMeasure.toMeasure_map,
    FiniteMeasure.toMeasure_sum]
  change
    Measure.map Prod.fst
        (∑ i, (rho i : Measure (X × Y))) =
      ∑ i, Measure.map Prod.fst (rho i : Measure (X × Y))
  exact Measure.map_finset_sum' measurable_fst.aemeasurable

private theorem secondMarginal_fintypeSum
    {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (rho : I -> FiniteMeasure (X × Y)) :
    secondMarginal (∑ i, rho i) = ∑ i, secondMarginal (rho i) := by
  apply FiniteMeasure.toMeasure_injective
  simp only [secondMarginal, FiniteMeasure.toMeasure_map,
    FiniteMeasure.toMeasure_sum]
  change
    Measure.map Prod.snd
        (∑ i, (rho i : Measure (X × Y))) =
      ∑ i, Measure.map Prod.snd (rho i : Measure (X × Y))
  exact Measure.map_finset_sum' measurable_snd.aemeasurable

private theorem firstMarginal_smul
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : NNReal) (rho : FiniteMeasure (X × Y)) :
    firstMarginal (c • rho) = c • firstMarginal rho := by
  unfold firstMarginal
  exact FiniteMeasure.map_smul c rho

private theorem secondMarginal_smul
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : NNReal) (rho : FiniteMeasure (X × Y)) :
    secondMarginal (c • rho) = c • secondMarginal rho := by
  unfold secondMarginal
  exact FiniteMeasure.map_smul c rho

private theorem normalizedRestriction_mass
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) (_hRho : rho ≠ 0) :
    rho.normalize.toFiniteMeasure.mass = 1 :=
  ProbabilityMeasure.mass_toFiniteMeasure rho.normalize

private theorem normalizedRestriction_mem_ae
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) (s : Set Omega)
    (hs : MeasurableSet s) (hRho : rho.restrict s ≠ 0) :
    ∀ᵐ z ∂((rho.restrict s).normalize.toFiniteMeasure :
      Measure Omega), z ∈ s := by
  rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero _ hRho,
    FiniteMeasure.toMeasure_smul]
  exact Measure.ae_smul_measure (ae_restrict_mem hs) _

private theorem integralDistance_mem_prod_ball_bounds
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (rho : FiniteMeasure (E × E)) (x y : E) (r : Real)
    (hMass : rho.mass = 1)
    (hSupported :
      ∀ᵐ z ∂(rho : Measure (E × E)),
        z.1 ∈ Metric.ball x r ∧ z.2 ∈ Metric.ball y r)
    (hIntegrable :
      Integrable (fun z : E × E => dist z.1 z.2)
        (rho : Measure (E × E))) :
    dist x y - 2 * r <=
        ∫ z, dist z.1 z.2 ∂(rho : Measure (E × E)) ∧
      (∫ z, dist z.1 z.2 ∂(rho : Measure (E × E))) <=
        dist x y + 2 * r := by
  have hConstantIntegral (c : Real) :
      (∫ _z : E × E, c ∂(rho : Measure (E × E))) = c := by
    rw [integral_const]
    simp only [FiniteMeasure.measureReal_eq_coe_coeFn, smul_eq_mul]
    change (rho.mass : Real) * c = c
    rw [hMass]
    simp
  have hLower :
      (fun _z : E × E => dist x y - 2 * r) ≤ᵐ[
          (rho : Measure (E × E))]
        (fun z => dist z.1 z.2) := by
    filter_upwards [hSupported] with z hz
    have hxBall : dist z.1 x < r := Metric.mem_ball.mp hz.1
    have hy : dist z.2 y < r := Metric.mem_ball.mp hz.2
    have hx : dist x z.1 < r := by
      simpa [dist_comm] using hxBall
    have hTriangle :
        dist x y <=
          dist x z.1 + dist z.1 z.2 + dist z.2 y := by
      calc
        dist x y <= dist x z.1 + dist z.1 y :=
          dist_triangle _ _ _
        _ <= dist x z.1 +
            (dist z.1 z.2 + dist z.2 y) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    linarith
  have hUpper :
      (fun z : E × E => dist z.1 z.2) ≤ᵐ[
          (rho : Measure (E × E))]
        (fun _z => dist x y + 2 * r) := by
    filter_upwards [hSupported] with z hz
    have hx : dist z.1 x < r := Metric.mem_ball.mp hz.1
    have hyBall : dist z.2 y < r := Metric.mem_ball.mp hz.2
    have hy : dist y z.2 < r := by
      simpa [dist_comm] using hyBall
    have hTriangle :
        dist z.1 z.2 <=
          dist z.1 x + dist x y + dist y z.2 := by
      calc
        dist z.1 z.2 <= dist z.1 x + dist x z.2 :=
          dist_triangle _ _ _
        _ <= dist z.1 x +
            (dist x y + dist y z.2) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    linarith
  constructor
  · calc
      dist x y - 2 * r =
          ∫ _z : E × E, dist x y - 2 * r
            ∂(rho : Measure (E × E)) :=
        (hConstantIntegral _).symm
      _ <= ∫ z, dist z.1 z.2
          ∂(rho : Measure (E × E)) :=
        integral_mono_ae (integrable_const _) hIntegrable hLower
  · calc
      (∫ z, dist z.1 z.2 ∂(rho : Measure (E × E))) <=
          ∫ _z : E × E, dist x y + 2 * r
            ∂(rho : Measure (E × E)) :=
        integral_mono_ae hIntegrable (integrable_const _) hUpper
      _ = dist x y + 2 * r := hConstantIntegral _

private theorem integrableDistance_of_mem_prod_ball
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    [BorelSpace E] [OpensMeasurableSpace (E × E)]
    (rho : FiniteMeasure (E × E)) (x y : E) (r : Real)
    (hSupported :
      ∀ᵐ z ∂(rho : Measure (E × E)),
        z.1 ∈ Metric.ball x r ∧ z.2 ∈ Metric.ball y r) :
    Integrable (fun z : E × E => dist z.1 z.2)
      (rho : Measure (E × E)) := by
  have hDom :
      Integrable (fun _z : E × E => dist x y + 2 * |r|)
        (rho : Measure (E × E)) :=
    integrable_const _
  refine hDom.mono'
    (continuous_dist.comp
      (continuous_fst.prodMk continuous_snd)).aestronglyMeasurable ?_
  filter_upwards [hSupported] with z hz
  have hx : dist z.1 x < r := Metric.mem_ball.mp hz.1
  have hyBall : dist z.2 y < r := Metric.mem_ball.mp hz.2
  have hy : dist y z.2 < r := by
    simpa [dist_comm] using hyBall
  have hTriangle :
      dist z.1 z.2 <=
        dist z.1 x + dist x y + dist y z.2 := by
    calc
      dist z.1 z.2 <= dist z.1 x + dist x z.2 :=
        dist_triangle _ _ _
      _ <= dist z.1 x + (dist x y + dist y z.2) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  have hr : r <= |r| := le_abs_self r
  linarith

/-- The topological support of a distance-optimal finite coupling is
distance-cyclically monotone. -/
theorem distanceOptimalSupportCyclicallyMonotone
    (n : Nat)
    {mu nu : FiniteMeasure (Euclidean n)}
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (gamma : FiniteCoupling mu nu)
    (hOptimal : IsDistanceOptimal gamma) :
    IsDistanceCyclicallyMonotone
      (Measure.support
        (gamma.plan :
          Measure (Euclidean n × Euclidean n))) := by
  classical
  intro I _ x y hSupport sigma
  cases isEmpty_or_nonempty I with
  | inl hEmpty =>
      letI := hEmpty
      simp
  | inr hNonempty =>
      letI := hNonempty
      by_contra hCycle
      let directCenter : Real :=
        ∑ i, dist (x i) (y i)
      let crossedCenter : Real :=
        ∑ i, dist (x i) (y (sigma i))
      have hCenterStrict : crossedCenter < directCenter := by
        exact lt_of_not_ge hCycle
      let cardReal : Real := Fintype.card I
      have hCardReal : 0 < cardReal := by
        dsimp only [cardReal]
        exact_mod_cast Fintype.card_pos
      let r : Real :=
        (directCenter - crossedCenter) / (8 * cardReal)
      have hr : 0 < r := by
        dsimp only [r]
        positivity
      have hrSmall :
          4 * cardReal * r <
            directCenter - crossedCenter := by
        have hCardRealNe : cardReal ≠ 0 := ne_of_gt hCardReal
        calc
          4 * cardReal * r =
              (directCenter - crossedCenter) / 2 := by
            dsimp only [r]
            field_simp
            ring
          _ < directCenter - crossedCenter := by
            linarith
      let U : I -> Set (Euclidean n × Euclidean n) :=
        fun i => Metric.ball (x i) r ×ˢ Metric.ball (y i) r
      have hUOpen (i : I) : IsOpen (U i) := by
        exact Metric.isOpen_ball.prod Metric.isOpen_ball
      have hUMeasurable (i : I) : MeasurableSet (U i) :=
        (hUOpen i).measurableSet
      have hPointMem (i : I) : (x i, y i) ∈ U i := by
        exact ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
      let tau : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
        fun i => gamma.plan.restrict (U i)
      have hTauMassPositive (i : I) : 0 < (tau i).mass := by
        have hMeasurePositive :
            0 <
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) (U i) :=
          (Measure.mem_support_iff_forall (x i, y i)).mp
            (hSupport i) (U i)
            ((hUOpen i).mem_nhds (hPointMem i))
        have hPlanPositive : 0 < gamma.plan (U i) := by
          apply pos_iff_ne_zero.mpr
          intro hZero
          have hMeasureZero :
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) (U i) = 0 :=
            (FiniteMeasure.null_iff_toMeasure_null gamma.plan (U i)).mp
              hZero
          exact hMeasurePositive.ne' hMeasureZero
        simpa only [tau, FiniteMeasure.restrict_mass] using
          hPlanPositive
      have hTauNonzero (i : I) : tau i ≠ 0 :=
        (FiniteMeasure.mass_nonzero_iff (tau i)).mp
          (hTauMassPositive i).ne'
      let rho : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
        fun i => (tau i).normalize.toFiniteMeasure
      have hRhoMass (i : I) : (rho i).mass = 1 := by
        exact normalizedRestriction_mass (tau i) (hTauNonzero i)
      have hRhoSupported (i : I) :
          ∀ᵐ z ∂(rho i :
            Measure (Euclidean n × Euclidean n)),
            z.1 ∈ Metric.ball (x i) r ∧
              z.2 ∈ Metric.ball (y i) r := by
        simpa only [rho, tau, U] using
          normalizedRestriction_mem_ae gamma.plan (U i)
            (hUMeasurable i) (hTauNonzero i)
      let crossed :
          I -> FiniteMeasure (Euclidean n × Euclidean n) :=
        fun i =>
          (firstMarginal (rho i)).prod
            (secondMarginal (rho (sigma i)))
      have hCrossedMass (i : I) : (crossed i).mass = 1 := by
        calc
          (crossed i).mass =
              (firstMarginal (crossed i)).mass :=
            (firstMarginal_mass_eq (crossed i)).symm
          _ =
              (firstMarginal (rho i)).mass := by
            rw [firstMarginal_crossProduct, hRhoMass]
            simp
          _ = (rho i).mass := firstMarginal_mass_eq (rho i)
          _ = 1 := hRhoMass i
      have hFirstSupported (i : I) :
          ∀ᵐ a ∂(firstMarginal (rho i) :
            Measure (Euclidean n)),
            a ∈ Metric.ball (x i) r := by
        change
          ∀ᵐ a ∂Measure.map Prod.fst
            (rho i : Measure (Euclidean n × Euclidean n)),
            a ∈ Metric.ball (x i) r
        apply
          (ae_map_iff (p := fun a => a ∈ Metric.ball (x i) r)
            measurable_fst.aemeasurable
            Metric.isOpen_ball.measurableSet).2
        filter_upwards [hRhoSupported i] with z hz
        exact hz.1
      have hSecondSupported (i : I) :
          ∀ᵐ b ∂(secondMarginal (rho (sigma i)) :
            Measure (Euclidean n)),
            b ∈ Metric.ball (y (sigma i)) r := by
        change
          ∀ᵐ b ∂Measure.map Prod.snd
            (rho (sigma i) :
              Measure (Euclidean n × Euclidean n)),
            b ∈ Metric.ball (y (sigma i)) r
        apply
          (ae_map_iff
            (p := fun b => b ∈ Metric.ball (y (sigma i)) r)
            measurable_snd.aemeasurable
            Metric.isOpen_ball.measurableSet).2
        filter_upwards [hRhoSupported (sigma i)] with z hz
        exact hz.2
      have hCrossedSupported (i : I) :
          ∀ᵐ z ∂(crossed i :
            Measure (Euclidean n × Euclidean n)),
            z.1 ∈ Metric.ball (x i) r ∧
              z.2 ∈ Metric.ball (y (sigma i)) r := by
        rw [show
          (crossed i : Measure (Euclidean n × Euclidean n)) =
            (firstMarginal (rho i) :
              Measure (Euclidean n)).prod
              (secondMarginal (rho (sigma i)) :
                Measure (Euclidean n)) by
          rfl]
        apply
          (Measure.ae_prod_iff_ae_ae
            ((Metric.isOpen_ball.measurableSet.prod
              Metric.isOpen_ball.measurableSet))).2
        filter_upwards [hFirstSupported i] with a ha
        filter_upwards [hSecondSupported i] with b hb
        exact ⟨ha, hb⟩
      have hRhoIntegrable (i : I) :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (rho i : Measure (Euclidean n × Euclidean n)) :=
        integrableDistance_of_mem_prod_ball
          (rho i) (x i) (y i) r (hRhoSupported i)
      have hCrossedIntegrable (i : I) :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (crossed i :
              Measure (Euclidean n × Euclidean n)) :=
        integrableDistance_of_mem_prod_ball
          (crossed i) (x i) (y (sigma i)) r
          (hCrossedSupported i)
      have hDirectBounds (i : I) :
          dist (x i) (y i) - 2 * r <=
              ∫ z, dist z.1 z.2
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n)) ∧
            (∫ z, dist z.1 z.2
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n))) <=
              dist (x i) (y i) + 2 * r :=
        integralDistance_mem_prod_ball_bounds
          (rho i) (x i) (y i) r (hRhoMass i)
          (hRhoSupported i) (hRhoIntegrable i)
      have hCrossedBounds (i : I) :
          dist (x i) (y (sigma i)) - 2 * r <=
              ∫ z, dist z.1 z.2
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n)) ∧
            (∫ z, dist z.1 z.2
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n))) <=
              dist (x i) (y (sigma i)) + 2 * r :=
        integralDistance_mem_prod_ball_bounds
          (crossed i) (x i) (y (sigma i)) r
          (hCrossedMass i) (hCrossedSupported i)
          (hCrossedIntegrable i)
      let direct :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        ∑ i, rho i
      let rerouted :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        ∑ i, crossed i
      have hDirectIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (direct : Measure (Euclidean n × Euclidean n)) := by
        dsimp only [direct]
        rw [FiniteMeasure.toMeasure_sum]
        exact integrable_finsetSum_measure.mpr fun i _ =>
          hRhoIntegrable i
      have hReroutedIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (rerouted : Measure (Euclidean n × Euclidean n)) := by
        dsimp only [rerouted]
        rw [FiniteMeasure.toMeasure_sum]
        exact integrable_finsetSum_measure.mpr fun i _ =>
          hCrossedIntegrable i
      have hDirectIntegral :
          (∫ z, dist z.1 z.2
              ∂(direct :
                Measure (Euclidean n × Euclidean n))) =
            ∑ i,
              ∫ z, dist z.1 z.2
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n)) := by
        dsimp only [direct]
        rw [FiniteMeasure.toMeasure_sum]
        exact integral_finsetSum_measure fun i _ => hRhoIntegrable i
      have hReroutedIntegral :
          (∫ z, dist z.1 z.2
              ∂(rerouted :
                Measure (Euclidean n × Euclidean n))) =
            ∑ i,
              ∫ z, dist z.1 z.2
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n)) := by
        dsimp only [rerouted]
        rw [FiniteMeasure.toMeasure_sum]
        exact
          integral_finsetSum_measure fun i _ => hCrossedIntegrable i
      have hDirectLower :
          directCenter - 2 * cardReal * r <=
            ∑ i,
              ∫ z, dist z.1 z.2
                ∂(rho i :
                  Measure (Euclidean n × Euclidean n)) := by
        calc
          directCenter - 2 * cardReal * r =
              ∑ i, (dist (x i) (y i) - 2 * r) := by
            simp [directCenter, cardReal]
            ring
          _ <=
              ∑ i,
                ∫ z, dist z.1 z.2
                  ∂(rho i :
                    Measure (Euclidean n × Euclidean n)) :=
            Finset.sum_le_sum fun i _ => (hDirectBounds i).1
      have hReroutedUpper :
          (∑ i,
              ∫ z, dist z.1 z.2
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n))) <=
            crossedCenter + 2 * cardReal * r := by
        calc
          (∑ i,
              ∫ z, dist z.1 z.2
                ∂(crossed i :
                  Measure (Euclidean n × Euclidean n))) <=
              ∑ i,
                (dist (x i) (y (sigma i)) + 2 * r) :=
            Finset.sum_le_sum fun i _ => (hCrossedBounds i).2
          _ = crossedCenter + 2 * cardReal * r := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
            dsimp only [crossedCenter, cardReal]
            ring
      have hReroutedCheaper :
          (∫ z, dist z.1 z.2
              ∂(rerouted :
                Measure (Euclidean n × Euclidean n))) <
            ∫ z, dist z.1 z.2
              ∂(direct :
                Measure (Euclidean n × Euclidean n)) := by
        rw [hDirectIntegral, hReroutedIntegral]
        linarith
      have hFirstMarginalRerouted :
          firstMarginal rerouted = firstMarginal direct := by
        rw [show firstMarginal rerouted =
            ∑ i, firstMarginal (crossed i) by
          exact firstMarginal_fintypeSum crossed]
        rw [show firstMarginal direct =
            ∑ i, firstMarginal (rho i) by
          exact firstMarginal_fintypeSum rho]
        apply Fintype.sum_congr
        intro i
        rw [firstMarginal_crossProduct, hRhoMass]
        simp
      have hSecondMarginalRerouted :
          secondMarginal rerouted = secondMarginal direct := by
        rw [show secondMarginal rerouted =
            ∑ i, secondMarginal (crossed i) by
          exact secondMarginal_fintypeSum crossed]
        rw [show secondMarginal direct =
            ∑ i, secondMarginal (rho i) by
          exact secondMarginal_fintypeSum rho]
        calc
          (∑ i, secondMarginal (crossed i)) =
              ∑ i, secondMarginal (rho (sigma i)) := by
            apply Fintype.sum_congr
            intro i
            rw [secondMarginal_crossProduct, hRhoMass]
            simp
          _ = ∑ i, secondMarginal (rho i) :=
            Equiv.sum_comp sigma (fun i => secondMarginal (rho i))
      let minimumMass : NNReal :=
        Finset.univ.inf' Finset.univ_nonempty
          (fun i => (tau i).mass)
      have hMinimumMassPositive : 0 < minimumMass := by
        apply
          (Finset.lt_inf'_iff (s := Finset.univ)
            Finset.univ_nonempty).2
        intro i _hi
        exact hTauMassPositive i
      have hMinimumMassLe (i : I) :
          minimumMass <= (tau i).mass := by
        exact Finset.inf'_le _ (Finset.mem_univ i)
      let cardNN : NNReal := Fintype.card I
      have hCardNN : 0 < cardNN := by
        dsimp only [cardNN]
        exact_mod_cast Fintype.card_pos
      let c : NNReal := minimumMass / cardNN
      have hc : 0 < c := by
        dsimp only [c]
        positivity
      let removed :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        c • direct
      let added :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        c • rerouted
      have hFirstMarginalAdded :
          firstMarginal added = firstMarginal removed := by
        dsimp only [added, removed]
        rw [firstMarginal_smul, firstMarginal_smul,
          hFirstMarginalRerouted]
      have hSecondMarginalAdded :
          secondMarginal added = secondMarginal removed := by
        dsimp only [added, removed]
        rw [secondMarginal_smul, secondMarginal_smul,
          hSecondMarginalRerouted]
      have hCoefficientLe (i : I) :
          c * (tau i).mass⁻¹ <= cardNN⁻¹ := by
        rw [show c * (tau i).mass⁻¹ = c / (tau i).mass by
          rw [div_eq_mul_inv]]
        rw [show cardNN⁻¹ = 1 / cardNN by
          rw [one_div]]
        apply
          (div_le_div_iff₀ (hTauMassPositive i) hCardNN).2
        dsimp only [c]
        rw [div_mul_cancel₀ _ hCardNN.ne']
        simpa using hMinimumMassLe i
      have hBlockLe (i : I) :
          (((c • rho i :
              FiniteMeasure (Euclidean n × Euclidean n))) :
              Measure (Euclidean n × Euclidean n)) <=
            (((cardNN⁻¹ • gamma.plan :
              FiniteMeasure (Euclidean n × Euclidean n))) :
              Measure (Euclidean n × Euclidean n)) := by
        have hTauLe :
            (tau i :
                Measure (Euclidean n × Euclidean n)) <=
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) := by
          dsimp only [tau]
          exact Measure.restrict_le_self
        change
          c • (rho i :
              Measure (Euclidean n × Euclidean n)) <=
            cardNN⁻¹ •
              (gamma.plan :
                Measure (Euclidean n × Euclidean n))
        rw [show
          (rho i :
              Measure (Euclidean n × Euclidean n)) =
            (tau i).mass⁻¹ •
              (tau i :
                Measure (Euclidean n × Euclidean n)) by
          dsimp only [rho]
          rw [FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero
            _ (hTauNonzero i), FiniteMeasure.toMeasure_smul]]
        rw [smul_smul]
        apply Measure.le_iff'.2
        intro s
        simp only [Measure.coe_nnreal_smul_apply]
        exact
          mul_le_mul
            (ENNReal.coe_le_coe.mpr (hCoefficientLe i))
            (hTauLe s) (by exact bot_le) (by exact bot_le)
      have hConstantSum :
          (∑ _i : I, cardNN⁻¹ • gamma.plan) = gamma.plan := by
        rw [← Finset.sum_smul]
        simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        change (cardNN * cardNN⁻¹) • gamma.plan = gamma.plan
        rw [mul_inv_cancel₀ hCardNN.ne']
        simp
      have hRemovedAsSum :
          removed = ∑ i, c • rho i := by
        dsimp only [removed, direct]
        simpa only using
          (Finset.smul_sum
            (s := Finset.univ) (r := c) (f := rho))
      have hRemovedLe :
          (removed :
              Measure (Euclidean n × Euclidean n)) <=
            (gamma.plan :
              Measure (Euclidean n × Euclidean n)) := by
        rw [hRemovedAsSum, FiniteMeasure.toMeasure_sum]
        calc
          (∑ i,
              ((c • rho i :
                FiniteMeasure (Euclidean n × Euclidean n)) :
                Measure (Euclidean n × Euclidean n))) <=
              ∑ i,
                ((cardNN⁻¹ • gamma.plan :
                  FiniteMeasure
                    (Euclidean n × Euclidean n)) :
                  Measure (Euclidean n × Euclidean n)) :=
            Finset.sum_le_sum fun i _ => hBlockLe i
          _ = (gamma.plan :
                Measure (Euclidean n × Euclidean n)) := by
            rw [← FiniteMeasure.toMeasure_sum, hConstantSum]
      have hRemovedIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (removed :
              Measure (Euclidean n × Euclidean n)) := by
        dsimp only [removed]
        exact hDirectIntegrable.smul_measure_nnreal
      have hAddedIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (added :
              Measure (Euclidean n × Euclidean n)) := by
        dsimp only [added]
        exact hReroutedIntegrable.smul_measure_nnreal
      have hAddedCheaper :
          (∫ z, dist z.1 z.2
              ∂(added :
                Measure (Euclidean n × Euclidean n))) <
            ∫ z, dist z.1 z.2
              ∂(removed :
                Measure (Euclidean n × Euclidean n)) := by
        dsimp only [added, removed]
        simp only [FiniteMeasure.toMeasure_smul,
          integral_smul_nnreal_measure]
        exact
          mul_lt_mul_of_pos_left hReroutedCheaper
            (by exact_mod_cast hc)
      obtain
          ⟨remainder, _hRemainderEq, hRemainderLe,
            hDecomposition⟩ :=
        existsFiniteMeasureRemainderOfLe
          gamma.plan removed hRemovedLe
      have hReplacementMarginals :=
        finiteMeasureReplacementPreservesMarginals
          remainder removed added gamma.plan hDecomposition
          hFirstMarginalAdded hSecondMarginalAdded
      let etaPlan :
          FiniteMeasure (Euclidean n × Euclidean n) :=
        remainder + added
      let eta : FiniteCoupling mu nu :=
        ⟨etaPlan,
          ⟨hReplacementMarginals.1.trans gamma.property.1,
            hReplacementMarginals.2.trans gamma.property.2⟩⟩
      have hGammaDistanceIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (gamma.plan :
              Measure (Euclidean n × Euclidean n)) := by
        simpa only [dist_eq_norm] using
          distanceIntegrableOfMarginalFirstMoments
            hSourceMoment hTargetMoment gamma
      have hRemainderIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              dist z.1 z.2)
            (remainder :
              Measure (Euclidean n × Euclidean n)) :=
        hGammaDistanceIntegrable.mono_measure hRemainderLe
      have hEtaCheaper :
          distanceCost eta < distanceCost gamma := by
        have hProfileCheaper :=
          profileCostReroutingLtOfAddedLtRemoved
            (profile := id) (gamma := gamma) (eta := eta)
            (remainder := remainder) (removed := removed)
            (added := added) hDecomposition.symm rfl
            (by
              simpa only [id_eq, dist_eq_norm] using
                hRemainderIntegrable)
            (by
              simpa only [id_eq, dist_eq_norm] using
                hRemovedIntegrable)
            (by
              simpa only [id_eq, dist_eq_norm] using
                hAddedIntegrable)
            (by
              simpa only [id_eq, dist_eq_norm] using
                hAddedCheaper)
        simpa only [distanceCost] using hProfileCheaper
      have hOptimalLe :
          distanceCost gamma <= distanceCost eta := by
        exact hOptimal.2 eta (mem_univ eta)
      exact (not_lt_of_ge hOptimalLe) hEtaCheaper

end ConcaveOTLimit
