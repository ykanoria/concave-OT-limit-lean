import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (remainder rho sigma : FiniteMeasure (Real × Real))
    (c : NNReal)
    (hForward : IsForwardPlan gamma)
    (hRemainderLe :
      (remainder : Measure (Real × Real)) <=
        (gamma.plan : Measure (Real × Real)))
    (hCrossed :
      ∀ᵐ r ∂(rho : Measure (Real × Real)),
        ∀ᵐ s ∂(sigma : Measure (Real × Real)),
          r.1 < s.2 /\ s.1 < r.2) :
    ∀ᵐ z ∂((remainder +
        c •
          ((firstMarginal rho).prod (secondMarginal sigma) +
            (firstMarginal sigma).prod (secondMarginal rho)) :
          FiniteMeasure (Real × Real)) :
        Measure (Real × Real)),
      z.1 <= z.2 := by
  have orderedMarginalProduct
      (tau upsilon : FiniteMeasure (Real × Real))
      (hOrdered :
        ∀ᵐ a ∂(tau : Measure (Real × Real)),
          ∀ᵐ b ∂(upsilon : Measure (Real × Real)),
            a.1 <= b.2) :
      ∀ᵐ z ∂(((firstMarginal tau).prod
          (secondMarginal upsilon) :
            FiniteMeasure (Real × Real)) :
        Measure (Real × Real)),
        z.1 <= z.2 := by
    have hOnProduct :
        ∀ᵐ ab ∂((tau : Measure (Real × Real)).prod
            (upsilon : Measure (Real × Real))),
          ab.1.1 <= ab.2.2 := by
      exact
        (Measure.ae_prod_iff_ae_ae
          (measurableSet_le
            (continuous_fst.comp continuous_fst).measurable
            (continuous_snd.comp continuous_snd).measurable)).2
          hOrdered
    let coordinateCross :
        ((Real × Real) × (Real × Real)) -> Real × Real :=
      fun ab => (ab.1.1, ab.2.2)
    have hCoordinateCross : Measurable coordinateCross := by
      dsimp only [coordinateCross]
      fun_prop
    have hProductMap :
        (firstMarginal tau).prod (secondMarginal upsilon) =
          (tau.prod upsilon).map coordinateCross := by
      simpa only [firstMarginal, secondMarginal,
        coordinateCross, Prod.map_apply] using
        FiniteMeasure.map_prod_map tau upsilon
          measurable_fst measurable_snd
    rw [hProductMap, FiniteMeasure.toMeasure_map]
    apply
      (ae_map_iff hCoordinateCross.aemeasurable
        (measurableSet_le measurable_fst measurable_snd)).2
    exact hOnProduct
  have hRhoSigma :
      ∀ᵐ r ∂(rho : Measure (Real × Real)),
        ∀ᵐ s ∂(sigma : Measure (Real × Real)),
          r.1 <= s.2 := by
    filter_upwards [hCrossed] with r hr
    filter_upwards [hr] with s hrs
    exact hrs.1.le
  have hSigmaRho :
      ∀ᵐ s ∂(sigma : Measure (Real × Real)),
        ∀ᵐ r ∂(rho : Measure (Real × Real)),
          s.1 <= r.2 := by
    have hRhoSigmaReverse :
        ∀ᵐ r ∂(rho : Measure (Real × Real)),
          ∀ᵐ s ∂(sigma : Measure (Real × Real)),
            s.1 <= r.2 := by
      filter_upwards [hCrossed] with r hr
      filter_upwards [hr] with s hrs
      exact hrs.2.le
    have hRelationMeasurable :
        MeasurableSet
          {rs : (Real × Real) × (Real × Real) |
            rs.2.1 <= rs.1.2} :=
      measurableSet_le
        (continuous_fst.comp continuous_snd).measurable
        (continuous_snd.comp continuous_fst).measurable
    exact
      (Measure.ae_ae_comm
        (μ := (rho : Measure (Real × Real)))
        (ν := (sigma : Measure (Real × Real)))
        hRelationMeasurable).mp hRhoSigmaReverse
  have hFirstProduct :=
    orderedMarginalProduct rho sigma hRhoSigma
  have hSecondProduct :=
    orderedMarginalProduct sigma rho hSigmaRho
  rw [FiniteMeasure.toMeasure_add, ae_add_measure_iff]
  constructor
  · exact
      hForward.filter_mono
        (MeasureTheory.ae_mono hRemainderLe)
  · rw [FiniteMeasure.toMeasure_smul]
    apply Measure.ae_smul_measure
    rw [FiniteMeasure.toMeasure_add, ae_add_measure_iff]
    exact ⟨hFirstProduct, hSecondProduct⟩
