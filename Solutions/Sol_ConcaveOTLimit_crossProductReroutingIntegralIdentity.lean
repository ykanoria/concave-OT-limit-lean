import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

open ConcaveOTLimit

theorem solution
    (rho sigma : FiniteMeasure (Real × Real))
    (profile : Real -> Real)
    (hCostMeasurable :
      Measurable
        (fun z : Real × Real => profile (dist z.1 z.2)))
    (hRho :
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (rho : Measure (Real × Real)))
    (hSigma :
      Integrable
        (fun z : Real × Real => profile (dist z.1 z.2))
        (sigma : Measure (Real × Real)))
    (hFirstCrossed :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.2.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))))
    (hSecondCrossed :
      Integrable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.1.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real)))) :
    (∫ z, profile (dist z.1 z.2)
        ∂((sigma.mass • rho + rho.mass • sigma :
          FiniteMeasure (Real × Real)) :
          Measure (Real × Real))) -
      (∫ z, profile (dist z.1 z.2)
        ∂(((firstMarginal rho).prod (secondMarginal sigma) +
          (firstMarginal sigma).prod (secondMarginal rho) :
            FiniteMeasure (Real × Real)) :
          Measure (Real × Real))) =
    ∫ rs,
      profile (dist rs.1.1 rs.1.2) +
          profile (dist rs.2.1 rs.2.2) -
        profile (dist rs.1.1 rs.2.2) -
        profile (dist rs.2.1 rs.1.2)
      ∂((rho.prod sigma : FiniteMeasure
        ((Real × Real) × (Real × Real))) :
        Measure ((Real × Real) × (Real × Real))) := by
  let cost : Real × Real -> Real :=
    fun z => profile (dist z.1 z.2)
  let cross :
      (Real × Real) × (Real × Real) -> Real × Real :=
    fun rs => (rs.1.1, rs.2.2)
  have hCost : Measurable cost := by
    simpa only [cost] using hCostMeasurable
  have hCross : Measurable cross := by
    dsimp only [cross]
    fun_prop
  have hRhoCost :
      Integrable cost (rho : Measure (Real × Real)) := by
    simpa only [cost] using hRho
  have hSigmaCost :
      Integrable cost (sigma : Measure (Real × Real)) := by
    simpa only [cost] using hSigma
  have hFirstCrossedCost :
      Integrable (fun rs => cost (rs.1.1, rs.2.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [cost] using hFirstCrossed
  have hSecondCrossedCost :
      Integrable (fun rs => cost (rs.2.1, rs.1.2))
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [cost] using hSecondCrossed
  have hFirstMap :
      (firstMarginal rho).prod (secondMarginal sigma) =
        (rho.prod sigma).map cross := by
    simpa only [firstMarginal, secondMarginal, cross,
      Prod.map_apply] using
      FiniteMeasure.map_prod_map rho sigma
        measurable_fst measurable_snd
  have hSecondMap :
      (firstMarginal sigma).prod (secondMarginal rho) =
        (sigma.prod rho).map cross := by
    simpa only [firstMarginal, secondMarginal, cross,
      Prod.map_apply] using
      FiniteMeasure.map_prod_map sigma rho
        measurable_fst measurable_snd
  have hFirstMapIntegrable :
      Integrable cost
        (Measure.map cross
          ((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    apply
      (integrable_map_measure hCost.aestronglyMeasurable
        hCross.aemeasurable).2
    simpa only [Function.comp_apply, cross] using
      hFirstCrossedCost
  have hSecondProductIntegrable :
      Integrable (fun sr => cost (sr.1.1, sr.2.2))
        ((sigma.prod rho : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [Function.comp_apply] using
      hSecondCrossedCost.swap
  have hSecondMapIntegrable :
      Integrable cost
        (Measure.map cross
          ((sigma.prod rho : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    apply
      (integrable_map_measure hCost.aestronglyMeasurable
        hCross.aemeasurable).2
    simpa only [Function.comp_apply, cross] using
      hSecondProductIntegrable
  have hFirstCrossedIntegral :
      (∫ z, cost z
          ∂(((firstMarginal rho).prod
            (secondMarginal sigma) :
              FiniteMeasure (Real × Real)) :
            Measure (Real × Real))) =
        ∫ rs, cost (rs.1.1, rs.2.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real))) := by
    rw [hFirstMap, FiniteMeasure.toMeasure_map,
      integral_map hCross.aemeasurable
        hFirstMapIntegrable.aestronglyMeasurable]
  have hSecondCrossedIntegral :
      (∫ z, cost z
          ∂(((firstMarginal sigma).prod
            (secondMarginal rho) :
              FiniteMeasure (Real × Real)) :
            Measure (Real × Real))) =
        ∫ rs, cost (rs.2.1, rs.1.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real))) := by
    rw [hSecondMap, FiniteMeasure.toMeasure_map,
      integral_map hCross.aemeasurable
        hSecondMapIntegrable.aestronglyMeasurable]
    simpa only [cross] using
      (integral_prod_swap
        (μ := (rho : Measure (Real × Real)))
        (ν := (sigma : Measure (Real × Real)))
        (fun rs : (Real × Real) × (Real × Real) =>
          cost (rs.2.1, rs.1.2)))
  have hFirstCrossedMeasureIntegrable :
      Integrable cost
        (((firstMarginal rho).prod
          (secondMarginal sigma) :
            FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) := by
    rw [hFirstMap, FiniteMeasure.toMeasure_map]
    exact hFirstMapIntegrable
  have hSecondCrossedMeasureIntegrable :
      Integrable cost
        (((firstMarginal sigma).prod
          (secondMarginal rho) :
            FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) := by
    rw [hSecondMap, FiniteMeasure.toMeasure_map]
    exact hSecondMapIntegrable
  have hDirectIntegral :
      (∫ z, cost z
          ∂((sigma.mass • rho + rho.mass • sigma :
            FiniteMeasure (Real × Real)) :
            Measure (Real × Real))) =
        sigma.mass • (∫ z, cost z
          ∂(rho : Measure (Real × Real))) +
        rho.mass • (∫ z, cost z
          ∂(sigma : Measure (Real × Real))) := by
    simp only [FiniteMeasure.toMeasure_add,
      FiniteMeasure.toMeasure_smul]
    rw [
      integral_add_measure
        hRhoCost.smul_measure_nnreal
        hSigmaCost.smul_measure_nnreal,
      integral_smul_nnreal_measure,
      integral_smul_nnreal_measure]
  have hCrossedIntegral :
      (∫ z, cost z
          ∂(((firstMarginal rho).prod
              (secondMarginal sigma) +
            (firstMarginal sigma).prod
              (secondMarginal rho) :
            FiniteMeasure (Real × Real)) :
            Measure (Real × Real))) =
        (∫ rs, cost (rs.1.1, rs.2.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) +
        (∫ rs, cost (rs.2.1, rs.1.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    rw [FiniteMeasure.toMeasure_add,
      integral_add_measure hFirstCrossedMeasureIntegrable
        hSecondCrossedMeasureIntegrable,
      hFirstCrossedIntegral, hSecondCrossedIntegral]
  have hDirectFirstProduct :
      (∫ rs, cost rs.1
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) =
        sigma.mass •
          (∫ z, cost z ∂(rho : Measure (Real × Real))) := by
    rw [FiniteMeasure.toMeasure_prod,
      integral_prod _
        (hRhoCost.comp_fst
          (sigma : Measure (Real × Real)))]
    simp_rw [integral_const]
    rw [integral_smul]
    simp [NNReal.smul_def, Measure.real,
      ← FiniteMeasure.ennreal_mass]
  have hDirectSecondProduct :
      (∫ rs, cost rs.2
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) =
        rho.mass •
          (∫ z, cost z ∂(sigma : Measure (Real × Real))) := by
    rw [FiniteMeasure.toMeasure_prod,
      integral_prod _
        (hSigmaCost.comp_snd
          (rho : Measure (Real × Real)))]
    change
      (∫ _ : Real × Real,
        (∫ y, cost y ∂(sigma : Measure (Real × Real)))
        ∂(rho : Measure (Real × Real))) =
      rho.mass •
        (∫ z, cost z ∂(sigma : Measure (Real × Real)))
    rw [integral_const]
    simp [NNReal.smul_def, Measure.real,
      ← FiniteMeasure.ennreal_mass]
  have hFirstProductIntegrable :
      Integrable (fun rs => cost rs.1)
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) :=
    hRhoCost.comp_fst (sigma : Measure (Real × Real))
  have hSecondProductIntegrable :
      Integrable (fun rs => cost rs.2)
        ((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) :=
    hSigmaCost.comp_snd (rho : Measure (Real × Real))
  have hDirectProductIntegral :
      (∫ rs, cost rs.1 + cost rs.2
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) =
        (∫ rs, cost rs.1
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) +
        (∫ rs, cost rs.2
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    exact integral_add hFirstProductIntegrable
      hSecondProductIntegrable
  have hFirstSubtractedIntegral :
      (∫ rs,
          cost rs.1 + cost rs.2 -
            cost (rs.1.1, rs.2.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) =
        (∫ rs, cost rs.1 + cost rs.2
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) -
        (∫ rs, cost (rs.1.1, rs.2.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    exact integral_sub
      (hFirstProductIntegrable.add hSecondProductIntegrable)
      hFirstCrossedCost
  have hGapIntegral :
      (∫ rs,
          cost rs.1 + cost rs.2 -
              cost (rs.1.1, rs.2.2) -
            cost (rs.2.1, rs.1.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) =
        (∫ rs, cost rs.1
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) +
        (∫ rs, cost rs.2
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) -
        (∫ rs, cost (rs.1.1, rs.2.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) -
        (∫ rs, cost (rs.2.1, rs.1.2)
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    calc
      _ =
          (∫ rs,
              cost rs.1 + cost rs.2 -
                cost (rs.1.1, rs.2.2)
            ∂((rho.prod sigma : FiniteMeasure
              ((Real × Real) × (Real × Real))) :
              Measure ((Real × Real) × (Real × Real)))) -
          (∫ rs, cost (rs.2.1, rs.1.2)
            ∂((rho.prod sigma : FiniteMeasure
              ((Real × Real) × (Real × Real))) :
              Measure ((Real × Real) × (Real × Real)))) := by
        exact
          integral_sub
            ((hFirstProductIntegrable.add
              hSecondProductIntegrable).sub
              hFirstCrossedCost)
            hSecondCrossedCost
      _ = _ := by
        rw [hFirstSubtractedIntegral, hDirectProductIntegral]
  change
    (∫ z, cost z
        ∂((sigma.mass • rho + rho.mass • sigma :
          FiniteMeasure (Real × Real)) :
          Measure (Real × Real))) -
      (∫ z, cost z
        ∂(((firstMarginal rho).prod (secondMarginal sigma) +
          (firstMarginal sigma).prod (secondMarginal rho) :
            FiniteMeasure (Real × Real)) :
          Measure (Real × Real))) =
    ∫ rs,
      cost rs.1 + cost rs.2 -
          cost (rs.1.1, rs.2.2) -
        cost (rs.2.1, rs.1.2)
      ∂((rho.prod sigma : FiniteMeasure
        ((Real × Real) × (Real × Real))) :
        Measure ((Real × Real) × (Real × Real)))
  rw [hDirectIntegral, hCrossedIntegral, hGapIntegral,
    hDirectFirstProduct, hDirectSecondProduct]
  ring
