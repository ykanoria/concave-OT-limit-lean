import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.Probability.CDF

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

open ConcaveOTLimit

private def finiteCdf (mu : FiniteMeasure Real) :
    StieltjesFunction Real :=
  mu.mass • ProbabilityTheory.cdf (mu.normalize : Measure Real)

private theorem finiteCdf_apply (mu : FiniteMeasure Real) (x : Real) :
    finiteCdf mu x = ((mu : Measure Real) (Iic x)).toReal := by
  change (mu.mass : Real) *
      ProbabilityTheory.cdf (mu.normalize : Measure Real) x =
    ((mu : Measure Real) (Iic x)).toReal
  rw [ProbabilityTheory.cdf_eq_real]
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [← ENNReal.coe_toNNReal_eq_toReal]
  exact congrArg (fun r : NNReal => (r : Real))
    (mu.self_eq_mass_mul_normalize (Iic x)).symm

private theorem finiteCdf_measure (mu : FiniteMeasure Real) :
    (finiteCdf mu).measure = (mu : Measure Real) := by
  rw [finiteCdf, StieltjesFunction.measure_smul,
    ProbabilityTheory.measure_cdf]
  simpa using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real))
    mu.self_eq_mass_smul_normalize.symm

private theorem tendsto_finiteCdf_atBot (mu : FiniteMeasure Real) :
    Tendsto (finiteCdf mu) atBot (nhds 0) := by
  simpa [finiteCdf] using
    (ProbabilityTheory.tendsto_cdf_atBot
      (mu.normalize : Measure Real)).const_smul (mu.mass : Real)

private theorem finiteCdf_leftLim (mu : FiniteMeasure Real) (x : Real) :
    Function.leftLim (finiteCdf mu) x =
      ((mu : Measure Real) (Iio x)).toReal := by
  have hMeasure := (finiteCdf mu).measure_Iio
    (tendsto_finiteCdf_atBot mu) x
  rw [finiteCdf_measure] at hMeasure
  simp only [sub_zero] at hMeasure
  have hNonneg : 0 <= Function.leftLim (finiteCdf mu) x := by
    calc
      0 <= finiteCdf mu (x - 1) := by
        change 0 <= (mu.mass : Real) *
          ProbabilityTheory.cdf (mu.normalize : Measure Real) (x - 1)
        exact mul_nonneg (by positivity)
          (ProbabilityTheory.cdf_nonneg _ _)
      _ <= Function.leftLim (finiteCdf mu) x :=
        (finiteCdf mu).mono.le_leftLim (by linarith)
  have hReal := congrArg ENNReal.toReal hMeasure
  simpa [ENNReal.toReal_ofReal hNonneg] using hReal.symm

theorem solution
    (mu nu : FiniteMeasure Real) :
    (forall x,
      ContinuousWithinAt (signedCumulative mu nu) (Ici x) x) /\
      (forall x,
        Function.leftLim (signedCumulative mu nu) x =
          signedCumulativeLeft mu nu x) := by
  constructor
  · intro x
    simpa only [signedCumulative, finiteCdf_apply] using
      ((finiteCdf mu).right_continuous x).sub
        ((finiteCdf nu).right_continuous x)
  · intro x
    apply leftLim_eq_of_tendsto
      (inferInstance : (nhdsWithin x (Iio x)).NeBot).ne
    simpa only [signedCumulative, signedCumulativeLeft, finiteCdf_apply,
      finiteCdf_leftLim] using
      ((finiteCdf mu).mono.tendsto_leftLim x).sub
        ((finiteCdf nu).mono.tendsto_leftLim x)
