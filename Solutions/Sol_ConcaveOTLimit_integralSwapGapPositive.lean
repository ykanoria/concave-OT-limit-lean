import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho : FiniteMeasure X) (sigma : FiniteMeasure Y)
    {gap : X × Y -> Real} {delta : Real}
    (hRho : 0 < rho.mass) (hSigma : 0 < sigma.mass)
    (hDelta : 0 < delta)
    (hIntegrable :
      Integrable gap
        ((rho.prod sigma : FiniteMeasure (X × Y)) :
          Measure (X × Y)))
    (hGap :
      ∀ᵐ z ∂((rho.prod sigma : FiniteMeasure (X × Y)) :
        Measure (X × Y)), delta <= gap z) :
    0 <
      ∫ z, gap z
        ∂((rho.prod sigma : FiniteMeasure (X × Y)) :
          Measure (X × Y)) := by
  let eta : Measure (X × Y) :=
    ((rho.prod sigma : FiniteMeasure (X × Y)) : Measure (X × Y))
  have hConstIntegrable : Integrable (fun _ : X × Y => delta) eta :=
    integrable_const delta
  have hLower :
      ∫ _ : X × Y, delta ∂eta <= ∫ z, gap z ∂eta :=
    integral_mono_ae hConstIntegrable hIntegrable hGap
  have hProdMass : 0 < (rho.prod sigma).mass := by
    rw [FiniteMeasure.mass_prod]
    exact mul_pos hRho hSigma
  have hMassPositive : 0 < eta.real Set.univ := by
    rw [Measure.real]
    apply ENNReal.toReal_pos
    · dsimp only [eta]
      rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact_mod_cast hProdMass.ne'
    · exact measure_ne_top eta Set.univ
  have hConstPositive :
      0 < ∫ _ : X × Y, delta ∂eta := by
    rw [integral_const]
    exact mul_pos hMassPositive hDelta
  exact hConstPositive.trans_le hLower
