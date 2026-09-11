import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory

namespace ConcaveOTLimit

/-- Crossing the target marginals of two finite plans preserves the marginals
of their mass-balanced sum. -/
theorem crossProductReroutingMarginals
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (rho sigma : FiniteMeasure (X × Y)) :
    firstMarginal
        ((firstMarginal rho).prod (secondMarginal sigma) +
          (firstMarginal sigma).prod (secondMarginal rho)) =
      firstMarginal (sigma.mass • rho + rho.mass • sigma) ∧
    secondMarginal
        ((firstMarginal rho).prod (secondMarginal sigma) +
          (firstMarginal sigma).prod (secondMarginal rho)) =
      secondMarginal (sigma.mass • rho + rho.mass • sigma) := by
  have map_fst_mass (tau : FiniteMeasure (X × Y)) :
      (tau.map Prod.fst).mass = tau.mass := by
    rw [FiniteMeasure.mass,
      FiniteMeasure.map_apply tau measurable_fst MeasurableSet.univ]
    simp [FiniteMeasure.mass]
  have map_snd_mass (tau : FiniteMeasure (X × Y)) :
      (tau.map Prod.snd).mass = tau.mass := by
    rw [FiniteMeasure.mass,
      FiniteMeasure.map_apply tau measurable_snd MeasurableSet.univ]
    simp [FiniteMeasure.mass]
  constructor
  · unfold firstMarginal secondMarginal
    rw [FiniteMeasure.map_add measurable_fst,
      FiniteMeasure.map_add measurable_fst]
    simp only [FiniteMeasure.map_fst_prod, FiniteMeasure.map_smul]
    rw [show (sigma.map Prod.snd) Set.univ = sigma.mass by
        exact map_snd_mass sigma,
      show (rho.map Prod.snd) Set.univ = rho.mass by
        exact map_snd_mass rho]
  · unfold firstMarginal secondMarginal
    rw [FiniteMeasure.map_add measurable_snd,
      FiniteMeasure.map_add measurable_snd]
    simp only [FiniteMeasure.map_snd_prod, FiniteMeasure.map_smul]
    rw [show (rho.map Prod.fst) Set.univ = rho.mass by
        exact map_fst_mass rho,
      show (sigma.map Prod.fst) Set.univ = sigma.mass by
        exact map_fst_mass sigma]
    ac_rfl

end ConcaveOTLimit
