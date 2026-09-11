import Theorems.Thm_ConcaveOTLimit_distanceCostEqMomentDifferenceAddBackward
import Theorems.Thm_ConcaveOTLimit_distanceCostEqMomentDifferenceIffForward
import Mathlib.Tactic.NormNum

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem momentDifferenceLeDistanceCost
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real)) :
    (integral (nu : Measure Real) fun y => y) -
        (integral (mu : Measure Real) fun x => x) <=
      distanceCost gamma := by
  rw [distanceCostEqMomentDifferenceAddBackward gamma hMu hNu]
  exact le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (integral_nonneg fun z => le_max_right _ _))

/-- If one forward real-line coupling exists, the forward couplings are
exactly the distance-optimal face. -/
theorem forwardPlansEqDistanceOptimalFace
    {mu nu : FiniteMeasure Real}
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real))
    (gammaForward : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gammaForward) :
    {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} =
      distanceOptimalFace mu nu := by
  ext gamma
  constructor
  · intro hGammaForward
    change IsDistanceOptimal gamma
    unfold IsDistanceOptimal IsProfileMinimizer IsMinimizerOn
    refine ⟨mem_univ gamma, ?_⟩
    intro eta _hEta
    change distanceCost gamma <= distanceCost eta
    rw [(distanceCostEqMomentDifferenceIffForward gamma hMu hNu).mpr
      hGammaForward]
    exact momentDifferenceLeDistanceCost eta hMu hNu
  · intro hGammaOptimal
    change IsDistanceOptimal gamma at hGammaOptimal
    rcases hGammaOptimal with ⟨_hGammaMem, hOptimal⟩
    have hLe :
        distanceCost gamma <= distanceCost gammaForward :=
      hOptimal gammaForward (mem_univ gammaForward)
    have hForwardCost :
        distanceCost gammaForward =
          (integral (nu : Measure Real) fun y => y) -
            (integral (mu : Measure Real) fun x => x) :=
      (distanceCostEqMomentDifferenceIffForward
        gammaForward hMu hNu).mpr hForward
    have hLower :
        (integral (nu : Measure Real) fun y => y) -
            (integral (mu : Measure Real) fun x => x) <=
          distanceCost gamma :=
      momentDifferenceLeDistanceCost gamma hMu hNu
    apply (distanceCostEqMomentDifferenceIffForward gamma hMu hNu).mp
    exact le_antisymm (hLe.trans_eq hForwardCost) hLower

end ConcaveOTLimit
