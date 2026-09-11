import Theorems.Thm_ConcaveOTLimit_crossProductReroutingIsForward
import Theorems.Thm_ConcaveOTLimit_existsBalancedCrossProductReroutingCoupling

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    {U V : Set (Real × Real)}
    (hMeasurable : MeasurableSet U ∧ MeasurableSet V)
    (hDisjoint : Disjoint U V) (c : NNReal)
    (hCoeffU : c * (gamma.plan.restrict U).mass ≤ 1)
    (hCoeffV : c * (gamma.plan.restrict V).mass ≤ 1)
    (hForward : IsForwardPlan gamma)
    (hCrossed :
      ∀ᵐ r ∂(gamma.plan.restrict U : Measure (Real × Real)),
        ∀ᵐ s ∂(gamma.plan.restrict V : Measure (Real × Real)),
          r.1 < s.2 ∧ s.1 < r.2) :
    let rho := gamma.plan.restrict U
    let sigma := gamma.plan.restrict V
    let removed := c • (sigma.mass • rho + rho.mass • sigma)
    let added := c •
      ((firstMarginal rho).prod (secondMarginal sigma) +
        (firstMarginal sigma).prod (secondMarginal rho))
    ∃ remainder : FiniteMeasure (Real × Real),
      ∃ eta : FiniteCoupling mu nu,
        IsForwardPlan eta ∧
          (removed : Measure (Real × Real)) ≤
            (gamma.plan : Measure (Real × Real)) ∧
          (remainder : Measure (Real × Real)) =
            (gamma.plan : Measure (Real × Real)) -
              (removed : Measure (Real × Real)) ∧
          (remainder : Measure (Real × Real)) ≤
            (gamma.plan : Measure (Real × Real)) ∧
          remainder + removed = gamma.plan ∧
          eta.plan = remainder + added := by
  dsimp only
  let rho := gamma.plan.restrict U
  let sigma := gamma.plan.restrict V
  let removed := c • (sigma.mass • rho + rho.mass • sigma)
  let added := c •
    ((firstMarginal rho).prod (secondMarginal sigma) +
      (firstMarginal sigma).prod (secondMarginal rho))
  obtain ⟨remainder, eta, hRemoved, hRemainder, hRemainderLe,
      hDecomposition, hEtaPlan⟩ :=
    existsBalancedCrossProductReroutingCoupling gamma hMeasurable
      hDisjoint c hCoeffU hCoeffV
  have hPlanForward :
      ∀ᵐ z ∂((remainder + added : FiniteMeasure (Real × Real)) :
        Measure (Real × Real)), z.1 ≤ z.2 :=
    crossProductReroutingIsForward gamma remainder rho sigma c
      hForward hRemainderLe hCrossed
  have hEtaForward : IsForwardPlan eta := by
    unfold IsForwardPlan
    rw [hEtaPlan]
    exact hPlanForward
  exact ⟨remainder, eta, hEtaForward, hRemoved, hRemainder,
    hRemainderLe, hDecomposition, hEtaPlan⟩
