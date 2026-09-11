import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_existsFiniteMeasureRemainderOfLe
import Theorems.Thm_ConcaveOTLimit_finiteMeasureReplacementPreservesMarginals
import Theorems.Thm_ConcaveOTLimit_profileCostReroutingLtOfAddedLtRemoved
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.Ascoli

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ConcaveOTLimit

/-- Continuous `1`-Lipschitz potentials normalized to vanish at the origin. -/
private def normalizedDistancePotentials (n : Nat) :
    Set C(Euclidean n, Real) :=
  {u | LipschitzWith 1 u /\ u 0 = 0}

/-- Normalized `1`-Lipschitz potentials are compact for compact-open
convergence. -/
private theorem normalizedDistancePotentials_isCompact (n : Nat) :
    IsCompact (normalizedDistancePotentials n) := by
  let S := normalizedDistancePotentials n
  have hRange :
      ContinuousMap.toFun '' S =
        {u : Euclidean n -> Real | LipschitzWith 1 u /\ u 0 = 0} := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · rintro hu
      exact ⟨⟨u, hu.1.continuous⟩, hu, rfl⟩
  have hClosed :
      IsClosed (ContinuousMap.toFun '' S) := by
    rw [hRange]
    change
      IsClosed
        ({u : Euclidean n -> Real | LipschitzWith 1 u} ∩
          {u : Euclidean n -> Real | u 0 = 0})
    exact
      (isClosed_setOf_lipschitzWith 1).inter
        (isClosed_eq (continuous_apply 0) continuous_const)
  have hPointwiseCompact :
      IsCompact (ContinuousMap.toFun '' S) := by
    apply
      IsCompact.of_isClosed_subset
        (isCompact_univ_pi fun _ : Euclidean n => isCompact_Icc)
        hClosed
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.mem_pi]
    intro x _hx
    have hx : |u x| <= ‖x‖ := by
      simpa [hu.2, Real.dist_eq, dist_eq_norm] using
        hu.1.dist_le_mul x 0
    exact (abs_le.mp hx)
  have hEquicontinuous :
      Equicontinuous ((↑) : S -> Euclidean n -> Real) := by
    exact
      (LipschitzWith.uniformEquicontinuous
        ((↑) : S -> Euclidean n -> Real) 1
        (fun u => u.property.1)).equicontinuous
  exact
    ArzelaAscoli.isCompact_of_equicontinuous
      S hPointwiseCompact hEquicontinuous

/-- The difference of the integrals of a potential against two finite
marginals. -/
def finiteMarginalPotentialDifference
    {E : Type*} [MeasurableSpace E]
    (mu nu : FiniteMeasure E) (u : E -> Real) : Real :=
  (∫ x, u x ∂(mu : Measure E)) -
    ∫ y, u y ∂(nu : Measure E)

/-- The exact conclusion needed from distance-cost Kantorovich duality:
a `1`-Lipschitz potential whose marginal difference is the attained least
distance cost. This is an explicit argument, not an axiom or typeclass. -/
structure DistanceDualWitness
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (mu nu : FiniteMeasure E) where
  potential : E -> Real
  lipschitz : LipschitzWith 1 potential
  minimum :
    IsLeast
      (Set.range
        (distanceCost : FiniteCoupling mu nu -> Real))
      (finiteMarginalPotentialDifference mu nu potential)

namespace DistanceDualWitness

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

/-- A real-valued `1`-Lipschitz function is integrable against a finite
measure with finite first norm moment. -/
theorem integrablePotentialOfLipschitz
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E]
    (u : E -> Real) (hu : LipschitzWith 1 u)
    {rho : FiniteMeasure E}
    (hRho : Integrable (fun x : E => ‖x‖) (rho : Measure E)) :
    Integrable u (rho : Measure E) := by
  have hDom :
      Integrable (fun x : E => ‖u 0‖ + ‖x‖)
        (rho : Measure E) :=
    (integrable_const ‖u 0‖).add hRho
  refine hDom.mono' hu.continuous.aestronglyMeasurable ?_
  filter_upwards [] with x
  calc
    ‖u x‖ = ‖(u x - u 0) + u 0‖ := by
      rw [sub_add_cancel]
    _ <= ‖u x - u 0‖ + ‖u 0‖ :=
      norm_add_le _ _
    _ <= ‖x‖ + ‖u 0‖ := by
      simpa [dist_eq_norm] using hu.dist_le_mul x 0
    _ = ‖u 0‖ + ‖x‖ := add_comm _ _

/-- Subtracting a constant does not change the dual objective when the
marginals have equal finite mass. -/
theorem finiteMarginalPotentialDifference_sub_const
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E]
    {mu nu : FiniteMeasure E}
    (u : E -> Real)
    (hMu : Integrable u (mu : Measure E))
    (hNu : Integrable u (nu : Measure E))
    (hMass : mu.mass = nu.mass)
    (c : Real) :
    finiteMarginalPotentialDifference mu nu (fun x => u x - c) =
      finiteMarginalPotentialDifference mu nu u := by
  have hMassReal : (mu.mass : Real) = (nu.mass : Real) := by
    exact congrArg ((↑) : NNReal -> Real) hMass
  change
    ((mu Set.univ : NNReal) : Real) =
      ((nu Set.univ : NNReal) : Real) at hMassReal
  unfold finiteMarginalPotentialDifference
  rw [integral_sub hMu (integrable_const c),
    integral_sub hNu (integrable_const c)]
  simp only [integral_const, smul_eq_mul,
    FiniteMeasure.measureReal_eq_coe_coeFn]
  rw [hMassReal]
  ring

/-- A witness potential is integrable under a finite first norm moment. -/
theorem integrablePotential
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E]
    {mu nu : FiniteMeasure E} (w : DistanceDualWitness mu nu)
    {rho : FiniteMeasure E}
    (hRho : Integrable (fun x : E => ‖x‖) (rho : Measure E)) :
    Integrable w.potential (rho : Measure E) :=
  integrablePotentialOfLipschitz w.potential w.lipschitz hRho

private theorem integralPotentialDifference_eq
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (u : E -> Real)
    (hMu : Integrable u (mu : Measure E))
    (hNu : Integrable u (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    (∫ z : E × E, (u z.1 - u z.2)
        ∂(gamma.plan : Measure (E × E))) =
      finiteMarginalPotentialDifference mu nu u := by
  have hFst :
      Integrable (fun z : E × E => u z.1)
        (gamma.plan : Measure (E × E)) :=
    (measurePreservingFst gamma).integrable_comp_of_integrable hMu
  have hSnd :
      Integrable (fun z : E × E => u z.2)
        (gamma.plan : Measure (E × E)) :=
    (measurePreservingSnd gamma).integrable_comp_of_integrable hNu
  have hFstIntegral :
      (∫ z : E × E, u z.1 ∂(gamma.plan : Measure (E × E))) =
        ∫ x, u x ∂(mu : Measure E) := by
    calc
      (∫ z : E × E, u z.1 ∂(gamma.plan : Measure (E × E))) =
          ∫ x, u x ∂Measure.map Prod.fst
            (gamma.plan : Measure (E × E)) := by
        symm
        apply integral_map
          (μ := (gamma.plan : Measure (E × E)))
          measurable_fst.aemeasurable
        rw [(measurePreservingFst gamma).map_eq]
        exact hMu.aestronglyMeasurable
      _ = ∫ x, u x ∂(mu : Measure E) := by
        rw [(measurePreservingFst gamma).map_eq]
  have hSndIntegral :
      (∫ z : E × E, u z.2 ∂(gamma.plan : Measure (E × E))) =
        ∫ y, u y ∂(nu : Measure E) := by
    calc
      (∫ z : E × E, u z.2 ∂(gamma.plan : Measure (E × E))) =
          ∫ y, u y ∂Measure.map Prod.snd
            (gamma.plan : Measure (E × E)) := by
        symm
        apply integral_map
          (μ := (gamma.plan : Measure (E × E)))
          measurable_snd.aemeasurable
        rw [(measurePreservingSnd gamma).map_eq]
        exact hNu.aestronglyMeasurable
      _ = ∫ y, u y ∂(nu : Measure E) := by
        rw [(measurePreservingSnd gamma).map_eq]
  rw [integral_sub hFst hSnd, hFstIntegral, hSndIntegral]
  rfl

/-- Weak Kantorovich duality for a `1`-Lipschitz potential. -/
theorem finiteMarginalPotentialDifference_le_distanceCost
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [MeasurableSub₂ E]
    {mu nu : FiniteMeasure E}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hSourceMoment :
      Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hTargetMoment :
      Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    finiteMarginalPotentialDifference mu nu u <= distanceCost gamma := by
  have hSourcePotential :
      Integrable u (mu : Measure E) :=
    integrablePotentialOfLipschitz u hu hSourceMoment
  have hTargetPotential :
      Integrable u (nu : Measure E) :=
    integrablePotentialOfLipschitz u hu hTargetMoment
  have hPotentialDifference :
      Integrable (fun z : E × E => u z.1 - u z.2)
        (gamma.plan : Measure (E × E)) :=
    ((measurePreservingFst gamma).integrable_comp_of_integrable
      hSourcePotential).sub
      ((measurePreservingSnd gamma).integrable_comp_of_integrable
        hTargetPotential)
  have hDistance :
      Integrable (fun z : E × E => dist z.1 z.2)
        (gamma.plan : Measure (E × E)) := by
    simpa [dist_eq_norm] using
      distanceIntegrableOfMarginalFirstMoments
        hSourceMoment hTargetMoment gamma
  calc
    finiteMarginalPotentialDifference mu nu u =
        ∫ z : E × E, (u z.1 - u z.2)
          ∂(gamma.plan : Measure (E × E)) :=
      (integralPotentialDifference_eq
        u hSourcePotential hTargetPotential gamma).symm
    _ <= ∫ z : E × E, dist z.1 z.2
          ∂(gamma.plan : Measure (E × E)) := by
      apply integral_mono hPotentialDifference hDistance
      intro z
      apply sub_le_iff_le_add'.2
      simpa using hu.le_add_mul z.1 z.2
    _ = distanceCost gamma := by
      simp [distanceCost, profileCost, dist_eq_norm]

/-- Equality in weak distance duality is equivalent to concentration on the
potential's distance contact set. -/
theorem distanceCost_eq_finiteMarginalPotentialDifference_iff_isSupported
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [MeasurableSub₂ E]
    {mu nu : FiniteMeasure E}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hSourceMoment :
      Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hTargetMoment :
      Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    distanceCost gamma = finiteMarginalPotentialDifference mu nu u <->
      IsSupported gamma (distanceContactSet u) := by
  have hSourcePotential :
      Integrable u (mu : Measure E) :=
    integrablePotentialOfLipschitz u hu hSourceMoment
  have hTargetPotential :
      Integrable u (nu : Measure E) :=
    integrablePotentialOfLipschitz u hu hTargetMoment
  have hPotentialDifference :
      Integrable (fun z : E × E => u z.1 - u z.2)
        (gamma.plan : Measure (E × E)) :=
    ((measurePreservingFst gamma).integrable_comp_of_integrable
      hSourcePotential).sub
      ((measurePreservingSnd gamma).integrable_comp_of_integrable
        hTargetPotential)
  have hDistance :
      Integrable (fun z : E × E => dist z.1 z.2)
        (gamma.plan : Measure (E × E)) := by
    simpa [dist_eq_norm] using
      distanceIntegrableOfMarginalFirstMoments
        hSourceMoment hTargetMoment gamma
  have hPotentialIntegral :
      (∫ z : E × E, (u z.1 - u z.2)
          ∂(gamma.plan : Measure (E × E))) =
        finiteMarginalPotentialDifference mu nu u :=
    integralPotentialDifference_eq
      u hSourcePotential hTargetPotential gamma
  have hDifferenceLeDistance :
      (fun z : E × E => u z.1 - u z.2) ≤ᵐ[
          (gamma.plan : Measure (E × E))]
        (fun z => dist z.1 z.2) :=
    Filter.Eventually.of_forall fun z => by
      apply sub_le_iff_le_add'.2
      simpa using hu.le_add_mul z.1 z.2
  have hDistanceCost :
      distanceCost gamma =
        ∫ z : E × E, dist z.1 z.2
          ∂(gamma.plan : Measure (E × E)) := by
    simp [distanceCost, profileCost, dist_eq_norm]
  rw [hDistanceCost, ← hPotentialIntegral]
  constructor
  · intro hIntegral
    have hPotentialEqDistance :
        (fun z : E × E => u z.1 - u z.2) =ᵐ[
            (gamma.plan : Measure (E × E))]
          (fun z => dist z.1 z.2) :=
      (integral_eq_iff_of_ae_le hPotentialDifference hDistance
        hDifferenceLeDistance).mp hIntegral.symm
    exact hPotentialEqDistance.symm
  · intro hContact
    exact integral_congr_ae hContact

/-- A coupling is distance-optimal exactly when its cost equals the dual
value supplied by the witness. -/
theorem isDistanceOptimal_iff_distanceCost_eq
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} (w : DistanceDualWitness mu nu)
    (gamma : FiniteCoupling mu nu) :
    IsDistanceOptimal gamma <->
      distanceCost gamma =
        finiteMarginalPotentialDifference mu nu w.potential := by
  constructor
  · rintro ⟨-, hGamma⟩
    obtain ⟨eta, hEta⟩ := w.minimum.1
    apply le_antisymm
    · calc
        distanceCost gamma <= distanceCost eta :=
          hGamma eta (mem_univ eta)
        _ = finiteMarginalPotentialDifference mu nu w.potential := hEta
    · exact w.minimum.2 ⟨gamma, rfl⟩
  · intro hGamma
    refine ⟨mem_univ gamma, ?_⟩
    intro eta _hEta
    change distanceCost gamma <= distanceCost eta
    rw [hGamma]
    exact w.minimum.2 ⟨eta, rfl⟩

/-- Conditional contact-set characterization. Once a dual witness is
supplied, no further duality or optimizer-existence result is needed. -/
theorem isDistanceOptimal_iff_isSupported
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (w : DistanceDualWitness mu nu)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (gamma : FiniteCoupling mu nu) :
    IsDistanceOptimal gamma <->
      IsSupported gamma (distanceContactSet w.potential) := by
  exact
    (w.isDistanceOptimal_iff_distanceCost_eq gamma).trans
      (distanceCost_eq_finiteMarginalPotentialDifference_iff_isSupported
        w.potential w.lipschitz hSourceMoment hTargetMoment gamma)

/-- The contact set of a `DistanceDualWitness` is distance-cyclically
monotone. -/
theorem contactSetIsDistanceCyclicallyMonotone
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} (w : DistanceDualWitness mu nu) :
    IsDistanceCyclicallyMonotone
      (distanceContactSet w.potential) := by
  classical
  have hDifferenceLeDistance (x y : E) :
      w.potential x - w.potential y <= dist x y := by
    apply sub_le_iff_le_add'.2
    simpa using w.lipschitz.le_add_mul x y
  intro I _ x y hContact sigma
  calc
    (∑ i, dist (x i) (y i)) =
        ∑ i, (w.potential (x i) - w.potential (y i)) := by
      apply Fintype.sum_congr
      intro i
      exact hContact i
    _ = (∑ i, w.potential (x i)) -
        ∑ i, w.potential (y i) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, w.potential (x i)) -
        ∑ i, w.potential (y (sigma i)) := by
      congr 1
      exact
        (Equiv.sum_comp sigma fun i => w.potential (y i)).symm
    _ = ∑ i,
        (w.potential (x i) - w.potential (y (sigma i))) := by
      rw [Finset.sum_sub_distrib]
    _ <= ∑ i, dist (x i) (y (sigma i)) := by
      exact Finset.sum_le_sum fun i _ =>
        hDifferenceLeDistance (x i) (y (sigma i))

end DistanceDualWitness

/-- Equal finite masses have at least one finite coupling, including at
zero mass. -/
theorem nonemptyFiniteCouplingOfEqualMass
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass) :
    Nonempty (FiniteCoupling mu nu) := by
  by_cases hZero : mu.mass = 0
  · have hMu : mu = 0 := (FiniteMeasure.mass_zero_iff mu).mp hZero
    have hNuMass : nu.mass = 0 := by
      rw [← hMass]
      exact hZero
    have hNu : nu = 0 := (FiniteMeasure.mass_zero_iff nu).mp hNuMass
    subst mu
    subst nu
    refine ⟨⟨0, ?_⟩⟩
    constructor
    · change FiniteMeasure.map 0 Prod.fst = 0
      ext s hs
      simp
    · change FiniteMeasure.map 0 Prod.snd = 0
      ext s hs
      simp
  · exact
      nonempty_finiteCoupling_of_equal_positive_mass
        mu nu hMass (pos_of_ne_zero hZero)

/-- Under finite first moments, the distance cost attains its minimum on the
equal-mass coupling space. This is primal compactness, not transport
duality. -/
theorem existsDistanceOptimal
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    exists gamma : FiniteCoupling mu nu, IsDistanceOptimal gamma := by
  obtain ⟨gammaZero⟩ :=
    nonemptyFiniteCouplingOfEqualMass n mu nu hMass
  by_cases hZero : mu.mass = 0
  · refine ⟨gammaZero, mem_univ gammaZero, ?_⟩
    intro eta _hEta
    have hGammaPlan :
        gammaZero.plan = 0 :=
      (zeroMassFiniteCouplingPlan gammaZero hZero).2.2
    have hEtaPlan :
        eta.plan = 0 :=
      (zeroMassFiniteCouplingPlan eta hZero).2.2
    simp [profileCost, hGammaPlan, hEtaPlan]
  · have hPositive : 0 < mu.mass := pos_of_ne_zero hZero
    have hIntegrandLower :
        LowerSemicontinuous
          (fun z : Euclidean n × Euclidean n => ‖z.1 - z.2‖) :=
      ((continuous_fst.sub continuous_snd).norm).lowerSemicontinuous
    have hCostLower :
        LowerSemicontinuous
          (distanceCost : FiniteCoupling mu nu -> Real) := by
      simpa [distanceCost] using
        (profileCost_lowerSemicontinuous_of_nonnegative
          (profile := id) hPositive hIntegrandLower
          (fun {r} hr => hr)
          (fun gamma =>
            distanceIntegrableOfMarginalFirstMoments
              hSourceMoment hTargetMoment gamma))
    obtain ⟨gamma, _hGammaMem, hGammaMin⟩ :=
      (hCostLower.lowerSemicontinuousOn Set.univ).exists_isMinOn
        ⟨gammaZero, mem_univ gammaZero⟩
        (finiteCouplingIsCompact mu nu)
    refine ⟨gamma, _hGammaMem, ?_⟩
    intro eta hEta
    change distanceCost gamma <= distanceCost eta
    exact (isMinOn_iff.mp hGammaMin) eta hEta

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

private theorem secondMarginal_fintypeSum
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

private theorem normalizedFiniteMeasure_mass
    {Omega : Type*} [MeasurableSpace Omega] [Nonempty Omega]
    (rho : FiniteMeasure Omega) :
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

private theorem crossProduct_mem_prod_ball
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    [OpensMeasurableSpace E]
    (rho sigma : FiniteMeasure (E × E))
    (x y : E) (r : Real)
    (hRho :
      ∀ᵐ z ∂(rho : Measure (E × E)), z.1 ∈ Metric.ball x r)
    (hSigma :
      ∀ᵐ z ∂(sigma : Measure (E × E)), z.2 ∈ Metric.ball y r) :
    ∀ᵐ z ∂(((firstMarginal rho).prod
        (secondMarginal sigma) : FiniteMeasure (E × E)) :
      Measure (E × E)),
      z.1 ∈ Metric.ball x r ∧ z.2 ∈ Metric.ball y r := by
  have hFirst :
      ∀ᵐ a ∂(firstMarginal rho : Measure E),
        a ∈ Metric.ball x r := by
    rw [firstMarginal, FiniteMeasure.toMeasure_map]
    exact
      (ae_map_iff measurable_fst.aemeasurable measurableSet_ball).2
        hRho
  have hSecond :
      ∀ᵐ b ∂(secondMarginal sigma : Measure E),
        b ∈ Metric.ball y r := by
    rw [secondMarginal, FiniteMeasure.toMeasure_map]
    exact
      (ae_map_iff measurable_snd.aemeasurable measurableSet_ball).2
        hSigma
  rw [FiniteMeasure.toMeasure_prod]
  apply
    (Measure.ae_prod_iff_ae_ae
      (measurableSet_ball.prod measurableSet_ball)).2
  filter_upwards [hFirst] with a ha
  filter_upwards [hSecond] with b hb
  exact ⟨ha, hb⟩

/-- The expected distance under a unit-mass measure carried by a product of
two balls differs from the distance between their centers by at most twice
the radius. -/
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
    {n : Nat}
    (rho : FiniteMeasure (Euclidean n × Euclidean n))
    (x y : Euclidean n) (r : Real)
    (hSupported :
      ∀ᵐ z ∂(rho : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ Metric.ball x r ∧ z.2 ∈ Metric.ball y r) :
    Integrable (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
      (rho : Measure (Euclidean n × Euclidean n)) := by
  apply Integrable.of_bound (by fun_prop) (dist x y + 2 * r)
  filter_upwards [hSupported] with z hz
  have hx : dist z.1 x < r := Metric.mem_ball.mp hz.1
  have hyBall : dist z.2 y < r := Metric.mem_ball.mp hz.2
  have hy : dist y z.2 < r := by
    simpa [dist_comm] using hyBall
  have hTriangle :
      dist z.1 z.2 <= dist z.1 x + dist x y + dist y z.2 := by
    calc
      dist z.1 z.2 <= dist z.1 x + dist x z.2 :=
        dist_triangle _ _ _
      _ <= dist z.1 x + (dist x y + dist y z.2) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  linarith

/-- The topological support of a distance-optimal finite coupling is
distance-cyclically monotone. The proof replaces small normalized pieces
around a purported violating cycle by cyclically rerouted products. -/
theorem distanceOptimalSupport_isDistanceCyclicallyMonotone
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
  by_contra hCycle
  have hStrict :
      (∑ i, dist (x i) (y (sigma i))) <
        ∑ i, dist (x i) (y i) :=
    lt_of_not_ge hCycle
  have hNonempty : Nonempty I := by
    by_contra hEmpty
    letI : IsEmpty I := not_nonempty_iff.mp hEmpty
    simpa using hStrict
  letI : Nonempty I := hNonempty
  let gap : Real :=
    (∑ i, dist (x i) (y i)) -
      ∑ i, dist (x i) (y (sigma i))
  have hGapPos : 0 < gap := by
    exact sub_pos.mpr hStrict
  have hCardPos : 0 < (Fintype.card I : Real) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hNonempty)
  let r : Real := gap / (8 * (Fintype.card I : Real))
  have hRPos : 0 < r := by
    exact div_pos hGapPos (mul_pos (by norm_num) hCardPos)
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
  let U : I -> Set (Euclidean n × Euclidean n) :=
    fun i => Metric.ball (x i) r ×ˢ Metric.ball (y i) r
  have hUOpen (i : I) : IsOpen (U i) := by
    exact Metric.isOpen_ball.prod Metric.isOpen_ball
  have hUMeasurable (i : I) : MeasurableSet (U i) :=
    (hUOpen i).measurableSet
  have hCenter (i : I) : (x i, y i) ∈ U i := by
    exact ⟨Metric.mem_ball_self hRPos, Metric.mem_ball_self hRPos⟩
  have hBlockMeasurePositive (i : I) :
      0 < (gamma.plan : Measure (Euclidean n × Euclidean n)) (U i) := by
    exact
      (Measure.mem_support_iff_forall (x i, y i)).mp (hSupport i)
        (U i) ((hUOpen i).mem_nhds (hCenter i))
  have hBlockPositive (i : I) : 0 < gamma.plan (U i) := by
    apply pos_iff_ne_zero.mpr
    intro hZero
    have hMeasureZero :
        (gamma.plan : Measure (Euclidean n × Euclidean n)) (U i) = 0 :=
      (FiniteMeasure.null_iff_toMeasure_null gamma.plan (U i)).mp hZero
    exact (ne_of_gt (hBlockMeasurePositive i)) hMeasureZero
  let raw : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
    fun i => gamma.plan.restrict (U i)
  have hRawPositive (i : I) : 0 < (raw i).mass := by
    simpa only [raw, FiniteMeasure.restrict_mass] using hBlockPositive i
  have hRawNe (i : I) : raw i ≠ 0 :=
    (FiniteMeasure.mass_nonzero_iff (raw i)).mp
      (ne_of_gt (hRawPositive i))
  let rho : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
    fun i => (raw i).normalize.toFiniteMeasure
  have hRhoMass (i : I) : (rho i).mass = 1 := by
    exact normalizedFiniteMeasure_mass (raw i)
  have hRhoEq (i : I) :
      rho i = (raw i).mass⁻¹ • raw i := by
    exact
      FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero
        (raw i) (hRawNe i)
  have hRhoSupported (i : I) :
      ∀ᵐ z ∂(rho i : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ Metric.ball (x i) r ∧ z.2 ∈ Metric.ball (y i) r := by
    simpa only [rho, raw, U] using
      normalizedRestriction_mem_ae gamma.plan (U i)
        (hUMeasurable i) (by
          simpa only [raw] using hRawNe i)
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
      (rho i : Measure (Euclidean n × Euclidean n)) <=
        (raw i).mass⁻¹ •
          (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
    have hRawLe :
        (raw i : Measure (Euclidean n × Euclidean n)) <=
          (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
      dsimp only [raw]
      exact Measure.restrict_le_self
    rw [hRhoEq i, FiniteMeasure.toMeasure_smul]
    intro s
    simp only [Measure.coe_nnreal_smul_apply]
    exact mul_le_mul_left' (hRawLe s) _
  have hRhoSumLe :
      ((∑ i, rho i : FiniteMeasure
          (Euclidean n × Euclidean n)) :
        Measure (Euclidean n × Euclidean n)) <=
      weight •
        (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
    rw [FiniteMeasure.toMeasure_sum]
    calc
      (∑ i, (rho i :
          Measure (Euclidean n × Euclidean n))) <=
          ∑ i, (raw i).mass⁻¹ •
            (gamma.plan :
              Measure (Euclidean n × Euclidean n)) :=
        Finset.sum_le_sum fun i _ => hRhoLe i
      _ = weight •
          (gamma.plan :
            Measure (Euclidean n × Euclidean n)) := by
        rw [← Finset.sum_smul]
  let tau : I -> FiniteMeasure (Euclidean n × Euclidean n) :=
    fun i =>
      (firstMarginal (rho i)).prod
        (secondMarginal (rho (sigma i)))
  have hTauMass (i : I) : (tau i).mass = 1 := by
    dsimp only [tau]
    rw [FiniteMeasure.mass_prod, firstMarginal_mass_eq,
      secondMarginal_mass_eq, hRhoMass, hRhoMass]
    simp
  have hTauSupported (i : I) :
      ∀ᵐ z ∂(tau i : Measure (Euclidean n × Euclidean n)),
        z.1 ∈ Metric.ball (x i) r ∧
          z.2 ∈ Metric.ball (y (sigma i)) r := by
    dsimp only [tau]
    apply crossProduct_mem_prod_ball
    · exact (hRhoSupported i).mono fun z hz => hz.1
    · exact
        (hRhoSupported (sigma i)).mono fun z hz => hz.2
  let removed : FiniteMeasure (Euclidean n × Euclidean n) :=
    c • ∑ i, rho i
  let added : FiniteMeasure (Euclidean n × Euclidean n) :=
    c • ∑ i, tau i
  have hRemovedLe :
      (removed : Measure (Euclidean n × Euclidean n)) <=
        (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
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
          ((∑ i, rho i : FiniteMeasure
            (Euclidean n × Euclidean n)) :
            Measure (Euclidean n × Euclidean n)) s <=
          (c : ENNReal) *
            ((weight : ENNReal) *
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)) s) :=
        mul_le_mul_left' hs _
      _ = (gamma.plan :
          Measure (Euclidean n × Euclidean n)) s := by
        rw [← mul_assoc, hCWeightENN, one_mul]
  have hFirstBase :
      firstMarginal (∑ i, tau i) =
        firstMarginal (∑ i, rho i) := by
    rw [firstMarginal_fintypeSum, firstMarginal_fintypeSum]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [tau]
    rw [firstMarginal_crossProduct, hRhoMass]
    simp
  have hSecondBase :
      secondMarginal (∑ i, tau i) =
        secondMarginal (∑ i, rho i) := by
    rw [secondMarginal_fintypeSum, secondMarginal_fintypeSum]
    calc
      (∑ i, secondMarginal (tau i)) =
          ∑ i, secondMarginal (rho (sigma i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp only [tau]
        rw [secondMarginal_crossProduct, hRhoMass]
        simp
      _ = ∑ i, secondMarginal (rho i) :=
        Equiv.sum_comp sigma fun i => secondMarginal (rho i)
  have hFirst :
      firstMarginal added = firstMarginal removed := by
    dsimp only [added, removed]
    simpa only [firstMarginal, FiniteMeasure.map_smul] using
      congrArg
        (fun eta : FiniteMeasure (Euclidean n) => c • eta)
        hFirstBase
  have hSecond :
      secondMarginal added = secondMarginal removed := by
    dsimp only [added, removed]
    simpa only [secondMarginal, FiniteMeasure.map_smul] using
      congrArg
        (fun eta : FiniteMeasure (Euclidean n) => c • eta)
        hSecondBase
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
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (rho i : Measure (Euclidean n × Euclidean n)) :=
    integrableDistance_of_mem_prod_ball
      (rho i) (x i) (y i) r (hRhoSupported i)
  have hTauIntegrable (i : I) :
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (tau i : Measure (Euclidean n × Euclidean n)) :=
    integrableDistance_of_mem_prod_ball
      (tau i) (x i) (y (sigma i)) r (hTauSupported i)
  have hRhoBounds (i : I) :
      dist (x i) (y i) - 2 * r <=
          ∫ z, dist z.1 z.2
            ∂(rho i : Measure (Euclidean n × Euclidean n)) ∧
        (∫ z, dist z.1 z.2
            ∂(rho i : Measure (Euclidean n × Euclidean n))) <=
          dist (x i) (y i) + 2 * r :=
    integralDistance_mem_prod_ball_bounds
      (rho i) (x i) (y i) r (hRhoMass i)
        (hRhoSupported i) (hRhoIntegrable i)
  have hTauBounds (i : I) :
      dist (x i) (y (sigma i)) - 2 * r <=
          ∫ z, dist z.1 z.2
            ∂(tau i : Measure (Euclidean n × Euclidean n)) ∧
        (∫ z, dist z.1 z.2
            ∂(tau i : Measure (Euclidean n × Euclidean n))) <=
          dist (x i) (y (sigma i)) + 2 * r :=
    integralDistance_mem_prod_ball_bounds
      (tau i) (x i) (y (sigma i)) r (hTauMass i)
        (hTauSupported i) (hTauIntegrable i)
  have hBaseCheaper :
      (∑ i, ∫ z, dist z.1 z.2
          ∂(tau i : Measure (Euclidean n × Euclidean n))) <
        ∑ i, ∫ z, dist z.1 z.2
          ∂(rho i : Measure (Euclidean n × Euclidean n)) := by
    calc
      (∑ i, ∫ z, dist z.1 z.2
          ∂(tau i : Measure (Euclidean n × Euclidean n))) <=
          ∑ i, (dist (x i) (y (sigma i)) + 2 * r) :=
        Finset.sum_le_sum fun i _ => (hTauBounds i).2
      _ < ∑ i, (dist (x i) (y i) - 2 * r) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp only [gap] at hError
        linarith
      _ <= ∑ i, ∫ z, dist z.1 z.2
          ∂(rho i : Measure (Euclidean n × Euclidean n)) :=
        Finset.sum_le_sum fun i _ => (hRhoBounds i).1
  have hTauSumIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        ((∑ i, tau i : FiniteMeasure
            (Euclidean n × Euclidean n)) :
          Measure (Euclidean n × Euclidean n)) := by
    rw [FiniteMeasure.toMeasure_sum]
    apply integrable_finsetSum_measure.2
    intro i _hi
    exact hTauIntegrable i
  have hAddedIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (added : Measure (Euclidean n × Euclidean n)) := by
    dsimp only [added]
    rw [FiniteMeasure.toMeasure_smul]
    exact hTauSumIntegrable.smul_measure_nnreal
  have hGammaIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (gamma.plan : Measure (Euclidean n × Euclidean n)) := by
    simpa only [dist_eq_norm] using
      distanceIntegrableOfMarginalFirstMoments
        hSourceMoment hTargetMoment gamma
  have hRemovedIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (removed : Measure (Euclidean n × Euclidean n)) :=
    hGammaIntegrable.mono_measure hRemovedLe
  have hRemainderIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n => dist z.1 z.2)
        (remainder : Measure (Euclidean n × Euclidean n)) :=
    hGammaIntegrable.mono_measure hRemainderLe
  have hTauSumIntegral :
      (∫ z, dist z.1 z.2
          ∂((∑ i, tau i : FiniteMeasure
              (Euclidean n × Euclidean n)) :
            Measure (Euclidean n × Euclidean n))) =
        ∑ i, ∫ z, dist z.1 z.2
          ∂(tau i : Measure (Euclidean n × Euclidean n)) := by
    rw [FiniteMeasure.toMeasure_sum]
    exact integral_finsetSum_measure fun i _hi => hTauIntegrable i
  have hRhoSumIntegral :
      (∫ z, dist z.1 z.2
          ∂((∑ i, rho i : FiniteMeasure
              (Euclidean n × Euclidean n)) :
            Measure (Euclidean n × Euclidean n))) =
        ∑ i, ∫ z, dist z.1 z.2
          ∂(rho i : Measure (Euclidean n × Euclidean n)) := by
    rw [FiniteMeasure.toMeasure_sum]
    exact integral_finsetSum_measure fun i _hi => hRhoIntegrable i
  have hScaledCheaper :
      (∫ z, dist z.1 z.2
          ∂(added : Measure (Euclidean n × Euclidean n))) <
        ∫ z, dist z.1 z.2
          ∂(removed : Measure (Euclidean n × Euclidean n)) := by
    dsimp only [added, removed]
    rw [FiniteMeasure.toMeasure_smul,
      FiniteMeasure.toMeasure_smul,
      integral_smul_nnreal_measure,
      integral_smul_nnreal_measure,
      hTauSumIntegral, hRhoSumIntegral]
    simpa only [NNReal.smul_def] using
      mul_lt_mul_of_pos_left hBaseCheaper
        (by exact_mod_cast hCPos : (0 : Real) < c)
  have hEtaLt : distanceCost eta < distanceCost gamma := by
    have hProfileLt :=
      profileCostReroutingLtOfAddedLtRemoved
        (profile := id) (gamma := gamma) (eta := eta)
        hDecomposition.symm rfl
        (by
          simpa only [id_eq, dist_eq_norm] using hRemainderIntegrable)
        (by
          simpa only [id_eq, dist_eq_norm] using hRemovedIntegrable)
        (by
          simpa only [id_eq, dist_eq_norm] using hAddedIntegrable)
        (by
          simpa only [id_eq, dist_eq_norm] using hScaledCheaper)
    exact hProfileLt
  exact
    (not_lt_of_ge (hOptimal.2 eta (mem_univ eta))) hEtaLt

/-- At zero common mass the distance dual witness is explicit, so no duality
theorem is needed. -/
theorem nonemptyDistanceDualWitnessOfMassZero
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hZero : mu.mass = 0) :
    Nonempty (DistanceDualWitness mu nu) := by
  obtain ⟨gammaZero⟩ :=
    nonemptyFiniteCouplingOfEqualMass n mu nu hMass
  have hCostZero :
      forall gamma : FiniteCoupling mu nu, distanceCost gamma = 0 := by
    intro gamma
    have hPlan : gamma.plan = 0 :=
      (zeroMassFiniteCouplingPlan gamma hZero).2.2
    simp [distanceCost, profileCost, hPlan]
  let u : Euclidean n -> Real := fun _ => 0
  have hu : LipschitzWith 1 u :=
    (LipschitzWith.const (0 : Real)).weaken zero_le
  have hDifference :
      finiteMarginalPotentialDifference mu nu u = 0 := by
    simp [finiteMarginalPotentialDifference, u]
  refine ⟨{
    potential := u
    lipschitz := hu
    minimum := ?_
  }⟩
  refine ⟨⟨gammaZero, ?_⟩, ?_⟩
  · rw [hCostZero gammaZero, hDifference]
  · rintro value ⟨gamma, rfl⟩
    rw [hDifference, hCostZero gamma]

/-- The one-sided inequality not supplied by weak duality. Its witness is
already an attained dual potential; weak duality forces equality. -/
def DistanceKantorovichRubinsteinReverseInequality
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n)) : Prop :=
  exists u : Euclidean n -> Real,
    LipschitzWith 1 u /\
      minimalDistanceCost mu nu <=
        finiteMarginalPotentialDifference mu nu u

/-- The non-attained form of the reverse Kantorovich-Rubinstein inequality:
dual potentials can approach the primal value arbitrarily closely. -/
def DistanceKantorovichRubinsteinApproximateReverseInequality
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n)) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        minimalDistanceCost mu nu <=
          finiteMarginalPotentialDifference mu nu u + epsilon

/-- Finite first moments make normalized `1`-Lipschitz potentials compact,
so approximate reverse duality automatically attains its limiting value. -/
theorem reverseKantorovichRubinstein_iff_approximateReverse
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    DistanceKantorovichRubinsteinReverseInequality n mu nu <->
      DistanceKantorovichRubinsteinApproximateReverseInequality n mu nu := by
  constructor
  · rintro ⟨u, hu, hReverse⟩ epsilon hEpsilon
    refine ⟨u, hu, ?_⟩
    exact hReverse.trans (le_add_of_nonneg_right hEpsilon.le)
  · intro hApproximate
    let epsilon : Nat -> Real :=
      fun k => 1 / ((k : Real) + 1)
    have hEpsilonPositive (k : Nat) : 0 < epsilon k := by
      dsimp only [epsilon]
      positivity
    choose potential hPotential using
      fun k => hApproximate (epsilon k) (hEpsilonPositive k)
    have hPotentialLipschitz (k : Nat) :
        LipschitzWith 1 (potential k) :=
      (hPotential k).1
    have hPotentialReverse (k : Nat) :
        minimalDistanceCost mu nu <=
          finiteMarginalPotentialDifference mu nu (potential k) +
            epsilon k :=
      (hPotential k).2
    let normalized : Nat -> C(Euclidean n, Real) :=
      fun k =>
        ⟨fun x => potential k x - potential k 0,
          (hPotentialLipschitz k).continuous.sub continuous_const⟩
    have hNormalized (k : Nat) :
        normalized k ∈ normalizedDistancePotentials n := by
      constructor
      · refine LipschitzWith.of_dist_le_mul ?_
        intro x y
        simpa [normalized] using
          (hPotentialLipschitz k).dist_le_mul x y
      · simp [normalized]
    have hPotentialSourceIntegrable (k : Nat) :
        Integrable (potential k) (mu : Measure (Euclidean n)) :=
      DistanceDualWitness.integrablePotentialOfLipschitz
        (potential k) (hPotentialLipschitz k) hSourceMoment
    have hPotentialTargetIntegrable (k : Nat) :
        Integrable (potential k) (nu : Measure (Euclidean n)) :=
      DistanceDualWitness.integrablePotentialOfLipschitz
        (potential k) (hPotentialLipschitz k) hTargetMoment
    have hNormalizedDifference (k : Nat) :
        finiteMarginalPotentialDifference mu nu (normalized k) =
          finiteMarginalPotentialDifference mu nu (potential k) := by
      simpa only [normalized, ContinuousMap.coe_mk] using
        DistanceDualWitness.finiteMarginalPotentialDifference_sub_const
          (potential k) (hPotentialSourceIntegrable k)
          (hPotentialTargetIntegrable k) hMass (potential k 0)
    obtain ⟨limit, hLimit, subsequence, hSubsequence,
        hConverges⟩ :=
      (normalizedDistancePotentials_isCompact n).tendsto_subseq
        hNormalized
    have hPointwise (x : Euclidean n) :
        Tendsto (fun k => normalized (subsequence k) x)
          atTop (nhds (limit x)) := by
      simpa only [Function.comp_apply] using
        (continuous_eval_const x).continuousAt.tendsto.comp hConverges
    have hNormalizedBound (k : Nat) (x : Euclidean n) :
        ‖normalized k x‖ <= ‖x‖ := by
      have hx :=
        (hNormalized k).1.dist_le_mul x 0
      simpa [(hNormalized k).2, Real.dist_eq, dist_eq_norm] using hx
    have hSourceIntegralConverges :
        Tendsto
          (fun k =>
            ∫ x, normalized (subsequence k) x
              ∂(mu : Measure (Euclidean n)))
          atTop
          (nhds
            (∫ x, limit x ∂(mu : Measure (Euclidean n)))) := by
      apply
        tendsto_integral_of_dominated_convergence
          (fun x : Euclidean n => ‖x‖)
      · exact fun k =>
          (normalized (subsequence k)).continuous.aestronglyMeasurable
      · exact hSourceMoment
      · exact fun k =>
          Filter.Eventually.of_forall fun x =>
            hNormalizedBound (subsequence k) x
      · exact Filter.Eventually.of_forall hPointwise
    have hTargetIntegralConverges :
        Tendsto
          (fun k =>
            ∫ x, normalized (subsequence k) x
              ∂(nu : Measure (Euclidean n)))
          atTop
          (nhds
            (∫ x, limit x ∂(nu : Measure (Euclidean n)))) := by
      apply
        tendsto_integral_of_dominated_convergence
          (fun x : Euclidean n => ‖x‖)
      · exact fun k =>
          (normalized (subsequence k)).continuous.aestronglyMeasurable
      · exact hTargetMoment
      · exact fun k =>
          Filter.Eventually.of_forall fun x =>
            hNormalizedBound (subsequence k) x
      · exact Filter.Eventually.of_forall hPointwise
    have hDifferenceConverges :
        Tendsto
          (fun k =>
            finiteMarginalPotentialDifference mu nu
              (normalized (subsequence k)))
          atTop
          (nhds
            (finiteMarginalPotentialDifference mu nu limit)) := by
      simpa [finiteMarginalPotentialDifference] using
        hSourceIntegralConverges.sub hTargetIntegralConverges
    have hEpsilonConverges :
        Tendsto epsilon atTop (nhds 0) := by
      simpa [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : Nat => (1 : Real) / (k + 1))
            atTop (nhds 0))
    have hRightConverges :
        Tendsto
          (fun k =>
            finiteMarginalPotentialDifference mu nu
                (normalized (subsequence k)) +
              epsilon (subsequence k))
          atTop
          (nhds
            (finiteMarginalPotentialDifference mu nu limit)) := by
      convert
        hDifferenceConverges.add
          (hEpsilonConverges.comp hSubsequence.tendsto_atTop) using 1
      simp
    refine ⟨limit, hLimit.1, ?_⟩
    apply ge_of_tendsto' hRightConverges
    intro k
    calc
      minimalDistanceCost mu nu <=
          finiteMarginalPotentialDifference mu nu
              (potential (subsequence k)) +
            epsilon (subsequence k) :=
        hPotentialReverse (subsequence k)
      _ =
          finiteMarginalPotentialDifference mu nu
              (normalized (subsequence k)) +
            epsilon (subsequence k) := by
        rw [hNormalizedDifference]

/-- A distance dual witness is equivalent to the missing reverse
Kantorovich-Rubinstein inequality. Primal attainment and the opposite
inequality are discharged from the stated hypotheses. -/
theorem nonemptyDistanceDualWitness_iff_reverseKantorovichRubinstein
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    Nonempty (DistanceDualWitness mu nu) <->
      DistanceKantorovichRubinsteinReverseInequality n mu nu := by
  constructor
  · rintro ⟨w⟩
    refine ⟨w.potential, w.lipschitz, ?_⟩
    unfold minimalDistanceCost
    exact w.minimum.csInf_eq.le
  · rintro ⟨u, hu, hReverse⟩
    obtain ⟨gamma, hGammaOptimal⟩ :=
      existsDistanceOptimal n mu nu hMass
        hSourceMoment hTargetMoment
    have hGammaLeast :
        IsLeast
          (Set.range
            (distanceCost : FiniteCoupling mu nu -> Real))
          (distanceCost gamma) := by
      refine ⟨⟨gamma, rfl⟩, ?_⟩
      rintro value ⟨eta, rfl⟩
      exact hGammaOptimal.2 eta (mem_univ eta)
    have hMinimumEq :
        minimalDistanceCost mu nu = distanceCost gamma := by
      exact hGammaLeast.csInf_eq
    have hWeak :
        finiteMarginalPotentialDifference mu nu u <= distanceCost gamma :=
      DistanceDualWitness.finiteMarginalPotentialDifference_le_distanceCost
        u hu hSourceMoment hTargetMoment gamma
    have hGammaEq :
        distanceCost gamma =
          finiteMarginalPotentialDifference mu nu u := by
      apply le_antisymm
      · rw [← hMinimumEq]
        exact hReverse
      · exact hWeak
    refine ⟨{
      potential := u
      lipschitz := hu
      minimum := ?_
    }⟩
    refine ⟨⟨gamma, hGammaEq⟩, ?_⟩
    rintro value ⟨eta, rfl⟩
    exact
      DistanceDualWitness.finiteMarginalPotentialDifference_le_distanceCost
        u hu hSourceMoment hTargetMoment eta

/-- The exact witness boundary can be stated without any attainment
assumption: it is equivalent to the epsilon-level reverse inequality. -/
theorem nonemptyDistanceDualWitness_iff_approximateReverseKantorovichRubinstein
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    Nonempty (DistanceDualWitness mu nu) <->
      DistanceKantorovichRubinsteinApproximateReverseInequality n mu nu :=
  (nonemptyDistanceDualWitness_iff_reverseKantorovichRubinstein
      n mu nu hMass hSourceMoment hTargetMoment).trans
    (reverseKantorovichRubinstein_iff_approximateReverse
      n mu nu hMass hSourceMoment hTargetMoment)

/-- Equivalently, the entire dual boundary is the existence of one coupling
concentrated on one `1`-Lipschitz distance contact set. -/
theorem nonemptyDistanceDualWitness_iff_existsContactCoupling
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    Nonempty (DistanceDualWitness mu nu) <->
      exists (u : Euclidean n -> Real) (gamma : FiniteCoupling mu nu),
        LipschitzWith 1 u /\
          IsSupported gamma (distanceContactSet u) := by
  constructor
  · rintro ⟨w⟩
    obtain ⟨gamma, hGammaEq⟩ := w.minimum.1
    refine ⟨w.potential, gamma, w.lipschitz, ?_⟩
    exact
      (DistanceDualWitness.distanceCost_eq_finiteMarginalPotentialDifference_iff_isSupported
          w.potential w.lipschitz hSourceMoment hTargetMoment gamma).mp
        hGammaEq
  · rintro ⟨u, gamma, hu, hContact⟩
    have hGammaEq :
        distanceCost gamma =
          finiteMarginalPotentialDifference mu nu u :=
      (DistanceDualWitness.distanceCost_eq_finiteMarginalPotentialDifference_iff_isSupported
          u hu hSourceMoment hTargetMoment gamma).mpr hContact
    refine ⟨{
      potential := u
      lipschitz := hu
      minimum := ?_
    }⟩
    refine ⟨⟨gamma, hGammaEq⟩, ?_⟩
    rintro value ⟨eta, rfl⟩
    exact
      DistanceDualWitness.finiteMarginalPotentialDifference_le_distanceCost
        u hu hSourceMoment hTargetMoment eta

universe u v

/-- Cyclic monotonicity over any universe of finite index types implies the
`Type 0` instance needed by the finite-chain construction. -/
private theorem isDistanceCyclicallyMonotone_universeZero
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, v} Gamma) :
    IsDistanceCyclicallyMonotone.{u, 0} Gamma := by
  intro I _ x y hxy sigma
  let e : ULift.{v} I ≃ I := Equiv.ulift
  let sigma' : Equiv.Perm (ULift.{v} I) :=
    e.trans sigma |>.trans e.symm
  have hCycle :=
    hCyclic
      (fun i => x (e i)) (fun i => y (e i))
      (fun i => hxy (e i)) sigma'
  calc
    (∑ i, dist (x i) (y i)) =
        ∑ i : ULift.{v} I, dist (x (e i)) (y (e i)) :=
      (Equiv.sum_comp e fun i => dist (x i) (y i)).symm
    _ <= ∑ i : ULift.{v} I,
        dist (x (e i)) (y (e (sigma' i))) :=
      hCycle
    _ = ∑ i : ULift.{v} I,
        dist (x (e i)) (y (sigma (e i))) := by
      apply Fintype.sum_congr
      intro i
      rfl
    _ = ∑ i, dist (x i) (y (sigma i)) :=
      Equiv.sum_comp e fun i => dist (x i) (y (sigma i))

/-- The cost of a nonempty finite chain used to construct a distance contact
potential from a cyclically monotone carrier. -/
private def dualFiniteDistanceChainCost
    {E : Type u} [PseudoMetricSpace E] {n : Nat}
    (a z : E) (p : Fin (n + 1) -> E × E) : Real :=
  dist a (p 0).1 +
      (∑ i : Fin n,
        dist (p i.succ).1 (p i.castSucc).2) -
    (∑ i : Fin (n + 1), dist (p i).1 (p i).2) +
    dist (p (Fin.last n)).2 z

private theorem dualFiniteDistanceChainCost_snoc
    {E : Type u} [PseudoMetricSpace E] {n : Nat}
    (a z : E) (p : Fin (n + 1) -> E × E) (q : E × E) :
    dualFiniteDistanceChainCost a z (Fin.snoc p q) =
      dualFiniteDistanceChainCost a q.1 p -
        dist q.1 q.2 + dist q.2 z := by
  have hLinks :
      (∑ i : Fin (n + 1),
          dist
            ((Fin.snoc p q : Fin (n + 2) -> E × E) i.succ).1
            ((Fin.snoc p q : Fin (n + 2) -> E × E) i.castSucc).2) =
        (∑ i : Fin n, dist (p i.succ).1 (p i.castSucc).2) +
          dist q.1 (p (Fin.last n)).2 := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Fintype.sum_congr
      intro i
      rw [← Fin.castSucc_succ i, Fin.snoc_castSucc,
        Fin.snoc_castSucc]
    · simp
  have hEdges :
      (∑ i : Fin (n + 2),
          dist
            ((Fin.snoc p q : Fin (n + 2) -> E × E) i).1
            ((Fin.snoc p q : Fin (n + 2) -> E × E) i).2) =
        (∑ i : Fin (n + 1), dist (p i).1 (p i).2) +
          dist q.1 q.2 := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Fintype.sum_congr
      intro i
      simp
    · simp
  simp only [dualFiniteDistanceChainCost]
  rw [hLinks, hEdges]
  rw [dist_comm q.1 (p (Fin.last n)).2]
  simp
  ring

private theorem dualFiniteDistanceChainCost_terminal_le
    {E : Type u} [PseudoMetricSpace E] {n : Nat}
    (a z z' : E) (p : Fin (n + 1) -> E × E) :
    dualFiniteDistanceChainCost a z' p <=
      dualFiniteDistanceChainCost a z p + dist z z' := by
  unfold dualFiniteDistanceChainCost
  linarith [dist_triangle (p (Fin.last n)).2 z z']

private theorem dualFiniteDistanceChainCost_lower
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    {n : Nat} (a z : E) (p : Fin (n + 1) -> E × E)
    (hp : ∀ i, p i ∈ Gamma) :
    -dist a z <= dualFiniteDistanceChainCost a z p := by
  let sigma : Equiv.Perm (Fin (n + 1)) :=
    (Fin.cycleRange (Fin.last n)).symm
  have hCycle :=
    hCyclic (I := Fin (n + 1))
      (fun i => (p i).1) (fun i => (p i).2) hp sigma
  have hSigmaZero : sigma 0 = Fin.last n := by
    exact Fin.cycleRange_symm_zero (Fin.last n)
  have hSigmaSucc (i : Fin n) :
      sigma i.succ = i.castSucc := by
    exact
      (Fin.cycleRange_symm_succ (Fin.last n) i).trans
        (Fin.succAbove_last_apply i)
  have hCross :
      (∑ i : Fin (n + 1), dist (p i).1 (p (sigma i)).2) =
        dist (p 0).1 (p (Fin.last n)).2 +
          ∑ i : Fin n,
            dist (p i.succ).1 (p i.castSucc).2 := by
    rw [Fin.sum_univ_succ]
    rw [hSigmaZero]
    congr 1
    apply Fintype.sum_congr
    intro i
    rw [hSigmaSucc]
  rw [hCross] at hCycle
  have hTriangle :
      dist (p 0).1 (p (Fin.last n)).2 <=
        dist a (p 0).1 + dist a z +
          dist (p (Fin.last n)).2 z := by
    calc
      dist (p 0).1 (p (Fin.last n)).2 <=
          dist (p 0).1 a + dist a (p (Fin.last n)).2 :=
        dist_triangle _ _ _
      _ <= dist (p 0).1 a +
          (dist a z + dist z (p (Fin.last n)).2) := by
        gcongr
        exact dist_triangle _ _ _
      _ = dist a (p 0).1 + dist a z +
          dist (p (Fin.last n)).2 z := by
        rw [dist_comm (p 0).1 a,
          dist_comm z (p (Fin.last n)).2]
        ring
  unfold dualFiniteDistanceChainCost
  linarith

private def dualFiniteDistanceChainValues
    {E : Type u} [PseudoMetricSpace E]
    (Gamma : Set (E × E)) (a z : E) : Set Real :=
  {r | r = dist a z ∨
    ∃ (n : Nat) (p : Fin (n + 1) -> E × E),
      (∀ i, p i ∈ Gamma) ∧
        r = dualFiniteDistanceChainCost a z p}

private theorem dualFiniteDistanceChainValues_nonempty
    {E : Type u} [PseudoMetricSpace E]
    (Gamma : Set (E × E)) (a z : E) :
    (dualFiniteDistanceChainValues Gamma a z).Nonempty :=
  ⟨dist a z, Or.inl rfl⟩

private theorem dualFiniteDistanceChainValues_bddBelow
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a z : E) :
    BddBelow (dualFiniteDistanceChainValues Gamma a z) := by
  refine ⟨-dist a z, ?_⟩
  rintro r (hr | ⟨n, p, hp, rfl⟩)
  · rw [hr]
    linarith [show 0 <= dist a z from dist_nonneg]
  · exact dualFiniteDistanceChainCost_lower hCyclic a z p hp

private def dualDistanceChainPotential
    {E : Type u} [PseudoMetricSpace E]
    (Gamma : Set (E × E)) (a z : E) : Real :=
  sInf (dualFiniteDistanceChainValues Gamma a z)

private theorem dualDistanceChainPotential_le_add_dist
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a z z' : E) :
    dualDistanceChainPotential Gamma a z' <=
      dualDistanceChainPotential Gamma a z + dist z z' := by
  rw [← sub_le_iff_le_add]
  apply le_csInf (dualFiniteDistanceChainValues_nonempty Gamma a z)
  intro r hr
  rcases hr with hr | ⟨n, p, hp, hr⟩
  · subst r
    have hValue :
        dualDistanceChainPotential Gamma a z' <= dist a z' :=
      csInf_le
        (dualFiniteDistanceChainValues_bddBelow hCyclic a z')
        (Or.inl rfl)
    linarith [dist_triangle a z z']
  · subst r
    have hValue :
        dualDistanceChainPotential Gamma a z' <=
          dualFiniteDistanceChainCost a z' p :=
      csInf_le
        (dualFiniteDistanceChainValues_bddBelow hCyclic a z')
        (Or.inr ⟨n, p, hp, rfl⟩)
    linarith [
      dualFiniteDistanceChainCost_terminal_le a z z' p]

private theorem dualDistanceChainPotential_lipschitz
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a : E) :
    LipschitzWith 1 (dualDistanceChainPotential Gamma a) := by
  apply LipschitzWith.of_le_add
  intro z z'
  simpa [dist_comm] using
    dualDistanceChainPotential_le_add_dist hCyclic a z' z

private theorem dualDistanceChainPotential_calibrates
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a : E) {x y : E} (hxy : (x, y) ∈ Gamma) :
    dist x y =
      dualDistanceChainPotential Gamma a x -
        dualDistanceChainPotential Gamma a y := by
  have hReverse :
      dualDistanceChainPotential Gamma a y + dist x y <=
        dualDistanceChainPotential Gamma a x := by
    apply le_csInf
      (dualFiniteDistanceChainValues_nonempty Gamma a x)
    intro r hr
    have hAppended :
        r - dist x y ∈ dualFiniteDistanceChainValues Gamma a y := by
      rcases hr with hr | ⟨n, p, hp, hr⟩
      · subst r
        let q : Fin 1 -> E × E := fun _ => (x, y)
        refine Or.inr ⟨0, q, ?_, ?_⟩
        · intro i
          simpa [q] using hxy
        · simp [dualFiniteDistanceChainCost, q]
      · subst r
        refine Or.inr ⟨n + 1, Fin.snoc p (x, y), ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hxy
          · simpa using hp j
        · rw [dualFiniteDistanceChainCost_snoc]
          simp
    have hInf :
        dualDistanceChainPotential Gamma a y <= r - dist x y :=
      csInf_le
        (dualFiniteDistanceChainValues_bddBelow hCyclic a y)
        hAppended
    linarith
  have hForward :
      dualDistanceChainPotential Gamma a x <=
        dualDistanceChainPotential Gamma a y + dist x y :=
    dualDistanceChainPotential_le_add_dist hCyclic a y x
      |>.trans_eq (by rw [dist_comm])
  linarith

private theorem existsDistanceContactPotentialForDualWitness
    {E : Type u} [PseudoMetricSpace E]
    (a : E) (Gamma : Set (E × E))
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma) :
    ∃ u : E -> Real,
      LipschitzWith 1 u ∧ Gamma ⊆ distanceContactSet u := by
  refine ⟨dualDistanceChainPotential Gamma a,
    dualDistanceChainPotential_lipschitz hCyclic a, ?_⟩
  intro z hz
  exact dualDistanceChainPotential_calibrates hCyclic a hz

/-- Existence of a distance dual witness is equivalent to existence of one
coupling carried by a distance-cyclically monotone set. The reverse
implication uses the finite shortest-chain potential construction above. -/
theorem nonemptyDistanceDualWitness_iff_existsSupportedDistanceCyclicallyMonotone
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    Nonempty (DistanceDualWitness mu nu) <->
      ∃ (Gamma : Set (Euclidean n × Euclidean n))
          (gamma : FiniteCoupling mu nu),
        IsDistanceCyclicallyMonotone Gamma ∧
          IsSupported gamma Gamma := by
  constructor
  · rintro ⟨w⟩
    obtain ⟨gamma, hGammaEq⟩ := w.minimum.1
    refine
      ⟨distanceContactSet w.potential, gamma,
        w.contactSetIsDistanceCyclicallyMonotone, ?_⟩
    exact
      (DistanceDualWitness.distanceCost_eq_finiteMarginalPotentialDifference_iff_isSupported
        w.potential w.lipschitz hSourceMoment hTargetMoment gamma).mp
          hGammaEq
  · rintro ⟨Gamma, gamma, hCyclic, hSupported⟩
    obtain ⟨u, hu, hSubset⟩ :=
      existsDistanceContactPotentialForDualWitness
        (0 : Euclidean n) Gamma
        (isDistanceCyclicallyMonotone_universeZero hCyclic)
    apply
      (nonemptyDistanceDualWitness_iff_existsContactCoupling
        n mu nu hSourceMoment hTargetMoment).mpr
    refine ⟨u, gamma, hu, ?_⟩
    filter_upwards [hSupported] with z hz
    exact hSubset hz

/-- Equal mass and finite first moments imply the epsilon-level reverse
Kantorovich-Rubinstein inequality. -/
theorem distanceKantorovichRubinsteinApproximateReverseInequality
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    DistanceKantorovichRubinsteinApproximateReverseInequality
      n mu nu := by
  apply
    (nonemptyDistanceDualWitness_iff_approximateReverseKantorovichRubinstein
      n mu nu hMass hSourceMoment hTargetMoment).mp
  apply
    (nonemptyDistanceDualWitness_iff_existsSupportedDistanceCyclicallyMonotone.{0}
      n mu nu hSourceMoment hTargetMoment).mpr
  obtain ⟨gamma, hGammaOptimal⟩ :=
    existsDistanceOptimal n mu nu hMass
      hSourceMoment hTargetMoment
  exact
    ⟨Measure.support
        (gamma.plan : Measure (Euclidean n × Euclidean n)),
      gamma,
      distanceOptimalSupport_isDistanceCyclicallyMonotone.{0}
        n hSourceMoment hTargetMoment gamma hGammaOptimal,
      Measure.support_mem_ae⟩

/-- Full distance contact characterization, conditional only on the explicit
dual witness whose existence is the Kantorovich-duality input. -/
theorem distanceContactCharacterization_of_distanceDualWitness
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (w : DistanceDualWitness mu nu) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  refine ⟨w.potential, w.lipschitz, ?_, ?_⟩
  · exact fun gamma =>
      w.isDistanceOptimal_iff_isSupported
        hSourceMoment hTargetMoment gamma
  · exact w.contactSetIsDistanceCyclicallyMonotone

/-- Under equal mass and finite first moments, the paper's distance-contact
characterization is equivalent to existence of the exact distance dual
witness. This is a reduction, not the original unconditional target. -/
theorem distanceContactCharacterization_iff_nonemptyDistanceDualWitness
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    (exists u : Euclidean n -> Real,
        LipschitzWith 1 u /\
          (∀ gamma : FiniteCoupling mu nu,
            IsDistanceOptimal gamma <->
              IsSupported gamma (distanceContactSet u)) /\
          IsDistanceCyclicallyMonotone (distanceContactSet u)) <->
      Nonempty (DistanceDualWitness mu nu) := by
  constructor
  · rintro ⟨u, hu, hCharacterization, _hCyclic⟩
    obtain ⟨gamma, hGammaOptimal⟩ :=
      existsDistanceOptimal n mu nu hMass
        hSourceMoment hTargetMoment
    apply
      (nonemptyDistanceDualWitness_iff_existsContactCoupling
        n mu nu hSourceMoment hTargetMoment).mpr
    exact
      ⟨u, gamma, hu,
        (hCharacterization gamma).mp hGammaOptimal⟩
  · rintro ⟨w⟩
    exact
      distanceContactCharacterization_of_distanceDualWitness
        n mu nu hSourceMoment hTargetMoment w

/-- The exact original conclusion is equivalently reduced to finding one
coupling carried by a distance-cyclically monotone set. -/
theorem distanceContactCharacterization_iff_existsSupportedDistanceCyclicallyMonotone
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    (exists u : Euclidean n -> Real,
        LipschitzWith 1 u /\
          (∀ gamma : FiniteCoupling mu nu,
            IsDistanceOptimal gamma <->
              IsSupported gamma (distanceContactSet u)) /\
          IsDistanceCyclicallyMonotone (distanceContactSet u)) <->
      ∃ (Gamma : Set (Euclidean n × Euclidean n))
          (gamma : FiniteCoupling mu nu),
        IsDistanceCyclicallyMonotone Gamma ∧
          IsSupported gamma Gamma :=
  (distanceContactCharacterization_iff_nonemptyDistanceDualWitness
      n mu nu hMass hSourceMoment hTargetMoment).trans
    (nonemptyDistanceDualWitness_iff_existsSupportedDistanceCyclicallyMonotone
      n mu nu hSourceMoment hTargetMoment)

/-- It is enough to prove the standard necessity direction: the topological
support of a distance-optimal plan is distance-cyclically monotone. -/
theorem distanceContactCharacterization_of_optimalSupportCyclicallyMonotone
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hOptimalSupportCyclic :
      ∀ gamma : FiniteCoupling mu nu,
        IsDistanceOptimal gamma ->
          IsDistanceCyclicallyMonotone
            (Measure.support
              (gamma.plan :
                Measure (Euclidean n × Euclidean n)))) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  apply
    (distanceContactCharacterization_iff_existsSupportedDistanceCyclicallyMonotone
      n mu nu hMass hSourceMoment hTargetMoment).mpr
  obtain ⟨gamma, hGammaOptimal⟩ :=
    existsDistanceOptimal n mu nu hMass
      hSourceMoment hTargetMoment
  exact
    ⟨Measure.support
        (gamma.plan : Measure (Euclidean n × Euclidean n)),
      gamma, hOptimalSupportCyclic gamma hGammaOptimal,
      Measure.support_mem_ae⟩

/-- The exact original existential conclusion is equivalent to the
epsilon-level no-duality-gap statement; both primal and dual attainment have
already been discharged. -/
theorem distanceContactCharacterization_iff_approximateReverseKantorovichRubinstein
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    (exists u : Euclidean n -> Real,
        LipschitzWith 1 u /\
          (∀ gamma : FiniteCoupling mu nu,
            IsDistanceOptimal gamma <->
              IsSupported gamma (distanceContactSet u)) /\
          IsDistanceCyclicallyMonotone (distanceContactSet u)) <->
      DistanceKantorovichRubinsteinApproximateReverseInequality n mu nu :=
  (distanceContactCharacterization_iff_nonemptyDistanceDualWitness
      n mu nu hMass hSourceMoment hTargetMoment).trans
    (nonemptyDistanceDualWitness_iff_approximateReverseKantorovichRubinstein
      n mu nu hMass hSourceMoment hTargetMoment)

/-- The original paper conclusion follows from precisely the missing reverse
Kantorovich-Rubinstein inequality. -/
theorem distanceContactCharacterization_of_reverseKantorovichRubinstein
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hReverse :
      DistanceKantorovichRubinsteinReverseInequality n mu nu) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  obtain ⟨w⟩ :=
    (nonemptyDistanceDualWitness_iff_reverseKantorovichRubinstein
      n mu nu hMass hSourceMoment hTargetMoment).mpr hReverse
  exact
    distanceContactCharacterization_of_distanceDualWitness
      n mu nu hSourceMoment hTargetMoment w

/-- The original conclusion only needs epsilon-level reverse duality;
compactness supplies the limiting potential and its attainment. -/
theorem distanceContactCharacterization_of_approximateReverseKantorovichRubinstein
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (hApproximate :
      DistanceKantorovichRubinsteinApproximateReverseInequality n mu nu) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  apply
    distanceContactCharacterization_of_reverseKantorovichRubinstein
      n mu nu hMass hSourceMoment hTargetMoment
  exact
    (reverseKantorovichRubinstein_iff_approximateReverse
      n mu nu hMass hSourceMoment hTargetMoment).mpr hApproximate

/-- The paper conclusion is unconditional when the common mass is zero. -/
theorem distanceContactCharacterization_of_mass_zero
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hZero : mu.mass = 0)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  obtain ⟨w⟩ :=
    nonemptyDistanceDualWitnessOfMassZero n mu nu hMass hZero
  exact
    distanceContactCharacterization_of_distanceDualWitness
      n mu nu hSourceMoment hTargetMoment w

/-- A single `1`-Lipschitz potential characterizes all distance-optimal
couplings by its distance contact set. -/
theorem distanceContactCharacterization
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMass : mu.mass = nu.mass)
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n))) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone (distanceContactSet u) := by
  apply
    distanceContactCharacterization_of_approximateReverseKantorovichRubinstein
      n mu nu hMass hSourceMoment hTargetMoment
  exact
    distanceKantorovichRubinsteinApproximateReverseInequality
      n mu nu hMass hSourceMoment hTargetMoment

end ConcaveOTLimit
