import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments
import Mathlib.GroupTheory.Perm.Fin

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace ConcaveOTLimit

universe u

/-- The cost of a nonempty finite chain of directed distance-calibrated
edges, with ordinary metric links between consecutive edges. -/
private def finiteDistanceChainCost
    {E : Type u} [PseudoMetricSpace E] {n : Nat}
    (a z : E) (p : Fin (n + 1) -> E × E) : Real :=
  dist a (p 0).1 +
      (∑ i : Fin n,
        dist (p i.succ).1 (p i.castSucc).2) -
    (∑ i : Fin (n + 1), dist (p i).1 (p i).2) +
    dist (p (Fin.last n)).2 z

/-- Appending one support edge has the expected Bellman-Ford cost. -/
private theorem finiteDistanceChainCost_snoc
    {E : Type u} [PseudoMetricSpace E] {n : Nat}
    (a z : E) (p : Fin (n + 1) -> E × E) (q : E × E) :
    finiteDistanceChainCost a z (Fin.snoc p q) =
      finiteDistanceChainCost a q.1 p -
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
      have hs :
          (Fin.snoc p q : Fin (n + 2) -> E × E) i.castSucc.succ =
            p i.succ := by
        rw [show i.castSucc.succ = i.succ.castSucc by
          apply Fin.ext
          rfl]
        simpa using
          (Fin.snoc_castSucc
            (α := fun _ : Fin (n + 2) => E × E)
            (p := p) (x := q) (i := i.succ))
      have ht :
          (Fin.snoc p q : Fin (n + 2) -> E × E)
              i.castSucc.castSucc =
            p i.castSucc := by
        exact
          (Fin.snoc_castSucc
            (α := fun _ : Fin (n + 2) => E × E)
            (p := p) (x := q) (i := i.castSucc))
      rw [hs, ht]
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
  simp only [finiteDistanceChainCost]
  rw [hLinks, hEdges]
  simp
  rw [dist_comm q.1 (p (Fin.last n)).2]
  ring

/-- Moving the terminal point of a finite chain costs at most the distance
between the two terminals. -/
private theorem finiteDistanceChainCost_terminal_le
    {E : Type u} [PseudoMetricSpace E] {n : Nat}
    (a z z' : E) (p : Fin (n + 1) -> E × E) :
    finiteDistanceChainCost a z' p <=
      finiteDistanceChainCost a z p + dist z z' := by
  unfold finiteDistanceChainCost
  linarith [dist_triangle (p (Fin.last n)).2 z z']

/-- Cyclic monotonicity is exactly the no-negative-cycle estimate for the
finite chains used below. -/
private theorem finiteDistanceChainCost_lower
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    {n : Nat} (a z : E) (p : Fin (n + 1) -> E × E)
    (hp : ∀ i, p i ∈ Gamma) :
    -dist a z <= finiteDistanceChainCost a z p := by
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
  unfold finiteDistanceChainCost
  linarith

/-- Values of all finite calibrated-edge chains from `a` to `z`. The first
disjunct is the chain containing no calibrated edge. -/
private def finiteDistanceChainValues
    {E : Type u} [PseudoMetricSpace E]
    (Gamma : Set (E × E)) (a z : E) : Set Real :=
  {r | r = dist a z ∨
    ∃ (n : Nat) (p : Fin (n + 1) -> E × E),
      (∀ i, p i ∈ Gamma) ∧
        r = finiteDistanceChainCost a z p}

private theorem finiteDistanceChainValues_nonempty
    {E : Type u} [PseudoMetricSpace E]
    (Gamma : Set (E × E)) (a z : E) :
    (finiteDistanceChainValues Gamma a z).Nonempty :=
  ⟨dist a z, Or.inl rfl⟩

private theorem finiteDistanceChainValues_bddBelow
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a z : E) :
    BddBelow (finiteDistanceChainValues Gamma a z) := by
  refine ⟨-dist a z, ?_⟩
  rintro r (hr | ⟨n, p, hp, rfl⟩)
  · rw [hr]
    linarith [show 0 <= dist a z from dist_nonneg]
  · exact finiteDistanceChainCost_lower hCyclic a z p hp

/-- The shortest finite-chain potential based at `a`. -/
private def distanceChainPotential
    {E : Type u} [PseudoMetricSpace E]
    (Gamma : Set (E × E)) (a z : E) : Real :=
  sInf (finiteDistanceChainValues Gamma a z)

private theorem distanceChainPotential_le_add_dist
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a z z' : E) :
    distanceChainPotential Gamma a z' <=
      distanceChainPotential Gamma a z + dist z z' := by
  rw [← sub_le_iff_le_add]
  apply le_csInf (finiteDistanceChainValues_nonempty Gamma a z)
  intro r hr
  rcases hr with hr | ⟨n, p, hp, hr⟩
  · subst r
    have hValue :
        distanceChainPotential Gamma a z' <= dist a z' :=
      csInf_le
        (finiteDistanceChainValues_bddBelow hCyclic a z')
        (Or.inl rfl)
    linarith [dist_triangle a z z']
  · subst r
    have hValue :
        distanceChainPotential Gamma a z' <=
          finiteDistanceChainCost a z' p :=
      csInf_le
        (finiteDistanceChainValues_bddBelow hCyclic a z')
        (Or.inr ⟨n, p, hp, rfl⟩)
    linarith [finiteDistanceChainCost_terminal_le a z z' p]

private theorem distanceChainPotential_lipschitz
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a : E) :
    LipschitzWith 1 (distanceChainPotential Gamma a) := by
  apply LipschitzWith.of_le_add
  intro z z'
  simpa [dist_comm] using
    distanceChainPotential_le_add_dist hCyclic a z' z

private theorem distanceChainPotential_calibrates
    {E : Type u} [PseudoMetricSpace E]
    {Gamma : Set (E × E)}
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma)
    (a : E) {x y : E} (hxy : (x, y) ∈ Gamma) :
    dist x y =
      distanceChainPotential Gamma a x -
        distanceChainPotential Gamma a y := by
  have hReverse :
      distanceChainPotential Gamma a y + dist x y <=
        distanceChainPotential Gamma a x := by
    apply le_csInf (finiteDistanceChainValues_nonempty Gamma a x)
    intro r hr
    have hAppended :
        r - dist x y ∈ finiteDistanceChainValues Gamma a y := by
      rcases hr with hr | ⟨n, p, hp, hr⟩
      · subst r
        let q : Fin 1 -> E × E := fun _ => (x, y)
        refine Or.inr ⟨0, q, ?_, ?_⟩
        · intro i
          simpa [q] using hxy
        · simp [finiteDistanceChainCost, q]
      · subst r
        refine Or.inr ⟨n + 1, Fin.snoc p (x, y), ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hxy
          · simpa using hp j
        · rw [finiteDistanceChainCost_snoc]
          simp
    have hInf :
        distanceChainPotential Gamma a y <= r - dist x y :=
      csInf_le
        (finiteDistanceChainValues_bddBelow hCyclic a y)
        hAppended
    linarith
  have hForward :
      distanceChainPotential Gamma a x <=
        distanceChainPotential Gamma a y + dist x y :=
    distanceChainPotential_le_add_dist hCyclic a y x
      |>.trans_eq (by rw [dist_comm])
  linarith

/-- Every distance-cyclically monotone set is contained in the distance
contact set of a globally `1`-Lipschitz real potential. -/
theorem existsDistanceContactPotential_of_isDistanceCyclicallyMonotone
    {E : Type u} [PseudoMetricSpace E]
    (a : E) (Gamma : Set (E × E))
    (hCyclic : IsDistanceCyclicallyMonotone.{u, 0} Gamma) :
    ∃ u : E -> Real,
      LipschitzWith 1 u ∧ Gamma ⊆ distanceContactSet u := by
  refine ⟨distanceChainPotential Gamma a,
    distanceChainPotential_lipschitz hCyclic a, ?_⟩
  intro z hz
  exact distanceChainPotential_calibrates hCyclic a hz

private def distancePotentialMarginalDifference
    {E : Type*} [MeasurableSpace E]
    (mu nu : FiniteMeasure E) (u : E -> Real) : Real :=
  (∫ x, u x ∂(mu : Measure E)) -
    ∫ y, u y ∂(nu : Measure E)

private theorem distancePotentialMeasurePreservingFst
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (E × E)) (mu : Measure E) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.1

private theorem distancePotentialMeasurePreservingSnd
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (E × E)) (nu : Measure E) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure E => (eta : Measure E)) gamma.property.2

private theorem integrableDistancePotential
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
    _ <= ‖u x - u 0‖ + ‖u 0‖ := norm_add_le _ _
    _ <= ‖x‖ + ‖u 0‖ := by
      simpa [dist_eq_norm] using hu.dist_le_mul x 0
    _ = ‖u 0‖ + ‖x‖ := add_comm _ _

private theorem integralDistancePotentialDifference_eq
    {E : Type*} [MeasurableSpace E]
    {mu nu : FiniteMeasure E}
    (u : E -> Real)
    (hMu : Integrable u (mu : Measure E))
    (hNu : Integrable u (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    (∫ z : E × E, (u z.1 - u z.2)
        ∂(gamma.plan : Measure (E × E))) =
      distancePotentialMarginalDifference mu nu u := by
  have hFst :
      Integrable (fun z : E × E => u z.1)
        (gamma.plan : Measure (E × E)) :=
    (distancePotentialMeasurePreservingFst gamma)
      |>.integrable_comp_of_integrable hMu
  have hSnd :
      Integrable (fun z : E × E => u z.2)
        (gamma.plan : Measure (E × E)) :=
    (distancePotentialMeasurePreservingSnd gamma)
      |>.integrable_comp_of_integrable hNu
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
        rw [(distancePotentialMeasurePreservingFst gamma).map_eq]
        exact hMu.aestronglyMeasurable
      _ = ∫ x, u x ∂(mu : Measure E) := by
        rw [(distancePotentialMeasurePreservingFst gamma).map_eq]
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
        rw [(distancePotentialMeasurePreservingSnd gamma).map_eq]
        exact hNu.aestronglyMeasurable
      _ = ∫ y, u y ∂(nu : Measure E) := by
        rw [(distancePotentialMeasurePreservingSnd gamma).map_eq]
  rw [integral_sub hFst hSnd, hFstIntegral, hSndIntegral]
  rfl

private theorem distancePotentialMarginalDifference_le_distanceCost
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [MeasurableSub₂ E]
    {mu nu : FiniteMeasure E}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hSourceMoment :
      Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hTargetMoment :
      Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    distancePotentialMarginalDifference mu nu u <=
      distanceCost gamma := by
  have hSourcePotential :
      Integrable u (mu : Measure E) :=
    integrableDistancePotential u hu hSourceMoment
  have hTargetPotential :
      Integrable u (nu : Measure E) :=
    integrableDistancePotential u hu hTargetMoment
  have hPotentialDifference :
      Integrable (fun z : E × E => u z.1 - u z.2)
        (gamma.plan : Measure (E × E)) :=
    ((distancePotentialMeasurePreservingFst gamma)
      |>.integrable_comp_of_integrable hSourcePotential).sub
      ((distancePotentialMeasurePreservingSnd gamma)
        |>.integrable_comp_of_integrable hTargetPotential)
  have hDistance :
      Integrable (fun z : E × E => dist z.1 z.2)
        (gamma.plan : Measure (E × E)) := by
    simpa [dist_eq_norm] using
      distanceIntegrableOfMarginalFirstMoments
        hSourceMoment hTargetMoment gamma
  calc
    distancePotentialMarginalDifference mu nu u =
        ∫ z : E × E, (u z.1 - u z.2)
          ∂(gamma.plan : Measure (E × E)) :=
      (integralDistancePotentialDifference_eq
        u hSourcePotential hTargetPotential gamma).symm
    _ <= ∫ z : E × E, dist z.1 z.2
          ∂(gamma.plan : Measure (E × E)) := by
      apply integral_mono hPotentialDifference hDistance
      intro z
      apply sub_le_iff_le_add'.2
      simpa using hu.le_add_mul z.1 z.2
    _ = distanceCost gamma := by
      simp [distanceCost, profileCost, dist_eq_norm]

private theorem distanceCost_eq_distancePotentialMarginalDifference
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E]
    {mu nu : FiniteMeasure E}
    (u : E -> Real) (hu : LipschitzWith 1 u)
    (hSourceMoment :
      Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hTargetMoment :
      Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu)
    (hContact : IsSupported gamma (distanceContactSet u)) :
    distanceCost gamma =
      distancePotentialMarginalDifference mu nu u := by
  have hSourcePotential :
      Integrable u (mu : Measure E) :=
    integrableDistancePotential u hu hSourceMoment
  have hTargetPotential :
      Integrable u (nu : Measure E) :=
    integrableDistancePotential u hu hTargetMoment
  calc
    distanceCost gamma =
        ∫ z : E × E, dist z.1 z.2
          ∂(gamma.plan : Measure (E × E)) := by
      simp [distanceCost, profileCost, dist_eq_norm]
    _ = ∫ z : E × E, (u z.1 - u z.2)
          ∂(gamma.plan : Measure (E × E)) :=
      integral_congr_ae hContact
    _ = distancePotentialMarginalDifference mu nu u :=
      integralDistancePotentialDifference_eq
        u hSourcePotential hTargetPotential gamma

/-- A coupling concentrated on a distance-cyclically monotone set minimizes
the distance cost among all couplings with the same marginals. -/
theorem distanceCyclicMonotoneSufficiency
    (n : Nat)
    {mu nu : FiniteMeasure (Euclidean n)}
    (hSourceMoment :
      Integrable (fun x : Euclidean n => ‖x‖)
        (mu : Measure (Euclidean n)))
    (hTargetMoment :
      Integrable (fun y : Euclidean n => ‖y‖)
        (nu : Measure (Euclidean n)))
    (Gamma : Set (Euclidean n × Euclidean n))
    (gamma : FiniteCoupling mu nu)
    (hCyclic : IsDistanceCyclicallyMonotone.{0, 0} Gamma)
    (hSupported : IsSupported gamma Gamma) :
    IsDistanceOptimal gamma := by
  obtain ⟨u, hu, hGammaContact⟩ :=
    existsDistanceContactPotential_of_isDistanceCyclicallyMonotone
      (0 : Euclidean n) Gamma hCyclic
  have hContact :
      IsSupported gamma (distanceContactSet u) := by
    filter_upwards [hSupported] with z hz
    exact hGammaContact hz
  have hGammaCost :
      distanceCost gamma =
        distancePotentialMarginalDifference mu nu u :=
    distanceCost_eq_distancePotentialMarginalDifference
      u hu hSourceMoment hTargetMoment gamma hContact
  refine ⟨mem_univ gamma, ?_⟩
  intro eta _hEta
  change distanceCost gamma <= distanceCost eta
  rw [hGammaCost]
  exact distancePotentialMarginalDifference_le_distanceCost
    u hu hSourceMoment hTargetMoment eta

/-- The form directly usable under the marginal assumptions of
`canonicalRaywiseReplacement`. Equal mass is already encoded by the
existence of the finite coupling. -/
theorem distanceCyclicMonotoneSufficiency_of_marginalHypotheses
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (gamma : FiniteCoupling mu nu)
    (hCyclic : IsDistanceCyclicallyMonotone.{0, 0} Gamma)
    (hSupported : IsSupported gamma Gamma) :
    IsDistanceOptimal gamma :=
  distanceCyclicMonotoneSufficiency n
    hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
    Gamma gamma hCyclic hSupported

end ConcaveOTLimit
