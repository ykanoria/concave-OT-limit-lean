import Theorems.Thm_ConcaveOTLimit_powerGammaConvergencesOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_rescaledPowerSequentialGammaConverges
import Theorems.Thm_ConcaveOTLimit_sequentialGammaConvergesOnCongrEventually

open Filter MeasureTheory Topology

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (epsilon : Nat -> Real)
    (hEpsilon : ∀ n, epsilon n ∈ epsilonDomain)
    (hEpsilonTendsto :
      Tendsto epsilon atTop (nhdsWithin 0 epsilonDomain)) :
    SequentialGammaConverges
        (fun n (gamma : FiniteCoupling mu nu) =>
          (profileCost (powerProfile (epsilon n)) gamma : EReal))
        (fun gamma : FiniteCoupling mu nu =>
          (distanceCost gamma : EReal)) /\
      SequentialGammaConverges
        (fun n (gamma : FiniteCoupling mu nu) =>
          (rescaledProfileCost powerProfile (epsilon n) gamma : EReal))
        (fun gamma : FiniteCoupling mu nu =>
          extendedSecondaryCost logarithmicProfile gamma) := by
  have hPrimary :=
    (powerGammaConvergencesOfMarginalLogMoments
      hMu hNu epsilon hEpsilon hEpsilonTendsto).1
  let smallEpsilon : Nat -> Real :=
    fun n => min (epsilon n) (1 / 2)
  have hEpsilonTendsto' : Tendsto epsilon atTop (nhds 0) :=
    hEpsilonTendsto.mono_right inf_le_left
  have hEventuallyHalf : ∀ᶠ n in atTop, epsilon n <= 1 / 2 :=
    (hEpsilonTendsto'.eventually_lt_const (by norm_num)).mono
      fun _ h => h.le
  have hSmallEq : ∀ᶠ n in atTop, smallEpsilon n = epsilon n := by
    filter_upwards [hEventuallyHalf] with n hn
    exact min_eq_left hn
  have hSmallPos : ∀ n, 0 < smallEpsilon n := by
    intro n
    exact lt_min (hEpsilon n).1 (by norm_num)
  have hSmallLeHalf : ∀ n, smallEpsilon n <= 1 / 2 := by
    intro n
    exact min_le_right _ _
  have hSmallTendsto : Tendsto smallEpsilon atTop (nhds 0) :=
    hEpsilonTendsto'.congr'
      (hSmallEq.mono fun _ h => h.symm)
  have hRescaledSmall :=
    rescaledPowerSequentialGammaConverges
      hMu hNu smallEpsilon hSmallPos hSmallLeHalf hSmallTendsto
  have hRescaledEventually :
      ∀ᶠ n in atTop,
        (fun gamma : FiniteCoupling mu nu =>
          (rescaledProfileCost powerProfile (smallEpsilon n) gamma : EReal)) =
        (fun gamma : FiniteCoupling mu nu =>
          (rescaledProfileCost powerProfile (epsilon n) gamma : EReal)) := by
    filter_upwards [hSmallEq] with n hn
    rw [hn]
  exact
    ⟨hPrimary,
      (sequentialGammaConvergesOn_congrEventually
        hRescaledEventually).mp hRescaledSmall⟩
