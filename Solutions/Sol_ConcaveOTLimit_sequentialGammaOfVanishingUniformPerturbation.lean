import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {X : Type*} [TopologicalSpace X]
    (primary : X -> Real) (quotient : Nat -> X -> Real)
    (epsilon : Nat -> Real) (bound : Real)
    (hBoundNonnegative : 0 <= bound)
    (hEpsilon : Tendsto epsilon atTop (nhds 0))
    (hQuotientBound :
      ∀ n x, abs (quotient n x) <= bound)
    (hPrimarySequentiallyContinuous :
      ∀ {xSeq : Nat -> X} {x : X},
        Tendsto xSeq atTop (nhds x) ->
          Tendsto (fun n => primary (xSeq n))
            atTop (nhds (primary x))) :
    SequentialGammaConverges
      (fun n x =>
        ((primary x + epsilon n * quotient n x : Real) : EReal))
      (fun x => (primary x : EReal)) := by
  have movingTendsto :
      ∀ (index : Nat -> Nat),
        Tendsto index atTop atTop ->
          ∀ {xSeq : Nat -> X} {x : X},
            Tendsto xSeq atTop (nhds x) ->
              Tendsto
                (fun n =>
                  primary (xSeq n) +
                    epsilon (index n) * quotient (index n) (xSeq n))
                atTop (nhds (primary x)) := by
    intro index hIndex xSeq x hX
    have hIndexedEpsilon :
        Tendsto (epsilon ∘ index) atTop (nhds 0) :=
      hEpsilon.comp hIndex
    have hAbsEpsilon :
        Tendsto (fun n => abs (epsilon (index n)))
          atTop (nhds 0) := by
      simpa [Function.comp_apply, Real.norm_eq_abs] using
        hIndexedEpsilon.norm
    have hError :
        Tendsto
          (fun n => epsilon (index n) * quotient (index n) (xSeq n))
          atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro delta hDelta
      have hDenominator : 0 < bound + 1 := by
        linarith
      have hSmall :
          ∀ᶠ n in atTop,
            abs (epsilon (index n)) < delta / (bound + 1) :=
        hAbsEpsilon.eventually_lt_const
          (div_pos hDelta hDenominator)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hSmall
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_mul]
      have hQuotientStrict :
          abs (quotient (index n) (xSeq n)) < bound + 1 := by
        linarith [hQuotientBound (index n) (xSeq n)]
      calc
        abs (epsilon (index n)) *
              abs (quotient (index n) (xSeq n)) <=
            abs (epsilon (index n)) * (bound + 1) :=
          mul_le_mul_of_nonneg_left hQuotientStrict.le (abs_nonneg _)
        _ < (delta / (bound + 1)) * (bound + 1) :=
          mul_lt_mul_of_pos_right (hN n hn) hDenominator
        _ = delta := by field_simp
    simpa using
      (hPrimarySequentiallyContinuous hX).add hError
  refine ⟨?_, ?_⟩
  · intro xSeq x subseq hSubseq hX _ r hr
    have hMoving :=
      movingTendsto subseq hSubseq.tendsto_atTop hX
    have hrReal : r < primary x := EReal.coe_lt_coe_iff.mp hr
    filter_upwards [hMoving.eventually_const_lt hrReal] with n hn
    exact EReal.coe_le_coe_iff.mpr hn.le
  · intro x _
    refine ⟨fun _ => x, tendsto_const_nhds, ?_⟩
    apply EReal.tendsto_coe.mpr
    simpa using
      movingTendsto id tendsto_id
        (xSeq := fun _ => x) (x := x) tendsto_const_nhds
