import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {X : Type*} [TopologicalSpace X]
    (approximation : Nat -> X -> Real)
    (limit : X -> Real) (domain : Set X)
    (hLiminf :
      ∀ {xSeq : Nat -> X} {x : X} {subseq : Nat -> Nat},
        StrictMono subseq ->
          Tendsto xSeq atTop (nhds x) ->
            x ∈ domain ->
              ∀ r : Real, r < limit x ->
                ∀ᶠ k in atTop,
                  r <= approximation (subseq k) (xSeq k))
    (hRecovery :
      ∀ x ∈ domain,
        Tendsto (fun k => approximation k x)
          atTop (nhds (limit x))) :
    SequentialGammaConvergesOn
      (fun n x => (approximation n x : EReal))
      (fun x => (limit x : EReal)) domain where
  liminf := by
    intro xSeq x subseq hSubseq hTendsto hx r hr
    have hrReal : r < limit x := EReal.coe_lt_coe_iff.mp hr
    filter_upwards
      [hLiminf hSubseq hTendsto hx r hrReal] with k hk
    exact EReal.coe_le_coe_iff.mpr hk
  recovery := by
    intro x hx
    refine ⟨fun _ => x, tendsto_const_nhds, ?_⟩
    exact EReal.tendsto_coe.mpr (hRecovery x hx)
