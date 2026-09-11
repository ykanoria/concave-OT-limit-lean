import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {X : Type*} [TopologicalSpace X]
    (approximation : Nat -> X -> EReal)
    (lowerBound : X -> EReal) (domain : Set X)
    (hLowerSemicontinuous :
      ∀ {xSeq : Nat -> X} {x : X},
        Tendsto xSeq atTop (nhds x) ->
          x ∈ domain ->
            ∀ r : Real, (r : EReal) < lowerBound x ->
              ∀ᶠ k in atTop, (r : EReal) <= lowerBound (xSeq k))
    (hPointwise :
      ∀ n x, lowerBound x <= approximation n x) :
    ∀ {xSeq : Nat -> X} {x : X} {subseq : Nat -> Nat},
      StrictMono subseq ->
        Tendsto xSeq atTop (nhds x) ->
          x ∈ domain ->
            ∀ r : Real, (r : EReal) < lowerBound x ->
              ∀ᶠ k in atTop,
                (r : EReal) <= approximation (subseq k) (xSeq k) := by
  intro xSeq x subseq _ hTendsto hx r hr
  filter_upwards [hLowerSemicontinuous hTendsto hx r hr] with k hk
  exact hk.trans (hPointwise (subseq k) (xSeq k))
