import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

open ConcaveOTLimit

private theorem forward
    {X : Type*} [TopologicalSpace X]
    {approximation approximation' : Nat -> X -> EReal}
    {limit : X -> EReal} {domain : Set X}
    (hEventually :
      ∀ᶠ n in atTop, approximation n = approximation' n)
    (hGamma : SequentialGammaConvergesOn approximation limit domain) :
    SequentialGammaConvergesOn approximation' limit domain where
  liminf := by
    intro xSeq x subseq hSubseq hTendsto hx r hr
    have hLower :=
      hGamma.liminf hSubseq hTendsto hx r hr
    have hEventuallySubseq :
        ∀ᶠ k in atTop,
          approximation (subseq k) = approximation' (subseq k) :=
      hSubseq.tendsto_atTop hEventually
    filter_upwards [hLower, hEventuallySubseq] with k hk hEq
    simpa only [hEq] using hk
  recovery := by
    intro x hx
    obtain ⟨xSeq, hTendsto, hEnergy⟩ := hGamma.recovery x hx
    refine ⟨xSeq, hTendsto, ?_⟩
    apply hEnergy.congr'
    filter_upwards [hEventually] with n hEq
    exact congrFun hEq (xSeq n)

theorem solution
    {X : Type*} [TopologicalSpace X]
    {approximation approximation' : Nat -> X -> EReal}
    {limit : X -> EReal} {domain : Set X}
    (hEventually :
      ∀ᶠ n in atTop, approximation n = approximation' n) :
    SequentialGammaConvergesOn approximation limit domain <->
      SequentialGammaConvergesOn approximation' limit domain := by
  constructor
  · exact forward hEventually
  · exact forward (hEventually.mono fun _ h => h.symm)
