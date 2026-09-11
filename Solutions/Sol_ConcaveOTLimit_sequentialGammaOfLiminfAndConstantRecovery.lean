import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {X : Type*} [TopologicalSpace X]
    (approximation : Nat -> X -> EReal)
    (limit : X -> EReal) (domain : Set X)
    (hliminf :
      ∀ {xSeq : Nat -> X} {x : X} {subseq : Nat -> Nat},
        StrictMono subseq ->
          Tendsto xSeq atTop (nhds x) ->
            x ∈ domain ->
              ∀ r : Real, (r : EReal) < limit x ->
                ∀ᶠ k in atTop,
                  (r : EReal) <= approximation (subseq k) (xSeq k))
    (hrecovery :
      ∀ x ∈ domain,
        Tendsto (fun k => approximation k x)
          atTop (nhds (limit x))) :
    SequentialGammaConvergesOn approximation limit domain where
  liminf := hliminf
  recovery x hx :=
    ⟨fun _ => x, tendsto_const_nhds, by simpa using hrecovery x hx⟩
