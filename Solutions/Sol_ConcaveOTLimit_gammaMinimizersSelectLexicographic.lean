import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {X : Type*} [TopologicalSpace X]
    {primaryApprox rescaled : Nat -> X -> EReal}
    {primary secondary : X -> EReal}
    (hprimary : SequentialGammaConverges primaryApprox primary)
    (hliminf :
      ∀ {xSeq : Nat -> X} {x : X} {subseq : Nat -> Nat},
        StrictMono subseq ->
          Tendsto xSeq atTop (nhds x) ->
            IsMinOn primary univ x ->
              ∀ r : Real, (r : EReal) < secondary x ->
                ∀ᶠ k in atTop,
                  (r : EReal) <= rescaled (subseq k) (xSeq k))
    (hrecovery :
      ∀ z, IsMinOn primary univ z ->
        Tendsto (fun k => rescaled k z)
          atTop (nhds (secondary z)))
    {u : Nat -> X} {x : X}
    (hu : Tendsto u atTop (nhds x))
    (hprimaryMin :
      ∀ n, IsMinOn (primaryApprox n) univ (u n))
    (hrescaledMin :
      ∀ n, IsMinOn (rescaled n) univ (u n)) :
    IsMinOn primary univ x /\
      IsMinOn secondary {z | IsMinOn primary univ z} x := by
  have hxprimary : IsMinOn primary univ x := by
    intro z hz
    by_contra hle
    have hzx : primary z < primary x := lt_of_not_ge hle
    obtain ⟨r, hzr, hrx⟩ := EReal.exists_between_coe_real hzx
    obtain ⟨v, -, hvenergy⟩ := hprimary.recovery z (mem_univ z)
    have hlower :
        ∀ᶠ n : Nat in atTop,
          (r : EReal) <= primaryApprox n (u n) := by
      simpa using
        hprimary.liminf (subseq := id) strictMono_id hu
          (mem_univ x) r hrx
    have hupper :
        ∀ᶠ n : Nat in atTop,
          primaryApprox n (v n) < (r : EReal) :=
      hvenergy.eventually_lt_const hzr
    have hfalse : ∀ᶠ n : Nat in atTop, False :=
      (hlower.and hupper).mono fun n hn => by
        have hnmin :
            primaryApprox n (u n) <= primaryApprox n (v n) :=
          hprimaryMin n (mem_univ (v n))
        exact (not_lt_of_ge (hn.1.trans hnmin)) hn.2
    have hex : ∃ n : Nat, False := Filter.Eventually.exists hfalse
    exact hex.elim fun _ h => h
  refine ⟨hxprimary, ?_⟩
  intro z hz
  by_contra hle
  have hzx : secondary z < secondary x := lt_of_not_ge hle
  obtain ⟨r, hzr, hrx⟩ := EReal.exists_between_coe_real hzx
  have hlower :
      ∀ᶠ n : Nat in atTop,
        (r : EReal) <= rescaled n (u n) := by
    simpa using
      hliminf (subseq := id) strictMono_id hu hxprimary r hrx
  have hupper :
      ∀ᶠ n : Nat in atTop, rescaled n z < (r : EReal) :=
    (hrecovery z hz).eventually_lt_const hzr
  have hfalse : ∀ᶠ n : Nat in atTop, False :=
    (hlower.and hupper).mono fun n hn => by
      have hnmin : rescaled n (u n) <= rescaled n z :=
        hrescaledMin n (mem_univ z)
      exact (not_lt_of_ge (hn.1.trans hnmin)) hn.2
  have hex : ∃ n : Nat, False := Filter.Eventually.exists hfalse
  exact hex.elim fun _ h => h
