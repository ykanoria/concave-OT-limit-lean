import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

namespace ConcaveOTLimit

/-- A convergent sequence of exact minimizers of Gamma-convergent
functionals minimizes the Gamma limit on its domain. -/
theorem sequentialGammaLimitIsMinimizer
    {X : Type*} [TopologicalSpace X]
    {approx : Nat -> X -> EReal} {limit : X -> EReal} {s : Set X}
    (hGamma : SequentialGammaConvergesOn approx limit s)
    {u : Nat -> X} {x : X}
    (hu : Tendsto u atTop (nhds x)) (hx : x ∈ s)
    (hmin : ∀ n, IsMinOn (approx n) univ (u n)) :
    IsMinOn limit s x := by
  intro z hz
  by_contra hle
  have hzx : limit z < limit x := lt_of_not_ge hle
  obtain ⟨r, hzr, hrx⟩ := EReal.exists_between_coe_real hzx
  obtain ⟨v, -, hvenergy⟩ := hGamma.recovery z hz
  have hlower :
      ∀ᶠ n : Nat in atTop, (r : EReal) <= approx n (u n) := by
    simpa using
      hGamma.liminf (subseq := id) strictMono_id hu hx r hrx
  have hupper :
      ∀ᶠ n : Nat in atTop, approx n (v n) < (r : EReal) :=
    hvenergy.eventually_lt_const hzr
  have hfalse : ∀ᶠ n : Nat in atTop, False :=
    (hlower.and hupper).mono fun n hn => by
      have hnmin : approx n (u n) <= approx n (v n) :=
        hmin n (mem_univ (v n))
      exact (not_lt_of_ge (hn.1.trans hnmin)) hn.2
  have hex : ∃ n : Nat, False := Filter.Eventually.exists hfalse
  exact hex.elim fun _ h => h

end ConcaveOTLimit
