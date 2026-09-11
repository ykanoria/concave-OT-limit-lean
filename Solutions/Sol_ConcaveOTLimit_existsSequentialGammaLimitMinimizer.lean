import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology
open ConcaveOTLimit

theorem solution
    {X : Type*} [TopologicalSpace X]
    {approx : Nat -> X -> EReal} {limit : X -> EReal} {s : Set X}
    (hs : IsSeqCompact s)
    (hGamma : SequentialGammaConvergesOn approx limit s)
    (u : Nat -> X) (hu_mem : ∀ n, u n ∈ s)
    (hmin : ∀ n, IsMinOn (approx n) univ (u n)) :
    ∃ x ∈ s, IsMinOn limit s x ∧
      ∃ k : Nat -> Nat,
        StrictMono k ∧ Tendsto (u ∘ k) atTop (nhds x) := by
  obtain ⟨x, hx, k, hk, hut⟩ := hs hu_mem
  refine ⟨x, hx, ?_, k, hk, hut⟩
  intro z hz
  by_contra hle
  have hzx : limit z < limit x := lt_of_not_ge hle
  obtain ⟨r, hzr, hrx⟩ := EReal.exists_between_coe_real hzx
  obtain ⟨v, -, hvenergy⟩ := hGamma.recovery z hz
  have hlower :
      ∀ᶠ n : Nat in atTop,
        (r : EReal) <= approx (k n) (u (k n)) := by
    simpa [Function.comp_def] using
      hGamma.liminf (subseq := k) hk hut hx r hrx
  have hupper :
      ∀ᶠ n : Nat in atTop,
        approx (k n) (v (k n)) < (r : EReal) := by
    simpa [Function.comp_def] using
      (hvenergy.comp hk.tendsto_atTop).eventually_lt_const hzr
  have hfalse : ∀ᶠ n : Nat in atTop, False :=
    (hlower.and hupper).mono fun n hn => by
      have hnmin :
          approx (k n) (u (k n)) <= approx (k n) (v (k n)) :=
        hmin (k n) (mem_univ (v (k n)))
      exact (not_lt_of_ge (hn.1.trans hnmin)) hn.2
  have hex : ∃ n : Nat, False := Filter.Eventually.exists hfalse
  exact hex.elim fun _ h => h
