import Mathlib.Topology.Sequences

open Filter
open scoped Topology

namespace ConcaveOTLimit

/-- In a sequentially compact space, identification of every convergent
subsequence with `x` implies convergence of the full sequence to `x`. -/
theorem tendstoOfSeqCompactUniqueSubseqLimit
    {X : Type*} [TopologicalSpace X] [SeqCompactSpace X]
    (u : Nat -> X) (x : X)
    (hUnique : forall phi : Nat -> Nat, StrictMono phi -> forall y : X,
      Tendsto (fun n => u (phi n)) atTop (nhds y) -> y = x) :
    Tendsto u atTop (nhds x) := by
  have hSubseq :
      forall phi : Nat -> Nat, StrictMono phi ->
        exists psi : Nat -> Nat, StrictMono psi /\
          Tendsto (fun n => u (phi (psi n))) atTop (nhds x) := by
    intro phi hPhi
    obtain ⟨y, psi, hPsi, hTendsto⟩ :=
      SeqCompactSpace.tendsto_subseq (fun n => u (phi n))
    have hy : y = x :=
      hUnique (phi ∘ psi) (hPhi.comp hPsi) y (by
        simpa [Function.comp_def] using hTendsto)
    exact ⟨psi, hPsi, by
      simpa [hy, Function.comp_def] using hTendsto⟩
  refine Filter.tendsto_of_subseq_tendsto
    (x := u) (f := nhds x) (l := atTop) ?_
  intro ns hNs
  obtain ⟨phi, hPhi, hNsPhi⟩ :=
    Filter.strictMono_subseq_of_tendsto_atTop hNs
  obtain ⟨psi, -, hTendsto⟩ := hSubseq (ns ∘ phi) hNsPhi
  exact ⟨phi ∘ psi, by
    simpa [Function.comp_def] using hTendsto⟩

end ConcaveOTLimit
