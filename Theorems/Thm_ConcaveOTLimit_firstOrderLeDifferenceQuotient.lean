import Definitions.Def_ConcaveOTLimitModel

open Filter Set Topology

namespace ConcaveOTLimit

private theorem quotient_le_quotient
    {family : Real -> Real -> Real} {d delta epsilon : Real}
    (hconv : ConvexOn Real epsilonDomain (fun t => family t d))
    (htend : Tendsto (fun t => family t d)
      (nhdsWithin 0 epsilonDomain) (nhds d))
    (hdelta : delta ∈ epsilonDomain)
    (hepsilon : epsilon ∈ epsilonDomain)
    (hde : delta <= epsilon) :
    (family delta d - d) / delta <=
      (family epsilon d - d) / epsilon := by
  let L := nhdsWithin 0 epsilonDomain
  have hL : NeBot L := by
    simpa [L, epsilonDomain] using
      (left_nhdsWithin_Ioo_neBot (show (0 : Real) < 1 by norm_num))
  let left : Real -> Real :=
    fun a => (family delta d - family a d) / (delta - a)
  let right : Real -> Real :=
    fun a => (family epsilon d - family a d) / (epsilon - a)
  have hleft :
      Tendsto left L (nhds ((family delta d - d) / delta)) := by
    have hnum :
        Tendsto (fun a : Real => family delta d - family a d) L
          (nhds (family delta d - d)) :=
      tendsto_const_nhds.sub htend
    have hden :
        Tendsto (fun a : Real => delta - a) L (nhds delta) := by
      have hid : Tendsto (fun a : Real => a) L (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using
        (tendsto_const_nhds.sub hid :
          Tendsto (fun a : Real => delta - a) L (nhds (delta - 0)))
    have h := hnum.div hden hdelta.1.ne'
    change Tendsto
      ((fun a : Real => family delta d - family a d) /
        fun a : Real => delta - a) L
        (nhds ((family delta d - d) / delta))
    exact h
  have hright :
      Tendsto right L
        (nhds ((family epsilon d - d) / epsilon)) := by
    have hnum :
        Tendsto (fun a : Real => family epsilon d - family a d) L
          (nhds (family epsilon d - d)) :=
      tendsto_const_nhds.sub htend
    have hden :
        Tendsto (fun a : Real => epsilon - a) L (nhds epsilon) := by
      have hid : Tendsto (fun a : Real => a) L (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using
        (tendsto_const_nhds.sub hid :
          Tendsto (fun a : Real => epsilon - a) L
            (nhds (epsilon - 0)))
    have h := hnum.div hden hepsilon.1.ne'
    change Tendsto
      ((fun a : Real => family epsilon d - family a d) /
        fun a : Real => epsilon - a) L
        (nhds ((family epsilon d - d) / epsilon))
    exact h
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds hdelta.1),
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds hepsilon.1)] with a ha hadelta haepsilon
  exact hconv.secant_mono ha hdelta hepsilon
    (ne_of_gt hadelta) (ne_of_gt haepsilon) hde

/-- Convexity in the perturbation parameter bounds every positive difference
quotient below by its first-order limit. -/
theorem firstOrderLeDifferenceQuotient
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hAssumptions : PerturbationAssumptions family firstOrder)
    {epsilon d : Real}
    (hEpsilon : epsilon ∈ epsilonDomain) (hd : 0 <= d) :
    firstOrder d <= (family epsilon d - d) / epsilon := by
  let L := nhdsWithin 0 epsilonDomain
  have hL : NeBot L := by
    simpa [L, epsilonDomain] using
      (left_nhdsWithin_Ioo_neBot (show (0 : Real) < 1 by norm_num))
  apply le_of_tendsto (hAssumptions.firstOrderLimit hd)
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iic_mem_nhds hEpsilon.1)] with delta hdelta hde
  exact quotient_le_quotient
    (hAssumptions.convexInEpsilon hd)
    (hAssumptions.tendsToIdentity hd)
    hdelta hEpsilon hde

end ConcaveOTLimit
