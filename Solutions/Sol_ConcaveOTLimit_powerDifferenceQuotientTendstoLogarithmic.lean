import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {r : Real} (hr : 0 <= r) :
    Tendsto
      (fun epsilon =>
        (powerProfile epsilon r - r) / epsilon)
      (nhdsWithin 0 (Ioi 0))
      (nhds (logarithmicProfile r)) := by
  rcases hr.eq_or_lt with rfl | hr
  · have heventually :
        ∀ᶠ epsilon : Real in nhdsWithin 0 (Ioi 0), epsilon < 1 :=
      (eventually_lt_nhds zero_lt_one).filter_mono inf_le_left
    have hconstant :
        Tendsto (fun _ : Real => (0 : Real))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_const_nhds
    simpa [logarithmicProfile] using hconstant.congr' (by
      filter_upwards [heventually] with epsilon hepsilon
      have hpower : (0 : Real) ^ (1 - epsilon) = 0 :=
        Real.zero_rpow (by linarith)
      simp [powerProfile, hpower])
  · have hidentity : HasDerivAt (fun epsilon : Real => epsilon) 1 0 :=
      hasDerivAt_id 0
    have hinner : HasDerivAt (fun epsilon : Real => 1 - epsilon) (-1) 0 :=
      hidentity.const_sub 1
    have hderiv :
        HasDerivAt
          (fun epsilon : Real => r ^ (1 - epsilon))
          (logarithmicProfile r) 0 := by
      have h := hinner.const_rpow hr
      convert h using 1
      simp [logarithmicProfile, Real.negMulLog]
      ring
    simpa [powerProfile, div_eq_inv_mul, mul_comm] using
      hderiv.tendsto_slope_zero_right
