import Theorems.Thm_ConcaveOTLimit_signedCumulativeLeLeftOfAtomlessAt

open Filter MeasureTheory Set Topology

open ConcaveOTLimit

theorem solution
    (mu nu : FiniteMeasure Real) (x h : Real)
    (hAtomlessAt : (mu : Measure Real) {x} = 0)
    (hCrossing : IsGoodIncreasingCrossing mu nu x h) :
    h = signedCumulative mu nu x := by
  rcases hCrossing with
    ⟨hGraph, epsilon, hEpsilon, hIncreasing⟩
  have hCumulativeLeLeft :
      signedCumulative mu nu x <= signedCumulativeLeft mu nu x :=
    signedCumulativeLeLeftOfAtomlessAt mu nu x hAtomlessAt
  have hCumulativeLeLevel : signedCumulative mu nu x <= h := by
    change
      h ∈
        uIcc (signedCumulativeLeft mu nu x)
          (signedCumulative mu nu x)
      at hGraph
    rw [uIcc_comm, uIcc_of_le hCumulativeLeLeft] at hGraph
    exact hGraph.1
  let y : Nat -> Real :=
    fun n => x + epsilon / ((n : Real) + 1)
  have hyAntitone : Antitone y := by
    intro n m hnm
    dsimp [y]
    have hn : 0 < (n : Real) + 1 := by positivity
    have hnmReal : (n : Real) + 1 <= (m : Real) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    gcongr
  have hyTendsto : Tendsto y atTop (nhds x) := by
    have hInv :
        Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
          atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [y, div_eq_mul_inv] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hInv)
  have hInter : (⋂ n, Iic (y n)) = Iic x := by
    ext z
    simp only [mem_iInter, mem_Iic]
    constructor
    · intro hz
      exact ge_of_tendsto hyTendsto (Eventually.of_forall hz)
    · intro hz n
      apply hz.trans
      dsimp [y]
      have hDen : 0 <= (n : Real) + 1 := by positivity
      exact le_add_of_nonneg_right (div_nonneg hEpsilon.le hDen)
  have hMuENNReal :
      Tendsto
        (fun n => (mu : Measure Real) (Iic (y n)))
        atTop (nhds ((mu : Measure Real) (Iic x))) := by
    have h :=
      tendsto_measure_iInter_atTop
        (μ := (mu : Measure Real))
        (fun _ => measurableSet_Iic.nullMeasurableSet)
        hyAntitone.Iic
        ⟨0, measure_ne_top (mu : Measure Real) (Iic (y 0))⟩
    simpa only [Function.comp_apply, hInter] using h
  have hNuENNReal :
      Tendsto
        (fun n => (nu : Measure Real) (Iic (y n)))
        atTop (nhds ((nu : Measure Real) (Iic x))) := by
    have h :=
      tendsto_measure_iInter_atTop
        (μ := (nu : Measure Real))
        (fun _ => measurableSet_Iic.nullMeasurableSet)
        hyAntitone.Iic
        ⟨0, measure_ne_top (nu : Measure Real) (Iic (y 0))⟩
    simpa only [Function.comp_apply, hInter] using h
  have hMuReal :
      Tendsto
        (fun n => ((mu : Measure Real) (Iic (y n))).toReal)
        atTop (nhds (((mu : Measure Real) (Iic x)).toReal)) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (mu : Measure Real) (Iic x))).comp hMuENNReal
  have hNuReal :
      Tendsto
        (fun n => ((nu : Measure Real) (Iic (y n))).toReal)
        atTop (nhds (((nu : Measure Real) (Iic x)).toReal)) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (nu : Measure Real) (Iic x))).comp hNuENNReal
  have hSignedTendsto :
      Tendsto (fun n => signedCumulative mu nu (y n))
        atTop (nhds (signedCumulative mu nu x)) := by
    simpa only [signedCumulative] using hMuReal.sub hNuReal
  have hLevelLeEventually :
      ∀ᶠ n in atTop, h <= signedCumulative mu nu (y n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hDen : 0 < (n : Real) + 1 := by positivity
    have hOneLtDen : (1 : Real) < (n : Real) + 1 := by
      exact_mod_cast Nat.lt_add_one_of_le hn
    have hStepPos : 0 < epsilon / ((n : Real) + 1) :=
      div_pos hEpsilon hDen
    have hStepLt : epsilon / ((n : Real) + 1) < epsilon := by
      rw [div_lt_iff₀ hDen]
      nlinarith
    have hyMem : y n ∈ Ioo (x - epsilon) (x + epsilon) := by
      dsimp [y]
      constructor <;> nlinarith
    have hyNe : y n ≠ x := by
      dsimp [y]
      nlinarith
    have hyGraph :
        (y n, signedCumulative mu nu (y n)) ∈
          generalizedCumulativeGraph mu nu := by
      change
        signedCumulative mu nu (y n) ∈
          uIcc (signedCumulativeLeft mu nu (y n))
            (signedCumulative mu nu (y n))
      exact right_mem_uIcc
    have hProduct := hIncreasing hyMem hyNe hyGraph
    rcases mul_pos_iff.mp hProduct with hPositive | hNegative
    · exact sub_nonneg.mp hPositive.1.le
    · have hyDiffPos : 0 < y n - x := by
        dsimp [y]
        nlinarith
      nlinarith [hNegative.2]
  have hLevelLeCumulative : h <= signedCumulative mu nu x :=
    ge_of_tendsto hSignedTendsto hLevelLeEventually
  exact le_antisymm hLevelLeCumulative hCumulativeLeLevel
