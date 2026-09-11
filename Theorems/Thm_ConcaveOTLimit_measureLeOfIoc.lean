import Theorems.Thm_ConcaveOTLimit_signedCumulativeRightContinuousAndLeftLim

open MeasureTheory Set

namespace ConcaveOTLimit

noncomputable section

private theorem signedCumulative_swap_increment
    (mu nu : FiniteMeasure Real) {a b : Real} (hab : a ≤ b) :
    signedCumulative nu mu b - signedCumulative nu mu a =
      (nu : Measure Real).real (Ioc a b) -
        (mu : Measure Real).real (Ioc a b) := by
  have hMu :
      (mu : Measure Real).real (Iic b) =
        (mu : Measure Real).real (Iic a) +
          (mu : Measure Real).real (Ioc a b) := by
    rw [← Iic_union_Ioc_eq_Iic hab]
    exact measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
  have hNu :
      (nu : Measure Real).real (Iic b) =
        (nu : Measure Real).real (Iic a) +
          (nu : Measure Real).real (Ioc a b) := by
    rw [← Iic_union_Ioc_eq_Iic hab]
    exact measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
  simp only [signedCumulative, Measure.real_def] at hMu hNu ⊢
  linarith

private def iocRemainderCdf
    (mu nu : FiniteMeasure Real)
    (hIoc :
      ∀ ⦃a b : Real⦄, a < b →
        (mu : Measure Real) (Ioc a b) ≤
          (nu : Measure Real) (Ioc a b)) :
    StieltjesFunction Real where
  toFun := signedCumulative nu mu
  mono' := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    have hReal :
        (mu : Measure Real).real (Ioc a b) ≤
          (nu : Measure Real).real (Ioc a b) :=
      ENNReal.toReal_mono (measure_ne_top (nu : Measure Real) _)
        (hIoc hab)
    rw [← sub_nonneg,
      signedCumulative_swap_increment mu nu hab.le]
    exact sub_nonneg.mpr hReal
  right_continuous' x :=
    (signedCumulativeRightContinuousAndLeftLim nu mu).1 x

/-- Domination on all bounded open-closed intervals determines domination of
finite Borel measures on the real line. -/
theorem measure_le_of_Ioc
    (mu nu : Measure Real)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hIoc : ∀ ⦃a b : Real⦄, a < b → mu (Ioc a b) ≤ nu (Ioc a b)) :
    mu ≤ nu := by
  let muFinite : FiniteMeasure Real := ⟨mu, inferInstance⟩
  let nuFinite : FiniteMeasure Real := ⟨nu, inferInstance⟩
  let rho : Measure Real :=
    (iocRemainderCdf muFinite nuFinite hIoc).measure
  letI : IsFiniteMeasure rho := by
    dsimp only [rho]
    apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
      (C := nu.real univ + mu.real univ)
    intro x
    change |nu.real (Iic x) - mu.real (Iic x)| ≤
      nu.real univ + mu.real univ
    calc
      |nu.real (Iic x) - mu.real (Iic x)| ≤
          |nu.real (Iic x)| + |mu.real (Iic x)| :=
        abs_sub _ _
      _ = nu.real (Iic x) + mu.real (Iic x) := by
        rw [abs_of_nonneg measureReal_nonneg,
          abs_of_nonneg measureReal_nonneg]
      _ ≤ nu.real univ + mu.real univ :=
        add_le_add (measureReal_mono (subset_univ _))
          (measureReal_mono (subset_univ _))
  have hBalance : mu + rho = nu := by
    apply Measure.ext_of_Ioc
    intro a b hab
    have hIncrement :=
      signedCumulative_swap_increment muFinite nuFinite hab.le
    rw [Measure.add_apply]
    dsimp only [rho]
    rw [StieltjesFunction.measure_Ioc]
    change mu (Ioc a b) +
        ENNReal.ofReal
          (signedCumulative nuFinite muFinite b -
            signedCumulative nuFinite muFinite a) =
      nu (Ioc a b)
    rw [hIncrement, ENNReal.ofReal_sub _ measureReal_nonneg,
      ofReal_measureReal, ofReal_measureReal]
    exact add_tsub_cancel_of_le (hIoc hab)
  rw [← hBalance]
  exact Measure.le_add_right le_rfl

end

end ConcaveOTLimit
