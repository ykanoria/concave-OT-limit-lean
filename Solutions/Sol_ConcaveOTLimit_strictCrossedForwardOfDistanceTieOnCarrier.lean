import Theorems.Thm_ConcaveOTLimit_forwardPairsDistanceTwoCycleAndReroutingOfTie

open Set

open ConcaveOTLimit

theorem solution
    {A : Set Real} {x y x' y' : Real}
    (hxA : x ∈ A) (hyA : y ∈ Aᶜ)
    (hx'A : x' ∈ A) (hy'A : y' ∈ Aᶜ)
    (hxy : x < y) (hx'y' : x' < y')
    (hTie :
      dist x y + dist x' y' = dist x y' + dist x' y) :
    x < y' /\ x' < y := by
  have hCrossed :=
    (forwardPairsDistanceTwoCycleAndReroutingOfTie
      hxy.le hx'y'.le).2 hTie
  have hxy'Ne : x ≠ y' := by
    intro h
    exact hy'A (h ▸ hxA)
  have hx'yNe : x' ≠ y := by
    intro h
    exact hyA (h ▸ hx'A)
  exact
    ⟨lt_of_le_of_ne hCrossed.1 hxy'Ne,
      lt_of_le_of_ne hCrossed.2 hx'yNe⟩
