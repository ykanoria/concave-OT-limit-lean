import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace ExcursionCoupling

open MeasureTheory Set Function

noncomputable def Fsigma (mu nu : Measure Real) (x : Real) : Real :=
  (mu (Iic x)).toReal - (nu (Iic x)).toReal

def completedGraph (F : Real -> Real) : Set (Real × Real) :=
  {p | p.2 ∈ uIcc (leftLim F p.1) (F p.1)}

def levelSet (F : Real -> Real) (h : Real) : Set Real :=
  {x | (x, h) ∈ completedGraph F}

def posPoints (F : Real -> Real) : Set (Real × Real) :=
  {p | p ∈ completedGraph F ∧ ∃ epsilon > 0, ∀ q ∈ completedGraph F,
    |q.1 - p.1| < epsilon -> q.1 ≠ p.1 ->
      0 < (q.2 - p.2) * (q.1 - p.1)}

def negPoints (F : Real -> Real) : Set (Real × Real) :=
  {p | p ∈ completedGraph F ∧ ∃ epsilon > 0, ∀ q ∈ completedGraph F,
    |q.1 - p.1| < epsilon -> q.1 ≠ p.1 ->
      (q.2 - p.2) * (q.1 - p.1) < 0}

def regularLevel (F : Real -> Real) (h : Real) : Prop :=
  ∃ n : Nat, ∃ x : Fin (2 * n) -> Real,
    StrictMono x ∧ levelSet F h = range x ∧
      (∀ i : Fin (2 * n), (x i, h) ∈ posPoints F ∪ negPoints F) ∧
      (∀ i : Fin (2 * n),
        ((x i, h) ∈ posPoints F ↔ (0 < h ↔ Even (i : Nat))))

def pairedRoutes (F : Real -> Real) : Set (Real × Real) :=
  {r | ∃ h : Real, h ≠ 0 ∧ regularLevel F h ∧
    (r.1, h) ∈ posPoints F ∧ (r.2, h) ∈ negPoints F ∧
    ((0 < h ∧ r.1 < r.2 ∧
        ∀ z ∈ Ioo r.1 r.2, z ∉ levelSet F h) ∨
      (h < 0 ∧ r.2 < r.1 ∧
        ∀ z ∈ Ioo r.2 r.1, z ∉ levelSet F h))}

def NonCrossing (S : Set (Real × Real)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    uIcc p.1 p.2 ∩ uIcc q.1 q.2 = ∅ ∨
      (∃ z : Real, uIcc p.1 p.2 ∩ uIcc q.1 q.2 = {z}) ∨
      uIcc p.1 p.2 ⊆ uIcc q.1 q.2 ∨
      uIcc q.1 q.2 ⊆ uIcc p.1 p.2

def NonConnecting (S : Set (Real × Real)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    0 < min |p.2 - p.1| |q.2 - q.1| -> p.2 ≠ q.1

def SameOrientation (S : Set (Real × Real)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    uIcc q.1 q.2 ⊆ Ioo (p.1 ⊓ p.2) (p.1 ⊔ p.2) ->
      0 <= (p.2 - p.1) * (q.2 - q.1)

def IsMonotoneArchSet (S : Set (Real × Real)) : Prop :=
  NonCrossing S ∧ NonConnecting S ∧ SameOrientation S

end ExcursionCoupling
