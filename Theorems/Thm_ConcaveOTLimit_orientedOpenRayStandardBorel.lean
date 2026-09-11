import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.LocallyClosed

open Set Topology

noncomputable section

namespace ConcaveOTLimit

private theorem polishSpace_subtype_of_isLocallyClosed
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {s : Set X} (hs : IsLocallyClosed s) : PolishSpace s := by
  obtain ⟨u, z, hu, hz, rfl⟩ := hs
  let t : Set z := {x | (x : X) ∈ u}
  have ht : IsOpen t := hu.preimage continuous_subtype_val
  letI : PolishSpace z := hz.polishSpace
  letI : PolishSpace t := ht.polishSpace
  let e : (u ∩ z : Set X) ≃ₜ t := {
    toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
    invFun x := ⟨x.1.1, x.2, x.1.2⟩
    left_inv x := by ext; rfl
    right_inv x := by ext; rfl
    continuous_toFun :=
      (continuous_subtype_val.subtype_mk fun x => x.2.2).subtype_mk
        fun x => x.2.1
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        fun x => ⟨x.2, x.1.2⟩
  }
  exact e.isClosedEmbedding.polishSpace

/-- The valid raw ray codes form a locally closed subset of the raw code
space. The frame equations are closed and the strict endpoint order is
open. -/
theorem isRayCode_isLocallyClosed (n : Nat) :
    IsLocallyClosed {p : RawRayCode n | IsRayCode p} := by
  have hnorm : IsClosed {p : RawRayCode n | ‖p.1.2‖ = 1} :=
    isClosed_eq
      (continuous_norm.comp (continuous_snd.comp continuous_fst))
      continuous_const
  have hinner :
      IsClosed {p : RawRayCode n | inner Real p.1.1 p.1.2 = 0} :=
    isClosed_eq (continuous_inner.comp continuous_fst) continuous_const
  have hbounds : IsOpen {p : RawRayCode n | p.2.1 < p.2.2} :=
    isOpen_lt (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)
  simpa only [IsRayCode, setOf_and] using
    hnorm.isLocallyClosed.inter
      (hinner.isLocallyClosed.inter hbounds.isLocallyClosed)

/-- The validity predicate for raw ray codes is Borel measurable. -/
theorem isRayCode_measurableSet (n : Nat) :
    MeasurableSet {p : RawRayCode n | IsRayCode p} := by
  obtain ⟨u, z, hu, hz, hcode⟩ := isRayCode_isLocallyClosed n
  rw [hcode]
  exact hu.measurableSet.inter hz.measurableSet

/-- The inherited topology on valid oriented open ray codes is Polish. -/
instance instPolishSpaceOrientedOpenRay (n : Nat) :
    PolishSpace (OrientedOpenRay n) :=
  polishSpace_subtype_of_isLocallyClosed (isRayCode_isLocallyClosed n)

/-- Valid oriented open ray codes, with their inherited Borel sigma algebra,
form a standard Borel space. -/
instance instStandardBorelSpaceOrientedOpenRay (n : Nat) :
    StandardBorelSpace (OrientedOpenRay n) :=
  (isRayCode_measurableSet n).standardBorel

/-- The inclusion of valid ray codes into raw ray codes is a measurable
embedding with Borel range. -/
theorem orientedOpenRay_measurableEmbedding (n : Nat) :
    MeasurableEmbedding
      ((↑) : OrientedOpenRay n -> RawRayCode n) :=
  MeasurableEmbedding.subtype_coe (isRayCode_measurableSet n)

namespace OrientedOpenRay

theorem continuous_anchor {n : Nat} :
    Continuous (anchor : OrientedOpenRay n -> Euclidean n) := by
  exact continuous_fst.comp (continuous_fst.comp continuous_subtype_val)

theorem measurable_anchor {n : Nat} :
    Measurable (anchor : OrientedOpenRay n -> Euclidean n) :=
  continuous_anchor.measurable

theorem continuous_direction {n : Nat} :
    Continuous (direction : OrientedOpenRay n -> Euclidean n) := by
  exact continuous_snd.comp (continuous_fst.comp continuous_subtype_val)

theorem measurable_direction {n : Nat} :
    Measurable (direction : OrientedOpenRay n -> Euclidean n) :=
  continuous_direction.measurable

theorem continuous_lower {n : Nat} :
    Continuous (lower : OrientedOpenRay n -> EReal) := by
  exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)

theorem measurable_lower {n : Nat} :
    Measurable (lower : OrientedOpenRay n -> EReal) :=
  continuous_lower.measurable

theorem continuous_upper {n : Nat} :
    Continuous (upper : OrientedOpenRay n -> EReal) := by
  exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)

theorem measurable_upper {n : Nat} :
    Measurable (upper : OrientedOpenRay n -> EReal) :=
  continuous_upper.measurable

/-- Evaluation along one fixed ray is continuous in its real coordinate. -/
theorem continuous_point {n : Nat} (R : OrientedOpenRay n) :
    Continuous R.point := by
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem measurable_point {n : Nat} (R : OrientedOpenRay n) :
    Measurable R.point :=
  (continuous_point R).measurable

/-- Evaluation at one fixed coordinate is continuous in the ray code. -/
theorem continuous_point_at {n : Nat} (t : Real) :
    Continuous fun R : OrientedOpenRay n => R.point t := by
  exact continuous_anchor.add (continuous_direction.const_smul t)

theorem measurable_point_at {n : Nat} (t : Real) :
    Measurable fun R : OrientedOpenRay n => R.point t :=
  (continuous_point_at t).measurable

/-- Joint ray-coordinate evaluation is continuous. -/
theorem continuous_point_uncurry {n : Nat} :
    Continuous fun p : OrientedOpenRay n × Real => p.1.point p.2 := by
  exact (continuous_anchor.comp continuous_fst).add
    (continuous_snd.smul (continuous_direction.comp continuous_fst))

theorem measurable_point_uncurry {n : Nat} :
    Measurable fun p : OrientedOpenRay n × Real => p.1.point p.2 :=
  continuous_point_uncurry.measurable

end OrientedOpenRay

/-- Ray coordinates vary continuously with the ambient point. -/
theorem continuous_rayCoordinate {n : Nat} (R : OrientedOpenRay n) :
    Continuous (rayCoordinate R) := by
  exact continuous_inner.comp
    ((continuous_id.sub continuous_const).prodMk continuous_const)

theorem measurable_rayCoordinate {n : Nat} (R : OrientedOpenRay n) :
    Measurable (rayCoordinate R) :=
  (continuous_rayCoordinate R).measurable

/-- Joint evaluation of the ray-coordinate map is continuous. -/
theorem continuous_rayCoordinate_uncurry {n : Nat} :
    Continuous fun p : OrientedOpenRay n × Euclidean n =>
      rayCoordinate p.1 p.2 := by
  exact continuous_inner.comp
    ((continuous_snd.sub
        (OrientedOpenRay.continuous_anchor.comp continuous_fst)).prodMk
      (OrientedOpenRay.continuous_direction.comp continuous_fst))

theorem measurable_rayCoordinate_uncurry {n : Nat} :
    Measurable fun p : OrientedOpenRay n × Euclidean n =>
      rayCoordinate p.1 p.2 :=
  continuous_rayCoordinate_uncurry.measurable

end ConcaveOTLimit
