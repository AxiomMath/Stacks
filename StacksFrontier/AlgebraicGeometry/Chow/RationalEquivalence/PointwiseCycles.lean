module

public import StacksFrontier.AlgebraicGeometry.Chow.Cycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeZero
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksCore.Tactic.StacksAttribute

/-!
# Cycles as pointwise degree-zero Milnor K-chains

Let `(S, δ)` be the base situation of chapter 42 and `p : X ⟶ S` locally of finite type. A
`k`-cycle on `X` is a locally finitely supported integer-valued function on the points of `X`
which vanishes off the points of relative dimension `k`. Equivalently it is a locally finite
family of degree-zero Milnor K-classes, one at each point of relative dimension `k`: the
degree-zero Milnor K-group of a field is canonically `ℤ`, so the two descriptions differ only by
that identification. This is the identification of groups recorded in Stacks 0GU2, and the first
row of the presentation of the Chow group displayed in Stacks 0GU3.

## Main definitions

* `Stacks.Chow.pointsOfDimension` — the set of points of a prescribed relative dimension.
* `Stacks.Chow.PointwiseCycleGroup` — the locally finite direct sum of the degree-zero Milnor
  K-groups of the residue fields at those points.
* `Stacks.Chow.pointwiseCoeff` — the integer coefficient function of such a family.
* `Stacks.Chow.cycleToPointwise`, `Stacks.Chow.pointwiseToCycle` — the two comparison maps.

## Main results

* `Stacks.Chow.pointwiseCycleEquiv` — the identification of `Z_k(X)` with that direct sum
  (Stacks 0GU2).
* `Stacks.Chow.pointwiseCycleEquiv_apply` — its coordinates are the coefficients of the cycle.

## Implementation notes

The locally finite direct sum is `AlgebraicGeometry.locallyFiniteDirectSum`, whose finiteness
condition is phrased against quasi-compact opens; a cycle's support is locally finite in the
sense of `LocallyFiniteSupport`, and the passage between the two uses that the affine opens form
a basis and are quasi-compact. The inverse of the equivalence extends a pointwise family by zero
off the points of the given dimension, which is what makes the extended function land in
`Z_k(X)`.

## References

* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Topology

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)

/-- The points of `X` whose relative dimension over the base is `k`; equivalently, the generic
points of the integral closed subschemes of delta-dimension `k`. -/
def pointsOfDimension (k : ℤ) : Set X :=
  {x | relativeDimension C.dimensionFunction p x = k}

/-- A point lies in `pointsOfDimension` exactly when its relative dimension is `k`. -/
@[simp]
theorem mem_pointsOfDimension {k : ℤ} {x : X} :
    x ∈ pointsOfDimension C p k ↔ relativeDimension C.dimensionFunction p x = k :=
  Iff.rfl

/-- **Stacks 0GU2.** The group of locally finite families of degree-zero Milnor K-classes at the
points of relative dimension `k`: the pointwise description of the group of `k`-cycles. -/
abbrev PointwiseCycleGroup (k : ℤ) : Type u :=
  ↥(locallyFiniteDirectSum X (pointsOfDimension C p k)
    fun x ↦ MilnorKTheory (X.residueField x.1) 0)

/-- The integer coefficient function of a pointwise family: the Milnor K-class at a point of
relative dimension `k` read as an integer, and zero at every other point. -/
def pointwiseCoeff (k : ℤ) (a : PointwiseCycleGroup C p k) (x : X) : ℤ :=
  open Classical in
  if hx : x ∈ pointsOfDimension C p k then
    milnorKTheoryZeroAddEquiv (X.residueField x) (a.1 ⟨x, hx⟩)
  else 0

/-- At a point of relative dimension `k` the coefficient function of a pointwise family is the
integer underlying its Milnor K-class there. -/
theorem pointwiseCoeff_of_mem {k : ℤ} (a : PointwiseCycleGroup C p k) {x : X}
    (hx : x ∈ pointsOfDimension C p k) :
    pointwiseCoeff C p k a x = milnorKTheoryZeroAddEquiv (X.residueField x) (a.1 ⟨x, hx⟩) := by
  classical
  simp [pointwiseCoeff, hx]

/-- Off the points of relative dimension `k` the coefficient function of a pointwise family
vanishes. -/
theorem pointwiseCoeff_of_not_mem {k : ℤ} (a : PointwiseCycleGroup C p k) {x : X}
    (hx : x ∉ pointsOfDimension C p k) : pointwiseCoeff C p k a x = 0 := by
  classical
  simp [pointwiseCoeff, hx]

/-- The coefficient function of a pointwise family has locally finite support: every point has
an affine, hence quasi-compact, open neighbourhood, on which the family is finitely supported by
definition. -/
theorem locallyFiniteSupport_pointwiseCoeff (k : ℤ) (a : PointwiseCycleGroup C p k) :
    LocallyFiniteSupport (pointwiseCoeff C p k a) := by
  intro x
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨(U : Set X), U.2.mem_nhds hxU, ?_⟩
  refine ((a.2 U hUaff.isCompact).image fun y : pointsOfDimension C p k ↦ (y : X)).subset ?_
  rintro y ⟨hyU, hyne⟩
  have hdim : y ∈ pointsOfDimension C p k := by
    by_contra h
    exact hyne (pointwiseCoeff_of_not_mem C p a h)
  refine ⟨⟨y, hdim⟩, ⟨hyU, fun h ↦ hyne ?_⟩, rfl⟩
  rw [pointwiseCoeff_of_mem C p a hdim, h, map_zero]

variable [LocallyOfFiniteType p]

/-- A cycle of delta-dimension `k` has all its nonzero coefficients at points of relative
dimension `k`. -/
theorem mem_pointsOfDimension_of_apply_ne_zero {k : ℤ} (c : CycleGroup C p k) {x : X}
    (hx : c.1 x ≠ 0) : x ∈ pointsOfDimension C p k :=
  (mem_pointsOfDimension C p).mpr
    ((mem_cyclesOfDimension_iff_forall_point C p k c.1).mp c.2 x hx)

/-- On a quasi-compact open, only finitely many points of relative dimension `k` carry a nonzero
coefficient of a given `k`-cycle. -/
theorem finite_pointsOfDimension_inter_support (k : ℤ) (c : CycleGroup C p k) (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    {x : pointsOfDimension C p k | (x : X) ∈ (U : Set X) ∧
      (milnorKTheoryZeroAddEquiv (X.residueField x.1)).symm (c.1 x.1) ≠ 0}.Finite := by
  have hsupport : ((U : Set X) ∩ Function.support (c.1 : X → ℤ)).Finite :=
    c.1.locallyFiniteSupport.finite_inter_support_of_isCompact hU
  refine Set.Finite.of_finite_image (f := fun x : pointsOfDimension C p k ↦ (x : X))
    (hsupport.subset ?_) (Set.injOn_of_injective Subtype.val_injective)
  rintro y ⟨x, ⟨hxU, hxne⟩, rfl⟩
  exact ⟨hxU, fun h ↦ hxne (by simp [h])⟩

/-- The `k`-cycle attached to a locally finite pointwise family of Milnor K-classes. -/
def pointwiseToCycle (k : ℤ) : PointwiseCycleGroup C p k →+ CycleGroup C p k where
  toFun a :=
    ⟨⟨pointwiseCoeff C p k a, fun _ _ ↦ trivial,
        fun z _ ↦ locallyFiniteSupport_pointwiseCoeff C p k a z⟩,
      (mem_cyclesOfDimension_iff_forall_point C p k _).mpr fun x hx ↦ by
        by_contra hdim
        exact hx (pointwiseCoeff_of_not_mem C p a hdim)⟩
  map_zero' := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change pointwiseCoeff C p k 0 x = 0
    by_cases hx : x ∈ pointsOfDimension C p k
    · rw [pointwiseCoeff_of_mem C p 0 hx]
      simp
    · rw [pointwiseCoeff_of_not_mem C p 0 hx]
  map_add' a b := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change pointwiseCoeff C p k (a + b) x =
      pointwiseCoeff C p k a x + pointwiseCoeff C p k b x
    by_cases hx : x ∈ pointsOfDimension C p k
    · rw [pointwiseCoeff_of_mem C p (a + b) hx, pointwiseCoeff_of_mem C p a hx,
        pointwiseCoeff_of_mem C p b hx]
      change milnorKTheoryZeroAddEquiv _ (a.1 ⟨x, hx⟩ + b.1 ⟨x, hx⟩) = _
      simp
    · rw [pointwiseCoeff_of_not_mem C p (a + b) hx, pointwiseCoeff_of_not_mem C p a hx,
        pointwiseCoeff_of_not_mem C p b hx, add_zero]

/-- The pointwise family of Milnor K-classes attached to a `k`-cycle. -/
def cycleToPointwise (k : ℤ) : CycleGroup C p k →+ PointwiseCycleGroup C p k where
  toFun c :=
    ⟨fun x ↦ (milnorKTheoryZeroAddEquiv (X.residueField x.1)).symm (c.1 x.1),
      fun U hU ↦ finite_pointsOfDimension_inter_support C p k c U hU⟩
  map_zero' := Subtype.ext (funext fun x ↦ by simp)
  map_add' a b := Subtype.ext (funext fun x ↦ by simp)

/-- The coordinates of the pointwise family attached to a cycle. -/
@[simp]
theorem cycleToPointwise_apply (k : ℤ) (c : CycleGroup C p k) (x : pointsOfDimension C p k) :
    (cycleToPointwise C p k c).1 x =
      (milnorKTheoryZeroAddEquiv (X.residueField x.1)).symm (c.1 x.1) :=
  rfl

/-- **Stacks 0GU2.** The group of `k`-cycles is the locally finite direct sum of the degree-zero
Milnor K-groups of the residue fields at the points of relative dimension `k`. -/
@[stacks 0GU2 "the pointwise description of cycles"]
def pointwiseCycleEquiv (k : ℤ) : CycleGroup C p k ≃+ PointwiseCycleGroup C p k where
  toFun := cycleToPointwise C p k
  invFun := pointwiseToCycle C p k
  left_inv c := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change pointwiseCoeff C p k (cycleToPointwise C p k c) x = c.1 x
    by_cases hx : x ∈ pointsOfDimension C p k
    · rw [pointwiseCoeff_of_mem C p (cycleToPointwise C p k c) hx]
      simp
    · rw [pointwiseCoeff_of_not_mem C p (cycleToPointwise C p k c) hx]
      by_contra h
      exact hx (mem_pointsOfDimension_of_apply_ne_zero C p c (Ne.symm h))
  right_inv a := by
    refine Subtype.ext (funext fun x ↦ ?_)
    change (milnorKTheoryZeroAddEquiv (X.residueField x.1)).symm
      (pointwiseCoeff C p k a x.1) = a.1 x
    rw [pointwiseCoeff_of_mem C p a x.2]
    simp
  map_add' := (cycleToPointwise C p k).map_add

/-- **Stacks 0GU2.** Under the pointwise description of cycles, the degree-zero Milnor K-class at
a point of relative dimension `k` is the coefficient of the cycle there. -/
@[stacks 0GU2 "the coordinate identification with integer coefficients"]
theorem pointwiseCycleEquiv_apply (k : ℤ) (c : CycleGroup C p k)
    (x : pointsOfDimension C p k) :
    milnorKTheoryZeroAddEquiv (X.residueField x.1) ((pointwiseCycleEquiv C p k c).1 x) =
      c.1 x.1 := by
  simp [pointwiseCycleEquiv]

/-- The cycle underlying a pointwise family is given by its coefficient function. -/
@[simp]
theorem pointwiseCycleEquiv_symm_apply (k : ℤ) (a : PointwiseCycleGroup C p k) (x : X) :
    ((pointwiseCycleEquiv C p k).symm a).1 x = pointwiseCoeff C p k a x :=
  rfl

end Stacks.Chow

end
