module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicard
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom

/-!
# Pullback of a divisor class along a nonconstant morphism of curves multiplies degree

Let `k` be a field and let `π : X ⟶ Y` be a nonconstant morphism of proper curves over `k`.  The
degree of the pullback of an invertible module is `deg(π)·deg(L)`, where `deg(π) = [R(X) : R(Y)]`
is the degree of the extension of function fields ([Stacks, Tag 0AYZ]).  Degree and pullback both
descend to the Picard group, so the same formula holds for Picard classes; and when `k` is
algebraically closed and the two curves are smooth, the divisor class group of a curve is its
Picard group, so the formula holds for divisor classes with `curveClassGroupDegree` as the degree.

## Main definitions

* `Stacks.EtaleCohomology.curveClassGroupPullback`: the pullback of divisor classes along a
  morphism of smooth curves over an algebraically closed field, read through the identification of
  the divisor class group with the Picard group.

## Main results

* `AlgebraicGeometry.picardDegree_picardModelAddEquiv`: the two degree homomorphisms on the two
  models of the Picard group agree.
* `AlgebraicGeometry.invertibleCurveDegreeHom_schemePullbackClass_eq_degreeOver_mul` and
  `AlgebraicGeometry.picardDegree_schemePicardPullbackHom_eq_degreeOver_mul`: pullback of Picard
  classes along a nonconstant morphism of proper curves multiplies degree by `deg(π)`, in each of
  the two models.
* `Stacks.EtaleCohomology.curveClassGroupDegree_curveClassGroupPullback`: pullback of divisor
  classes multiplies `curveClassGroupDegree` by `deg(π)`.

## Implementation notes

The Picard group of a scheme comes in two spellings.  `Stacks.Picard.ofScheme X` is the one
carrying the pullback homomorphism `Stacks.Picard.schemePullbackClassHom`, and
`AlgebraicGeometry.schemePicard X` is the one carrying the degree
`AlgebraicGeometry.picardDegree` and the identification with the divisor class group
`Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard`.  They are matched by
`Stacks.GluePicard.picardModelAddEquiv`, and `AlgebraicGeometry.schemePicardPullbackHom`
transports the pullback across that match.  Both degrees are evaluated on a representative
invertible module, so `AlgebraicGeometry.picardDegree_picardModelAddEquiv` identifies them, and
the whole formula reduces to the rank-one case of [Stacks, Tag 0AYZ],
`AlgebraicGeometry.invertibleCurveDegree_pullback_eq_degreeOver_mul`.

Nonconstancy of `π` enters only through that tag; it is what makes the extension of function
fields finite, so that `AlgebraicGeometry.degreeOver` is defined.

Properness and the dimension bound are carried separately rather than through a notion of
projective curve, because that is the shape in which `AlgebraicGeometry.picardDegree` and
`AlgebraicGeometry.invertibleCurveDegree` consume them.

No tag is attached.  [Stacks, Tag 0AYZ] is already registered on the module-level degree formula
that this file consumes, and [Stacks, Tag 0BE9] on the identification of the divisor class group
with the Picard group; this file only transports the first along the second.

`Stacks.EtaleCohomology.curveClassGroupPullback` is built from the pullback of Picard classes and
is not compared here with restriction on first étale cohomology,
`Stacks.EtaleCohomology.multiplicativeRestriction π 1`.  Such a comparison asks for a morphism
of divisor sequences along `π`, and of its three components only the first two are available for
a general `π` (`Stacks.EtaleCohomology.multiplicativeDirectImageSquareMap` and
`Stacks.EtaleCohomology.genericPointMap`).  The third, on `⨁_x i_{x,*} 𝐙`, exists only as
`Stacks.EtaleCohomology.closedPointDivisorDirectImageMap`, which takes a choice of one point
over each closed point with coefficient one; for a ramified morphism of curves the correct
component weights the points over `x` by their ramification indices, and the order-of-vanishing
input for that, a form of
`Stacks.EtaleCohomology.ord_dominantFunctionFieldMap_of_flat` without its hypothesis that the
maximal ideal maps onto the maximal ideal, is not in the library.

## References

* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ): the degree of a pullback
  of a finite locally free module along a nonconstant morphism of proper curves.
* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9): the divisor class group
  of a smooth curve is its Picard group.
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX): the Picard group.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-! ### The two degree homomorphisms on the two models of the Picard group -/

section Models

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1)

/-- **The two degree homomorphisms on the Picard group of a proper curve agree.**  Both are
evaluated on a representative invertible module: `AlgebraicGeometry.picardDegree` on
`AlgebraicGeometry.schemePicard`, and `AlgebraicGeometry.invertibleCurveDegreeHom` on
`Stacks.Picard.ofScheme`, the model carrying the pullback homomorphism. -/
theorem picardDegree_picardModelAddEquiv (y : Stacks.Picard.ofScheme X) :
    picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace y) =
      invertibleCurveDegreeHom k f hdim y := by
  have h : Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace y =
      Stacks.SheafOfModules.Picard.classOf X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)
        (Stacks.Picard.picardRepresentative X.toRingedSpace y).obj
        (Stacks.Picard.picardRepresentative X.toRingedSpace y).property := by
    rw [← Stacks.GluePicard.picardModelAddEquiv_classOf]
    exact congrArg _ (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace y).symm
  rw [h]
  exact picardDegree_classOf k f hdim _ _

end Models

/-! ### The degree of the pullback of a Picard class -/

section Pullback

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of k))
  (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY] [IsProper πX] [IsProper πY]
  (π : X ⟶ Y) (hπ : π ≫ πY = πX) (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y)

/-- **The degree of the pullback of a Picard class along a nonconstant morphism of proper
curves** is `deg(π)` times the degree of that class, in the model `Stacks.Picard.ofScheme`
carrying the pullback homomorphism.  This is the rank-one case of [Stacks, Tag 0AYZ] read on
Picard classes: the representative of the pulled-back class is isomorphic to the pullback of the
representative, and the degree of an invertible module is an isomorphism invariant. -/
theorem invertibleCurveDegreeHom_schemePullbackClass_eq_degreeOver_mul
    (y : Stacks.Picard.ofScheme Y) :
    invertibleCurveDegreeHom k πX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX)))
        (Stacks.Picard.schemePullbackClass π y) =
      (@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY π hπ)
          (isDominant_of_not_constant k πX πY π hnc) : ℤ) *
        invertibleCurveDegreeHom k πY
          (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πY))) y := by
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso π y
  rw [invertibleCurveDegreeHom_apply, invertibleCurveDegreeHom_apply,
    invertibleCurveDegreeOfClass, invertibleCurveDegreeOfClass,
    invertibleCurveDegree_eq_of_iso k πX _ e]
  exact invertibleCurveDegree_pullback_eq_degreeOver_mul k πX πY π hπ hnc _

/-- **The degree of the pullback of a Picard class along a nonconstant morphism of proper
curves**, in the model `AlgebraicGeometry.schemePicard` carrying the degree homomorphism. -/
theorem picardDegree_schemePicardPullbackHom_eq_degreeOver_mul (c : schemePicard Y) :
    picardDegree k πX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX)))
        (schemePicardPullbackHom π c) =
      (@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY π hπ)
          (isDominant_of_not_constant k πX πY π hnc) : ℤ) *
        picardDegree k πY (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πY))) c := by
  obtain ⟨y, rfl⟩ : ∃ y, Stacks.GluePicard.picardModelAddEquiv Y.toRingedSpace y = c :=
    ⟨(Stacks.GluePicard.picardModelAddEquiv Y.toRingedSpace).symm c,
      (Stacks.GluePicard.picardModelAddEquiv Y.toRingedSpace).apply_symm_apply c⟩
  rw [schemePicardPullbackHom_picardModelAddEquiv, picardDegree_picardModelAddEquiv,
    picardDegree_picardModelAddEquiv]
  exact invertibleCurveDegreeHom_schemePullbackClass_eq_degreeOver_mul k πX πY π hπ hnc y

end Pullback

end AlgebraicGeometry

/-! ### The degree of the pullback of a divisor class -/

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) [IsCurve k gX] [IsCurve k gY] [Smooth gX] [Smooth gY]

/-- **Pullback of divisor classes along a morphism of smooth curves over an algebraically closed
field**, read through the identification `Cl(-) ≅ Pic(-)` of
`Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard` and the pullback of Picard classes
`AlgebraicGeometry.schemePicardPullbackHom`. -/
def curveClassGroupPullback (π : X ⟶ Y) : curveClassGroup gY →+ curveClassGroup gX :=
  ((curveClassGroupAddEquivSchemePicard gX).symm.toAddMonoidHom.comp
      (schemePicardPullbackHom π)).comp
    (curveClassGroupAddEquivSchemePicard gY).toAddMonoidHom

/-- Under the identification `Cl(-) ≅ Pic(-)`, the pullback of a divisor class along `π`
corresponds to the pullback of its Picard class. -/
@[simp]
theorem curveClassGroupAddEquivSchemePicard_curveClassGroupPullback (π : X ⟶ Y)
    (c : curveClassGroup gY) :
    curveClassGroupAddEquivSchemePicard gX (curveClassGroupPullback gX gY π c) =
      schemePicardPullbackHom π (curveClassGroupAddEquivSchemePicard gY c) :=
  (curveClassGroupAddEquivSchemePicard gX).apply_symm_apply _

/-- **The degree of the pullback of a divisor class along a nonconstant morphism of smooth proper
curves over an algebraically closed field** is `deg(π)` times the degree of that class, where
`deg(π) = [R(X) : R(Y)]` is the degree of the extension of function fields.  This is the
rank-one case of [Stacks, Tag 0AYZ] read on divisor classes, the degree being
`Stacks.EtaleCohomology.curveClassGroupDegree`. -/
theorem curveClassGroupDegree_curveClassGroupPullback [IsProper gX] [IsProper gY] (π : X ⟶ Y)
    (hπ : π ≫ gY = gX) (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y) (c : curveClassGroup gY) :
    curveClassGroupDegree gX (curveClassGroupPullback gX gY π c) =
      (@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k gX gY π hπ)
          (isDominant_of_not_constant k gX gY π hnc) : ℤ) * curveClassGroupDegree gY c := by
  rw [← picardDegree_curveClassGroupAddEquivSchemePicard gX
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := gX))),
    ← picardDegree_curveClassGroupAddEquivSchemePicard gY
      (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := gY))),
    curveClassGroupAddEquivSchemePicard_curveClassGroupPullback]
  exact picardDegree_schemePicardPullbackHom_eq_degreeOver_mul k gX gY π hπ hnc _

end Stacks.EtaleCohomology

end
