module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The degree of a Picard class on a proper curve

Let `X` be proper of dimension at most one over a field `k`. The degree
`AlgebraicGeometry.invertibleCurveDegree` of an invertible `𝒪_X`-module is an invariant of its
isomorphism class and is additive in the tensor product, so it descends to a homomorphism of
abelian groups `Pic(X) ⟶ ℤ` on the Picard group of `X`.

## Main definitions

* `AlgebraicGeometry.invertibleCurveDegreeOfClass` — the degree of the chosen representative of
  a Picard class.
* `AlgebraicGeometry.invertibleCurveDegreeHom` — the degree as a homomorphism `Pic(X) ⟶ ℤ`.

## Main results

* `AlgebraicGeometry.invertibleCurveDegreeHom_picardClass` — its value on the class of `ℒ` is
  `deg(ℒ)`, for *any* representative `ℒ` and not only the chosen one.
* `AlgebraicGeometry.invertibleCurveDegreeHom_eq_zero_of_eq_zero` — a trivial class has degree
  zero.

## Implementation notes

The Picard group is `Stacks.Picard.ofScheme X`, the spelling the relative Picard functor
`Stacks.PicardFunctor.picardFunctor` is built from, and not the defeq
`AlgebraicGeometry.Scheme.picardGroup`. The two differ only in which proof of the sheaf condition
of the `RingCat`-valued structure sheaf they carry; `Stacks.Picard.ofScheme` is the one whose
pullback homomorphism `Stacks.Picard.schemePullbackClassHom` is available, which is what a
relative statement has to compose with.

The construction is the same one that
`Stacks.Models.RegularProperModelSituation.specialFiberComponentDegreeHom` performs for the
degree on a component of the special fibre of a regular proper model: evaluate the degree on the
representative chosen by `Stacks.Picard.picardRepresentative`, then show the value does not
depend on the choice and is additive. Both inputs are unconditional here:

* isomorphism invariance is `AlgebraicGeometry.invertibleCurveDegree_eq_of_iso`;
* additivity is `AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add`, the invertible case
  of [Stacks, Tag 0AYX], which carries no hypothesis beyond properness and the dimension bound.

No tag is attached. [Stacks, Tag 0AYX] is already registered on the additivity statement this
file consumes, and this file only repackages it as a homomorphism; [Stacks, Tag 01CX] is the
definition of the Picard group, already registered where that group is defined.

**The two spellings of the tensor product.** `picardClass_tensorSheaf` states addition of Picard
classes with `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, while
`invertibleCurveDegree_tensorSheaf_eq_add` states additivity of the degree with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`. These are the same term — the
implementation notes of `StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Cohomological.lean`
record this — so the two combine with no transport.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- The degree on `X` of the chosen representative of a Picard class. -/
def invertibleCurveDegreeOfClass (x : Stacks.Picard.ofScheme X) : ℤ :=
  @invertibleCurveDegree k _ X f _ hdim
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).obj
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).property

/-- The degree of the representative of the class of `ℒ` is the degree of `ℒ`: the two modules
are isomorphic, and the degree is an isomorphism invariant. -/
theorem invertibleCurveDegreeOfClass_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    invertibleCurveDegreeOfClass k f hdim
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL) =
      @invertibleCurveDegree k _ X f _ hdim L hL := by
  have e := ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace
      (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
        L hL))).some
  exact @invertibleCurveDegree_eq_of_iso k _ X f _ hdim _ _
    (Stacks.Picard.picardRepresentative X.toRingedSpace _).property hL e

/-- **The degree of a Picard class on a proper curve, as a homomorphism `Pic(X) ⟶ ℤ`**,
`[ℒ] ↦ deg(ℒ)`. It is well defined because the degree is an isomorphism invariant, and additive
because the degree is additive in the tensor product, the invertible case of [Stacks, Tag
0AYX]. -/
def invertibleCurveDegreeHom : Stacks.Picard.ofScheme X →+ ℤ :=
  AddMonoidHom.mk' (invertibleCurveDegreeOfClass k f hdim) fun x y => by
    set Lx := Stacks.Picard.picardRepresentative X.toRingedSpace x with hLxdef
    set Ly := Stacks.Picard.picardRepresentative X.toRingedSpace y with hLydef
    have hLxy := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _
      Lx.property Ly.property
    have hsum : x + y = Stacks.SheafOfModules.picardClass X.presheaf
        (structureIsSheaf X.toRingedSpace) _ hLxy := by
      conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x,
        ← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace y]
      exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ _ _ hLxy
    rw [hsum]
    refine (invertibleCurveDegreeOfClass_picardClass k f hdim _ hLxy).trans ?_
    exact @invertibleCurveDegree_tensorSheaf_eq_add k _ X f _ hdim Lx.obj Ly.obj
      Lx.property Ly.property hLxy

/-- The degree homomorphism on the class of `ℒ` is `deg(ℒ)`. -/
@[simp] theorem invertibleCurveDegreeHom_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    invertibleCurveDegreeHom k f hdim
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL) =
      @invertibleCurveDegree k _ X f _ hdim L hL :=
  invertibleCurveDegreeOfClass_picardClass k f hdim L hL

/-- The degree homomorphism agrees with the degree of the chosen representative. -/
theorem invertibleCurveDegreeHom_apply (x : Stacks.Picard.ofScheme X) :
    invertibleCurveDegreeHom k f hdim x = invertibleCurveDegreeOfClass k f hdim x := rfl

/-- The trivial Picard class has degree zero. -/
@[simp] theorem invertibleCurveDegreeHom_zero :
    invertibleCurveDegreeHom k f hdim 0 = 0 :=
  map_zero _

/-- The degree of a sum of Picard classes is the sum of the degrees: the degree is a
homomorphism. -/
theorem invertibleCurveDegreeHom_add (x y : Stacks.Picard.ofScheme X) :
    invertibleCurveDegreeHom k f hdim (x + y) =
      invertibleCurveDegreeHom k f hdim x + invertibleCurveDegreeHom k f hdim y :=
  map_add _ x y

/-- The degree of the negative of a Picard class is the negative of its degree: the inverse of
an invertible module has the opposite degree. -/
theorem invertibleCurveDegreeHom_neg (x : Stacks.Picard.ofScheme X) :
    invertibleCurveDegreeHom k f hdim (-x) = -invertibleCurveDegreeHom k f hdim x :=
  map_neg _ x

end AlgebraicGeometry

end
